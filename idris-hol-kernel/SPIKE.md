# Phase 0 interop spike — findings

> **Superseded in part.** `scripts/libify.py`, described below, no longer
> exists. The generated file is not post-processed at all now: the same
> three edits, plus a `vector` → `vector-immutable` rewrite, are done at
> expansion time on the s-expressions Racket's reader produces, by
> `rhombus-hol/rhombus/hol/tests/idris_kernel.rkt`. The findings about the
> codegen's *shape* and about interop being essentially free still hold —
> they are what that module's assumptions are built on.


Question: can a function compiled by `idris2 --cg racket` be called from an
ordinary Racket module via `require`, at an acceptable per-call cost?

**Answer: yes, and the interop is essentially free.**

## Why

`idris2 --cg racket` does not emit a Racket *library* module — it emits a
`#lang racket/base` file whose entire body is one big `(let () <every
top-level definition> (void (PrimIO-unsafePerformIO Main-main))
(collect-garbage))`. `require`ing that file as-is sees an empty module: every
name is scoped inside the anonymous `let`, and the file's only externally
visible effect is running `Main-main` as a side effect of loading it.

That shape is easy to fix mechanically: unwrap the `(let () ...)` so its
contents become top-level module definitions, add
`(provide (all-defined-out))`, and drop the line that forces `Main-main`.
`scripts/libify.py` does exactly this and nothing else — no renaming, no
reformatting, so a future codegen output with the same shape needs no
changes. The result is a plain `#lang racket/base` module whose Idris-level
names (`Kernel-reflR`, `Term-mkVar`, `HType-boolTy`, ...) are ordinary Racket
top-level bindings, directly `require`-able and callable.

Crucially, there is **no marshalling boundary in the usual sense**: Idris2's
Racket backend already represents every value as a plain Racket value (ADT
constructors as tagged vectors, `Either`/`Maybe` the same way, strings as
Racket strings, `Nat` as Racket integers). Since both sides run in the same
Racket process, calling `Kernel-reflR` from hand-written Racket is a normal
function call on those vectors — not a serialize/deserialize step, not a
subprocess round-trip. The only real work at the boundary is encoding
Rhombus's `Term`/`HType` *class instances* into the matching tagged-vector
shape (and decoding results back) — a recursive walk proportional to term
size, which is inherent to the problem, not overhead the interop adds.

## How to reproduce

```sh
cd idris-hol-kernel
idris2 --cg racket --build kernel.ipkg
python3 scripts/libify.py build/exec/kernel_app/kernel.rkt /tmp/kernel-lib.rkt
export LD_LIBRARY_PATH="$PWD/build/exec/kernel_app:$LD_LIBRARY_PATH"
racket -e '(require (file "/tmp/kernel-lib.rkt"))
           (displayln (Kernel-reflR (car (Kernel-initialTheory 0))
                                     (Term-mkVar "x" HType-boolTy)))'
```

`LD_LIBRARY_PATH` must include `build/exec/kernel_app` so the FFI-loaded
`libidris2_support.so` resolves — the generated executable's shell wrapper
sets this for you; a library caller has to do it itself (e.g. Racket's
`(putenv ...)` before `require`, or bundling the `.so` where the OS loader
already looks).

## Benchmark

200,000 calls to `Kernel-reflR` on a trivial term (`REFL x` where `x : bool`
in the initial theory), in-process, after warmup:

| | time/call |
|---|---|
| `Kernel-reflR` (idris2-generated, via `require`) | **~0.15 µs** |
| hand-written native-Racket function of the same shape (stubbed type check) | ~0.0006 µs |

The idris2-generated version is ~250x slower than a deliberately-trivial
native stand-in, but the absolute cost (150 nanoseconds) is negligible next
to anything Rhombus itself does per kernel call (class allocation, `match`
dispatch, `raco`-compiled Rhombus is not free either). This is well within
the range where the hot paths identified in the exploration (`conv.rhm`'s
`SUB_CONV`/`DEPTH_CONV`, `ruledb.rhm`'s `simp_conv`/`db_conv`) would not be
meaningfully slowed by the call mechanism itself — the real cost driver, if
any, will be the Rhombus Term/HType ⇄ Idris tagged-vector codec (Phase 1),
which is proportional to term size regardless of which kernel implementation
runs it. That codec needs its own benchmark once written; this spike only
clears the "is the calling convention itself viable" gate.

## Go/no-go: **go**

The interop mechanism is proven, cheap, and mechanical (one small,
well-isolated postprocessing script, `scripts/libify.py`, checked into this
directory). Phase 1 (the Term/HType codec + wiring into `kernel.rhm`) is
unblocked.

## Caveats to carry into Phase 1

- `scripts/libify.py` depends on the exact shape idris2 0.8.0 emits (a
  literal `(let () ...)` wrapper, a literal trailing
  `(void (PrimIO-unsafePerformIO Main-main))` / `(collect-garbage)` pair).
  It asserts on both and fails loudly if either is missing, so an idris2
  upgrade that changes codegen shape will be caught at build time, not
  silently miscompiled.
- The library still needs a `main`/`executable` in `kernel.ipkg` to get
  `idris2 --build` to run codegen at all (Idris2 has no library-only
  Racket codegen mode) — `Main.idr`'s smoke test stays for that reason, but
  its output is now dead code from the library's point of view (stripped by
  `libify.py`), not a shipped side effect.
- `LD_LIBRARY_PATH` handling needs a real answer before this is wired into
  `raco make` (which does not know to set it) — likely `(putenv
  "LD_LIBRARY_PATH" ...)` computed relative to the generated module's own
  path, done once when `kernel.rhm` requires the generated file, rather than
  relying on the caller's shell environment.

# Phase 0 interop spike

Question: can a function compiled by `idris2 --cg racket` be called from an
ordinary Racket module via `require`, at an acceptable per-call cost?

**Answer: yes, the interop is essentially free** — but the runtime
integration this unblocked was later built, measured, and reverted; see the
main `README.md` for why. This spike's technical findings (codegen shape,
interop cost) still hold and are recorded here for reference.

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
The result is a plain `#lang racket/base` module whose Idris-level names
(`Kernel-reflR`, `Term-mkVar`, `HType-boolTy`, ...) are ordinary Racket
top-level bindings, directly `require`-able and callable.

Crucially, there is **no marshalling boundary in the usual sense**: Idris2's
Racket backend already represents every value as a plain Racket value (ADT
constructors as tagged vectors, `Either`/`Maybe` the same way, strings as
Racket strings, `Nat` as Racket integers). Since both sides run in the same
Racket process, calling `Kernel-reflR` from hand-written Racket is a normal
function call on those vectors — not a serialize/deserialize step, not a
subprocess round-trip. The only real work at the boundary is encoding
Rhombus's `Term`/`HType` class instances into the matching tagged-vector
shape (and decoding results back), proportional to term size.

## Benchmark

200,000 calls to `Kernel-reflR` on a trivial term (`REFL x` where `x : bool`
in the initial theory), in-process, after warmup, measured **~0.15 µs per
call** — about 250x slower than a deliberately-trivial native-Racket stand-in
of the same shape, but negligible in absolute terms (150 nanoseconds) next
to anything Rhombus itself does per kernel call. The calling convention
itself was not the bottleneck; the codec built in the phase that followed
was (see the main README's account of the runtime integration and its
reversion).

## Note on reproducing

The original postprocessing script this spike used (`scripts/libify.py`) no
longer exists: the same transform is now done at expansion time on the
s-expressions Racket's reader produces, by
`rhombus-hol/rhombus/hol/tests/idris_kernel.rkt`, which is exercised (and
kept correct) by the tests described in the main README rather than by a
standalone script.

# idris-kernel

An exploratory Idris2 port of the LCF kernel
(`rhombus-hol-lib/rhombus/hol/private/{htype,term,kernel}.rhm`), compiled
through Idris2's Racket backend.

**Status: prototype, not wired in.** `rhombus-hol-lib/.../kernel.rhm` remains
the trust boundary that Rhombus/HOL actually uses. This directory is not
referenced by either Racket package (`rhombus-hol-lib`, `rhombus-hol`) and
does not participate in `raco make` / `raco test`. See `../PLAN.md`.

## Layout

- `src/HType.idr` — HOL types (`htype.rhm`).
- `src/Term.idr` — locally-nameless terms (`term.rhm`).
- `src/Kernel.idr` — the ten primitive inference rules and theory extension
  (`kernel.rhm`), returning `Either String a` rather than raising.
- `src/Main.idr` — a smoke test mirroring the first few checks in
  `rhombus-hol/rhombus/hol/tests/kernel.rhm`.

## Building

```sh
cd idris-kernel
idris2 --cg racket --build kernel.ipkg
racket build/exec/kernel_app/kernel.rkt   # or just: build/exec/kernel
```

The default backend (Chez, via `idris2 --build kernel.ipkg`) also works; pass
`--cg racket` to get Racket source instead of a Chez-compiled executable.

## Known gaps versus the Rhombus kernel

- `Thm`/`Theory` are ordinary exported records, not yet given the
  construction-proof boundary the Rhombus kernel has (`authentic`,
  `constructor ~none`, an unexported `internal` constructor). Idris2's
  `export`/`public export` visibility can express the same shape of
  boundary, but that has not been done here.
- Fresh theory-node identity is a threaded `Nat` counter, not an uninterned
  symbol; callers must pass the next counter through by hand.
- `new_basic_type_definition`'s soundness comment and `dest_abs`'s
  human-readable variable naming (`x, y, z, u, v, w, ...`) are ported as
  logic but not re-explained here; read the `.rhm` originals for the "why".
- No proofs of totality/soundness beyond what Idris2's (non-`%default
  total`) checker gives for free -- `%default covering` is used throughout,
  and list recursion into `HType`/`Term` is hand-written in `mutual` blocks
  because Idris2 0.8.0's termination checker does not see through
  `Eq`/`Show`'s default methods or higher-order list combinators (`map`,
  `foldl`, `any`) applied to a type mutually recursive with `List`.

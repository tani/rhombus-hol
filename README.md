# Rhombus/HOL

Rhombus/HOL is a theorem prover embedded in Rhombus as `#lang rhombus/hol`:
an LCF-style higher-order-logic kernel with an ACL2-style automatic prover on
top, where a definition is simultaneously a logical declaration and
executable Rhombus code.

```rhombus
#lang rhombus/hol

datatype List.of(?a)
| Nil()
| Cons(head :: ?a, tail :: List.of(?a))

function app(xs :: List.of(?a), ys :: List.of(?a)) :: List.of(?a):
  match xs
  | Nil(): ys
  | Cons(x, rest): Cons(x, app(rest, ys))

theorem app_nil_r:
  forall (xs :: List.of(?a)): app(xs, Nil()) === xs
```

That module exports a working `app` function, and it does not compile unless
`app_nil_r` is proved. Proofs run while the module compiles, not when it is
run: a failed proof, or a definition that cannot be shown to terminate, is a
compile error with the goals left over.

## Packages

- `rhombus-hol-kernel` — the LCF kernel: the whole trust boundary.
- `rhombus-hol-quickcheck` — standalone runtime property-checking support.
- `rhombus-hol-prover` — the derived rules, the prover, and `#lang rhombus/hol`.
- `rhombus-hol-stdlib` — the proved standard library.
- `rhombus-hol` — the distribution metapackage, documentation, and test suite.

## Building

```sh
raco pkg install --link \
  ./rhombus-hol-kernel ./rhombus-hol-quickcheck ./rhombus-hol-prover \
  ./rhombus-hol-stdlib ./rhombus-hol
raco make rhombus-hol-prover/rhombus/hol.rkt
raco test rhombus-hol/rhombus/hol/tests
```

## Formal kernel generation

`rhombus-hol-kernel/rhombus/hol/kernel_generated.rhm` is generated from the
Isabelle definitions and has a versioned ABI with the handwritten façade.
Regenerate it, including the Isabelle session build, with:

```sh
./isabelle-hol-kernel/export-kernel.sh
```

CI runs the same entry point with `--check`; that mode fails unless the
committed artifact exactly matches the Isabelle export.

## Documentation

```sh
raco setup --pkgs rhombus-hol
```

builds the manual at `rhombus-hol/rhombus/hol/doc/rhombus-hol/index.html`,
which covers the declaration forms, the surface grammar, termination
checking, the prover, and what the system does and does not trust.

The published documentation includes both the user manual and the
machine-checked Isabelle development:

- [Rhombus/HOL manual](https://tani.github.io/rhombus-hol/rhombus-hol/index.html)
- [Isabelle/HOL kernel verification](https://tani.github.io/rhombus-hol/isabelle/Unsorted/Rhombus_HOL_Kernel/index.html)
- [Verification audit theory](https://tani.github.io/rhombus-hol/isabelle/Unsorted/Rhombus_HOL_Kernel/Rhombus_HOL_Audit.html)

GitHub Actions regenerates these pages from `main`; the Isabelle presentation
contains the checked source, definitions, theorem statements, proof text, and
links into the imported HOL and HOL-ZF sessions.

## License

`LICENSE` contains the 0BSD terms for original Rhombus/HOL material.
[`REUSE.toml`](REUSE.toml) is the authoritative per-file copyright and SPDX
license map. [`THIRD_PARTY_NOTICES`](THIRD_PARTY_NOTICES) records exact
source-derived scopes separately from design references and generated assets;
[`LICENSES/`](LICENSES/) contains canonical SPDX terms, while
[`THIRD_PARTY_LICENSES/`](THIRD_PARTY_LICENSES/) retains audited upstream
notices and exact revisions. Package-local copies keep independently
distributable archives self-contained.

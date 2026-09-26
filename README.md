# Rhombus/HOL

Rhombus/HOL is an LCF-style higher-order-logic theorem prover embedded in
Rhombus, with a machine-checked Isabelle/HOL kernel behind it: the `#lang
rhombus/hol` surface language, its derived prover, and a proved standard
library all sit on top of that kernel.

## Packages

- `rhombus-hol-kernel` — the LCF kernel: the whole trust boundary, generated
  from and checked against `isabelle-hol-kernel`.
- `isabelle-hol-kernel` — the Isabelle/HOL formalization the kernel is
  generated from and checked against.
- `rhombus-hol-quickcheck` — runtime property-checking support, independent
  of the prover.
- `rhombus-hol-prover` — the derived layer built over the kernel and
  QuickCheck: tactics, conversions, and the `#lang rhombus/hol` language
  surface (frontend elaboration, the waterfall proof procedure, recursive
  function and datatype definition).
  Its modules under `rhombus/hol/` follow the pipeline:
  - `frontend/parser` — declaration shapes and HOL expression syntax into
    theory-independent Core values;
  - `frontend/checker` — typing and name resolution: each declaration is
    checked once, and both backends consume the closed result;
  - `backend/code` — lowering checked terms to executable Rhombus;
  - `backend/proof` — lowering checked terms into kernel terms, the
    definition principles, the derived logic, and proof automation;
  - `module.rhm` — the declaration macros that connect the stages.
- `rhombus-hol-stdlib` — a proved standard library built on the prover.
- `rhombus-hol` — the top-level package: `#lang rhombus/hol` itself, the
  test suite, and the documentation.

## Building

```sh
raco pkg install --auto --link \
  ./rhombus-hol-kernel ./rhombus-hol-quickcheck ./rhombus-hol-prover \
  ./rhombus-hol-stdlib ./rhombus-hol
raco make rhombus-hol-prover/rhombus/hol.rkt
```

## Testing

```sh
raco test --jobs 4 rhombus-hol/rhombus/hol/tests
```

The test tree mirrors the prover's layout (`frontend/`, `backend/`), with
`module/` holding end-to-end tests of whole declarations, and `kernel/`,
`quickcheck/`, `stdlib/`, and `spec/` covering the other packages and the
language specification.

## Formal kernel generation

`rhombus-hol-kernel/rhombus/hol/kernel/generated.rhm` is generated from the
Isabelle definitions and has a versioned ABI with the handwritten façade.
Regenerate it, including the Isabelle session build, with:

```sh
./isabelle-hol-kernel/tools/export-kernel.sh
```

CI runs the same entry point with `--check`; that mode fails unless the
committed artifact exactly matches the Isabelle export.

## Documentation

[`docs/LANGUAGE_SPEC.md`](docs/LANGUAGE_SPEC.md) is the normative specification
for the `#lang rhombus/hol` surface language: the language layer, the logical
effect of declarations, and the required trust and execution boundaries.

The published documentation is built from this branch:

- [Rhombus/HOL manual](https://tani.github.io/rhombus-hol/rhombus-hol/index.html)
- [Isabelle/HOL kernel verification](https://tani.github.io/rhombus-hol/isabelle/Unsorted/Rhombus_HOL_Kernel/index.html)
- [Verification audit theory](https://tani.github.io/rhombus-hol/isabelle/Unsorted/Rhombus_HOL_Kernel/verification/Rhombus_HOL_Audit.html)

GitHub Actions regenerates these pages; the Isabelle presentation contains
the checked source, definitions, theorem statements, proof text, and links
into the imported HOL and HOL-ZF sessions.

## License

`LICENSE` contains the 0BSD terms for original Rhombus/HOL material.
[`REUSE.toml`](REUSE.toml) is the authoritative per-file copyright and SPDX
license map. [`THIRD_PARTY_NOTICES`](THIRD_PARTY_NOTICES) records exact
source-derived scopes separately from design references and generated assets;
[`LICENSES/`](LICENSES/) contains canonical SPDX terms, while
[`THIRD_PARTY_LICENSES/`](THIRD_PARTY_LICENSES/) retains audited upstream
notices and exact revisions. Package-local copies keep independently
distributable archives self-contained.

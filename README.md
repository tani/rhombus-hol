# Rhombus/HOL

Rhombus/HOL is an LCF-style higher-order-logic kernel embedded in Rhombus,
with a machine-checked Isabelle/HOL development behind it.

This branch (`rhombus-hol-native-arith`) carries only the kernel: the
prover, standard library, and `#lang rhombus/hol` surface language are being
rebuilt on top of it with a native (not Peano-unary) arithmetic
representation, and are not present here. See `main` for the working
language and prover.

## Packages

- `rhombus-hol-kernel` — the LCF kernel: the whole trust boundary.
- `isabelle-hol-kernel` — the Isabelle/HOL formalization the kernel is
  generated from and checked against.

## Building

```sh
raco pkg install --link ./rhombus-hol-kernel
raco make rhombus-hol-kernel/rhombus/hol/kernel.rhm
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

The language decisions for that rebuild are recorded in
[`LANGUAGE_SPEC.md`](LANGUAGE_SPEC.md).

The published documentation for the full system (kernel, prover, standard
library) is built from `main`:

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

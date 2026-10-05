# Rhombus/HOL

A direct Rhombus reimplementation of HOL Light.

This branch intentionally starts from a small, single-package codebase.  The
implementation order follows upstream HOL Light closely:

```
fusion.ml
basics.ml
nets.ml
equal.ml
bool.ml
drule.ml
tactics.ml
simp.ml
parser.ml
preterm.ml
printer.ml
```

The current code begins with `rhombus/hol/fusion.rhm`.  No Isabelle-generated
kernel, previous Rhombus prover, waterfall implementation, or compatibility
layer is used.

## Build

```sh
raco pkg install --auto --batch --no-docs --skip-installed .
raco make rhombus/hol/fusion.rhm
raco test rhombus/hol/tests
```

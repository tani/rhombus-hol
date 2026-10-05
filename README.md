# Rhombus/HOL

A direct Rhombus reimplementation of HOL Light.

This branch intentionally uses a small, single-package codebase and follows
upstream HOL Light's module order closely.

## Restored validated core

The direct translations completed before the repository restart are included:

- `rhombus/hol/fusion.rhm`
- `rhombus/hol/basics.rhm`
- `rhombus/hol/nets.rhm`
- `rhombus/hol/equal.rhm`

with their small compatibility/support modules. These are the versions from
the earlier differential-validation work, which matched the pinned HOL Light
implementation on 3,914/3,914 generated cases.

The next translation targets are:

```
bool.ml
drule.ml
tactics.ml
simp.ml
parser.ml
preterm.ml
printer.ml
```

No Isabelle-generated kernel, waterfall implementation, previous
Rhombus/HOL frontend, or old multi-package architecture is used.

## Build

```sh
raco pkg install --auto --batch --no-docs --skip-installed .
raco make rhombus/hol/equal.rhm
raco test rhombus/hol/tests
```

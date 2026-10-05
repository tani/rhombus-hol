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
raco pkg install --auto --batch --no-docs --skip-installed --name rhombus-hol "$PWD"
raco make rhombus/hol/equal.rhm
raco test rhombus/hol/tests
```


## Differential verification

The full differential harness is under `differential/`. It builds an OCaml
oracle from the pinned HOL Light sources and compares it against the live
Rhombus implementation.

```sh
python3 differential/tests/run.py
python3 differential/tests/run_upper.py
```

The two suites contain 1,296 kernel cases and 2,618 upper-layer cases,
respectively. They are intentionally excluded from normal CI; the
`Differential` GitHub Actions workflow is manual-only.

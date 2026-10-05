# Differential harness

Differential testing for the direct HOL Light → Rhombus port.

The oracle is built offline from the pinned HOL Light sources bundled under
`upstream/`. The Rhombus side imports the live implementation from
`../rhombus/hol/`; there is no duplicate port tree.

Pinned HOL Light revision:
`cba9198db76e9dfb89cbd653df9412d01f65b22a`.

Requirements: Python 3, OCaml 4.14.x, OCaml Num, Racket 9.3 CS, and Rhombus.

Run:

```sh
python3 differential/tests/run.py
python3 differential/tests/run_upper.py
```

Expected totals for the restored `fusion/basics/nets/equal` translation:
1,296 kernel cases + 2,618 upper-layer cases = 3,914 exact matches.

This harness is intentionally not part of the normal fast CI. Use it locally
or invoke the dedicated manual GitHub Actions workflow.
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
1,296 kernel cases + 2,452 upper-layer cases = 3,748 common cases.
The partially restored native-private candidate preserves exact `atoms-bulk`
order through the original Patricia map and OCaml hash implementation.

Without `HOL_ENGINE_ONLY=1`, a checkout containing `private/term_hash.rhm`
also runs 164 internal hash cases, for a total of 3,912 checks.
Two obsolete frontend cases were removed.

This harness is intentionally not part of the normal fast CI. Use it locally
or invoke the dedicated manual GitHub Actions workflow.
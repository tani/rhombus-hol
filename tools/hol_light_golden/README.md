# HOL Light differential data

Offline tools that run the pinned HOL Light
(`cba9198db76e9dfb89cbd653df9412d01f65b22a`) to produce data for the
Rhombus/HOL tests. Nothing here is loaded by Rhombus/HOL; the tests compare
against the data and replay every proof in the Rhombus kernel.

Requirements: a HOL Light checkout at the pinned revision built with `make`
(OCaml 4.14, camlp5, zarith, findlib). Loading `hol.ml` takes a few minutes.

| File | Purpose |
|---|---|
| `dump.ml` | Serializers for types, terms and theorems, and the state dump. |
| `generate.sh` | Writes `rhombus/hol/tests/golden/hol_light.tsv.gz`. |
| `quote.ml` | Prints a term as Rhombus `hol_term(...)` constructor syntax. |
| `capture.ml` | Records the quotations an upstream file parses, in order. |
| `basic_tests_terms.ml` | Expands the quotations of `UnitTests/basic_tests.ml`. |

## Golden logical state

```sh
tools/hol_light_golden/generate.sh /path/to/hol-light
```

The output lists, in HOL Light's order, every type constant, term constant,
axiom and definition, and every toplevel theorem (the `database.ml` list plus
column-0 bindings of the ported modules). Each line is
`kind TAB name TAB serial`; the encoding is shared with
`rhombus/hol/tests/golden/serial.rhm`. The generation is deterministic.

`rhombus/hol/tests/golden/hol_light.rhm` loads every module and requires each
row to match exactly, or up to the numbering of names invented at run time
(`_<n>` genvars and `?<n>` type variables). HOL Light's parser advances both
counters while elaborating quotations; offline expansion does not, so their
numbering drifts while the statements agree. Accepted differences go in
`known_differences.tsv` with a reason.

## Upstream tests and examples

Quotations are expanded offline in a HOL Light session and pasted into the
Rhombus test as `def q<n> = hol_term(...)`:

```sh
cd /path/to/hol-light
printf '#use "%s/quote.ml";;\n#use "%s/basic_tests_terms.ml";;\n' "$T" "$T" | LINE_EDITOR=env ./hol.sh

printf '#use "%s/quote.ml";;\n#use "%s/dump.ml";;\n#use "%s/capture.ml";;\n%s\n' \
  "$T" "$T" "$T" 'capture_start ();; loadt "Examples/dickson.ml";; capture_emit ["DICKSON"];;' |
  LINE_EDITOR=env ./hol.sh
```

where `T` is this directory. `capture_emit` also prints each named theorem's
serial (`// golden` lines) for comparison in the ported test.

# Evaluating the Boyer-Moore waterfall

`rhombus/hol/Boyer_Moore/` translates HOL Light's `Boyer_Moore/` library,
the prover of P. Papapanagiotou and J. Fleuriot, "The Boyer-Moore Waterfall
Model Revisited" (arXiv:1808.03810). These tools run it on upstream's
`testset/` and compare the results with the paper's Appendix B.

```sh
raco make tools/boyer_moore_eval/eval.rhm
racket tools/boyer_moore_eval/eval.rhm 60 run.tsv paper   # Appendix A rules
racket tools/boyer_moore_eval/eval.rhm 60 run.tsv         # make.ml's bm_reset
python3 tools/boyer_moore_eval/compare.py run.tsv [--rows]
```

- `eval.rhm`: the heuristics of `BOYER_MOORE_FINAL` (BMF) on the 119
  arithmetic and 48 list conjectures, with a time limit per conjecture, and
  the reason of each failure (see the file).
- `appendix_b.tsv`: Appendix B transcribed (BMF on the paper's "HOL Light
  Test Set", 116 rows, 54 proved; the paper's text says 120 and 47%). The
  paper's Rippling test set uses functions that upstream's `testset/` does
  not define (`DBL`, `HALF`, `QREV`, `NTH`) and is not compared.
- `compare.py`: matches a run with Appendix B by theorem text.

## Results (60 s per conjecture)

With the paper's rewrite rules (`paper`), the port reproduces Appendix B:

- 115 of the 116 rows agree on proved or failed. The 54 theorems the paper
  proves are proved, each with the paper's number of proof steps and
  inductions; 52 also with the same generalizations and overgeneralizations,
  2 differ by one detected overgeneralization.
- Row 28, `n EXP SUC (SUC 0) = n * n`, is proved by the port (85 steps,
  12 inductions, 6 generalizations, 3.6 s) and failed in the paper (0.38 s).
  The counterexample checker that accepts or rejects a generalization
  samples random values, so these two cases may differ by the random
  choices.
- The 61 failures common to both: max_var_depth exceeded 27, a clause
  refuted ("cannot prove") 14, induction loop detected 12, no induction
  possible 4, time limit 4. The paper marks every failure as one detected
  by its loop elimination (depth or loop). The 4 time-outs (rows 45, 78,
  108, 114) fail in the paper within 7.4 s.

With `make.ml`'s `bm_reset`, which adds `~(SUC n = n)` and
`a + SUC b = SUC (a + b)` to Appendix A's rules, 61 of the 119 arithmetic
conjectures are proved (7 more than the paper), often in fewer steps, and 26
of the 48 list conjectures.

Proof times of proved conjectures: median 0.24 s, mean 0.74 s, maximum
4.1 s (arithmetic, port); the paper reports median 0.084 s, mean 0.13 s.

One failure of the list set, conjecture 27 (`ALL P l /\ ALL Q l <=> ALL
(\x. P x /\ Q x) l`), comes from HOL Light's `term_match`: `term_homatch`
keeps an instantiation when a higher-order pattern's head equals the term's
(drule.ml, `if compare chop vhop = 0 then insts`), without checking a
binding of that head made earlier, so the instance trees of the clause pool
take one pool clause for an instance of another, and the instance theorem is
then rejected (`prove_inst_trees`). The port's `drule.rhm` translates this
as is.

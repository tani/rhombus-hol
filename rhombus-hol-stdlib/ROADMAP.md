# rhombus-hol-stdlib theorem tiers

## Core-100

Core is the following exact, stable 100-theorem manifest. Ordering is normative.

### `algebra.rhm`
1. `iterate_zero`
2. `iterate_succ`
3. `iterate_add`
4. `nat_min_idempotent`
5. `nat_max_idempotent`
6. `nat_min_zero_left`
7. `nat_max_zero_left`
8. `nat_clamp_zero`

### `algorithm.rhm`
9. `insertion_sort_nil`
10. `insertion_sort_cons`
11. `factorial_zero`
12. `factorial_succ`
13. `choose_zero_zero`
14. `choose_succ_zero`
15. `string_append_empty_left`
16. `string_append_empty_right`
17. `string_codes_roundtrip`
18. `string_from_codes_roundtrip`

### `data.rhm`
19. `fst_pair`
20. `snd_pair`
21. `pair_eta`
22. `pair_eq`
23. `left_injective`
24. `right_injective`
25. `left_ne_right`
26. `some_injective`
27. `none_ne_some`
28. `option_map_none`
29. `option_map_some`
30. `option_map_id`
31. `option_map_compose`
32. `option_bind_none`
33. `option_bind_some`
34. `option_bind_right_identity`
35. `option_get_or_none`
36. `option_get_or_some`
37. `option_is_some_none`
38. `option_is_some_some`
39. `pair_swap_involutive`
40. `pair_association_inverse_left`
41. `pair_association_inverse_right`
42. `uncurry_curry`
43. `curry_uncurry`
44. `either_bimap_compose`
45. `either_swap_involutive`
46. `option_bind_associative`
47. `option_eliminate_none`
48. `option_eliminate_some`
49. `option_is_none_none`
50. `option_is_none_some`

### `finite.rhm`
51. `fset_member_empty`
52. `fset_member_to_set`
53. `fset_cardinality_empty`
54. `alist_lookup_nil`
55. `alist_lookup_cons_hit`
56. `map_lookup_empty`
57. `map_lookup_insert_same`
58. `map_values_compose`

### `integer.rhm`
59. `int_negate_zero`
60. `int_negate_positive`
61. `int_negate_negative`
62. `int_negate_involutive`
63. `int_abs_nonnegative`
64. `int_abs_negative`
65. `int_abs_negate`
66. `int_add_zero_left`
67. `int_add_zero_right`
68. `int_add_inverse_left`
69. `int_subtract_zero`
70. `int_subtract_self`
71. `int_multiply_zero_left`
72. `int_multiply_zero_right`
73. `int_from_nat_add`
74. `int_from_nat_multiply`
75. `int_le_from_nat`
76. `int_le_reflexive`

### `list.rhm`
77. `append_nil_left`
78. `append_cons`
79. `append_nil_right`
80. `append_associative`
81. `append_left_cancel`
82. `length_nil`
83. `length_cons`
84. `length_append`
85. `length_map`
86. `length_reverse`
87. `length_replicate`
88. `map_nil`
89. `map_cons`
90. `map_id`
91. `map_compose`
92. `map_append`
93. `reverse_nil`
94. `reverse_cons`
95. `reverse_append`
96. `reverse_involutive`
97. `map_reverse`
98. `member_nil`
99. `member_cons`
100. `member_append`

## Standard-1000

Standard contains Core-100 plus every theorem in the shipped modules. The current kernel-checked baseline is 1,001 theorems.

* 400 → 1,001 adds executable Boolean, natural-order, list, relation/set, rose-tree, integer, finite-collection, rational, algebra, quotient, number-theory, and programming APIs.
* The corresponding theorem families cover constructor equations, observer normal forms, pointwise Boolean algebra, option/list/tree transformations, arithmetic/order interfaces, and cross-domain consumer behavior.

A theorem enters Standard only after its defining module compiles and the full prover regression suite passes.

## Full

Full is the open-ended union of Standard and domain libraries for logic, equality, quantifiers, functions, products, sums, options, naturals, lists, nonempty sequences, trees, relations, orders, predicate sets, finite sets, maps, association lists, integers, rationals, algebra, lattices, quotients, combinatorics, number theory, finite sums/products, sorting, strings, predicates, isomorphisms, functional laws, and proof engineering. Full additions follow the same kernel-checked admission rule; no theorem is admitted through an axiom or placeholder.

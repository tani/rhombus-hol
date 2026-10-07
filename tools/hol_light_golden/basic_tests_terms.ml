(* ========================================================================= *)
(* Expand the quotations of UnitTests/basic_tests.ml (pinned revision) into  *)
(* hol_term(...) definitions (input of to_hol.py) for                        *)
(* rhombus/hol/tests/upstream/basic_tests.rhm.                               *)
(* Quotations are parsed in test order, so constants defined by earlier     *)
(* steps (benign redefinition) are parsed as constants, as upstream does.   *)
(* Run after hol.ml and quote.ml; prints Rhombus definitions to stdout.     *)
(* ========================================================================= *)

let emit name tm = print_string ("def " ^ name ^ " = " ^ rhombus_quote tm ^ "\n");;

emit "compute_if_open" `if x then 1 + 2 else 3 + 4`;;
emit "compute_if_true" `if true then 1 + 2 else 3 + 4`;;
emit "compute_three" `3`;;
emit "compute_lambda" `\x. x + (1 + 2)`;;
emit "compute_beta" `(\x. x + (1 + 2)) (3 + 4)`;;
emit "compute_ten" `10`;;
emit "compute_unknown" `(unknown_fn:num->num) (1+2)`;;
emit "compute_unknown_reduced" `(unknown_fn:num->num) 3`;;

emit "list_of_seq_in" `list_of_seq (\i. f(i + 17):B) 3`;;
emit "list_of_seq_out" `[f (0 + 17):B; f (1 + 17); f (2 + 17)]`;;
emit "el_in" `EL 1 [0;1;2;3;4]`;;
emit "el_out" `1`;;
emit "length_in" `LENGTH[1;2;3;4;5]`;;
emit "length_out" `5`;;
emit "reverse_in" `REVERSE[a:X;b;c;d]`;;
emit "reverse_out" `[d:X;c;b;a]`;;

emit "cbv_genabs_in" `(\((x,y),(z,w)). x + y + z + w) ((1,2),(3,4))`;;
emit "cbv_genabs_out" `1 + 2 + 3 + 4`;;
emit "cbv_body_in" `(\((x,y),(z,w)):(num#num)#(num#num). true /\ true)`;;
emit "cbv_body_out" `(\((x,y),(z,w)):(num#num)#(num#num). true)`;;
emit "cbv_match_in" `match [1;2;3;4;5] with [] -> [] | CONS x (CONS y z) -> z`;;
emit "cbv_match_out" `[3; 4; 5]`;;
emit "cbv_let_in" `let x = 1 in x + 2`;;
emit "cbv_let_out" `1 + 2`;;

let h_benign = `(h_benign:A list -> num) [] = 0 /\
                h_benign (CONS _ t) = 1 + h_benign t`;;
emit "benign_define_first" h_benign;;
let _ = define h_benign;;
emit "benign_define_second" `(h_benign:A list -> num) [] = 0 /\
                h_benign (CONS _ t) = 1 + h_benign t`;;

let steps_tm = `(forall s. steps (step:S->S->bool) 0 (s:S) (s:S)) /\
   (forall s s'' n. (exists s'. step s s' /\ steps step n s' s'')
      ==> steps step (n+1) s s'')`;;
emit "benign_inductive_first" steps_tm;;
let _ = new_inductive_definition steps_tm;;
emit "benign_inductive_second" `(forall s. steps (step:S->S->bool) 0 (s:S) (s:S)) /\
   (forall s s'' n. (exists s'. step s s' /\ steps step n s' s'')
      ==> steps step (n+1) s s'')`;;

emit "er_goal_1" `x + 1 = 1 + x /\ 1 + 1 = 2`;;
emit "er_goal_2" `(x + 1 = 1 + x /\ (x + y) + z = x + (y + z)) /\ 1 + 1 = 2`;;

emit "unify_refl_1" `?x. 1 = x`;;
emit "unify_refl_2" `?f. y + z = f y z`;;
emit "unify_refl_3" `?f. y + 1 = f y 0`;;

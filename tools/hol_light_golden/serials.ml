(* ========================================================================= *)
(* Print the serials of named theorems for an upstream example's port.      *)
(*                                                                           *)
(* Run after hol.ml and dump.ml (without HOL_GOLDEN_OUT), then load the     *)
(* example and call emit_serials with the theorem names to check:            *)
(*   loadt "Examples/x.ml";; emit_serials ["THM"];;                          *)
(* Each theorem is printed as a `// golden` line for the ported test.        *)
(* ========================================================================= *)

let emit_serials names =
  print_newline ();
  List.iter (fun name ->
    match golden_lookup name with
      Some th -> print_string ("// golden\t" ^ name ^ "\t" ^ golden_thm th ^ "\n")
    | None -> print_string ("// golden\t" ^ name ^ "\tMISSING\n"))
    names;;

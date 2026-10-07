(* ========================================================================= *)
(* Capture the quotations of an upstream example for offline expansion.     *)
(*                                                                           *)
(* Run after hol.ml, quote.ml and dump.ml (without HOL_GOLDEN_OUT), then     *)
(* load the example and call capture_emit with the theorem names to check:   *)
(*   capture_start ();; loadt "Examples/x.ml";; capture_emit ["THM"];;       *)
(* Each distinct quotation is printed, in first-use order, as a Rhombus     *)
(* hol_term(...) definition q<n> (input of to_hol.py) preceded by its        *)
(* source text; each named theorem is printed with its serial for the        *)
(* golden comparison.                                                        *)
(* ========================================================================= *)

let captured = ref ([] : (string * term) list);;

let capture_parse_term = parse_term;;

let capture_start () = captured := [];;

let parse_term s =
  let tm = capture_parse_term s in
  (if not (exists (fun (s',_) -> s' = s) !captured)
   then captured := (s,tm) :: !captured);
  tm;;

let capture_emit names =
  print_newline ();
  let comment s =
    String.concat "\n" (map (fun l -> "// " ^ String.trim l)
      (String.split_on_char '\n' (String.trim s))) in
  List.iteri (fun i (s,tm) ->
    print_string (comment s ^ "\ndef q" ^ string_of_int (i + 1) ^ " = " ^
                  rhombus_quote tm ^ "\n"))
    (rev !captured);
  List.iter (fun name ->
    match golden_lookup name with
      Some th -> print_string ("// golden\t" ^ name ^ "\t" ^ golden_thm th ^ "\n")
    | None -> print_string ("// golden\t" ^ name ^ "\tMISSING\n"))
    names;;

(* ========================================================================= *)
(* Printed forms for the Rhombus/HOL printer tests.                          *)
(*                                                                           *)
(* Run inside a HOL Light toplevel (pinned revision) after hol.ml and       *)
(* dump.ml. Writes, one per line, KIND TAB NAME TAB TEXT with the printer's *)
(* output escaped (backslash, tab and newline):                              *)
(*   const NAME (string_of_type of its generic type)                         *)
(*   axiom/definition INDEX, thm NAME (string_of_thm)                        *)
(*   goal NAME (pp_print_goalstack after g of the conclusion and           *)
(*              e (REPEAT STRIP_TAC), for the first theorems by name)        *)
(* ========================================================================= *)

let printed_escape s =
  let b = Buffer.create (String.length s) in
  String.iter (fun c -> match c with
      '\\' -> Buffer.add_string b "\\\\"
    | '\n' -> Buffer.add_string b "\\n"
    | '\t' -> Buffer.add_string b "\\t"
    | c -> Buffer.add_char b c) s;
  Buffer.contents b;;

let printed_dump () =
  let out = open_out (Sys.getenv "HOL_PRINTED_OUT") in
  let emit kind name text =
    output_string out (kind ^ "\t" ^ name ^ "\t" ^ printed_escape text ^ "\n") in
  List.iter (fun (s,ty) -> emit "const" s (string_of_type ty)) (rev (constants()));
  List.iteri (fun i th -> emit "axiom" (string_of_int i) (string_of_thm th))
    (rev (axioms()));
  List.iteri (fun i th -> emit "definition" (string_of_int i) (string_of_thm th))
    (rev (definitions()));
  let names = ref [] in
  let ic = open_in (Sys.getenv "HOL_GOLDEN_NAMES") in
  (try while true do
     let l = String.trim (input_line ic) in
     if l <> "" && not (mem l !names) then names := l :: !names
   done with End_of_file -> close_in ic);
  List.iter (fun (n,_) -> if not (mem n !names) then names := n :: !names)
    !theorems;
  let found = ref [] in
  List.iter (fun name ->
    match golden_lookup name with
      Some th -> emit "thm" name (string_of_thm th); found := (name,th) :: !found
    | None -> ())
    (sort (<) !names);
  let goals = ref 0 in
  List.iter (fun (name,th) ->
    if !goals < 40 && hyp th = [] then
      try
        ignore (g (concl th));
        ignore (e (REPEAT STRIP_TAC));
        emit "goal" name
          (Format.asprintf "%a" pp_print_goalstack !current_goalstack);
        incr goals
      with _ -> ())
    (rev !found);
  close_out out;;

if (try Sys.getenv "HOL_PRINTED_OUT" <> "" with Not_found -> false)
then printed_dump ();;

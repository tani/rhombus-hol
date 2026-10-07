(* ========================================================================= *)
(* Dump the logical state of HOL Light after the standard load sequence.    *)
(*                                                                           *)
(* Run inside a HOL Light toplevel (pinned revision) after hol.ml:          *)
(*   HOL_GOLDEN_NAMES=names.txt HOL_GOLDEN_OUT=out.tsv  then #use this file. *)
(* Without HOL_GOLDEN_OUT only the serializers are defined.                  *)
(* Each output line is  kind TAB name TAB serial  where serial uses the     *)
(* encoding shared with rhombus/hol/tests/golden/serial.rhm.               *)
(* ========================================================================= *)

let golden_quote s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter (fun c ->
    let n = Char.code c in
    if c = '"' then Buffer.add_string b "\\\""
    else if c = '\\' then Buffer.add_string b "\\\\"
    else if n < 0x20 || n > 0x7e then Buffer.add_string b (Printf.sprintf "\\u%04x" n)
    else Buffer.add_char b c) s;
  Buffer.add_char b '"';
  Buffer.contents b;;

let rec golden_type ty =
  if is_vartype ty then "V" ^ golden_quote (dest_vartype ty) else
  let s,args = dest_type ty in
  "T" ^ golden_quote s ^ "(" ^ String.concat "," (map golden_type args) ^ ")";;

let rec golden_term tm =
  if is_var tm then
    let n,ty = dest_var tm in "v" ^ golden_quote n ^ ":" ^ golden_type ty
  else if is_const tm then
    let n,ty = dest_const tm in "c" ^ golden_quote n ^ ":" ^ golden_type ty
  else if is_comb tm then
    let f,x = dest_comb tm in "(" ^ golden_term f ^ " " ^ golden_term x ^ ")"
  else
    let v,b = dest_abs tm in "\\" ^ golden_term v ^ "." ^ golden_term b;;

let golden_thm th =
  "[" ^ String.concat ";" (map golden_term (hyp th)) ^ "]|-" ^ golden_term (concl th);;

let golden_candidate = ref (None : thm option);;

let golden_lookup name =
  golden_candidate := None;
  let src = "golden_candidate := Some (" ^ name ^ " : thm);;" in
  (try
     let ph = !Toploop.parse_toplevel_phrase (Lexing.from_string src) in
     ignore (Toploop.execute_phrase false Format.str_formatter ph)
   with _ -> ());
  ignore (Format.flush_str_formatter ());
  !golden_candidate;;

let golden_dump () =
  let out = open_out (Sys.getenv "HOL_GOLDEN_OUT") in
  let emit kind name serial =
    output_string out (kind ^ "\t" ^ name ^ "\t" ^ serial ^ "\n") in
  List.iter (fun (s,n) -> emit "type" s (string_of_int n)) (rev (types()));
  List.iter (fun (s,ty) -> emit "const" s (golden_type ty)) (rev (constants()));
  List.iteri (fun i th -> emit "axiom" (string_of_int i) (golden_thm th))
    (rev (axioms()));
  List.iteri (fun i th -> emit "definition" (string_of_int i) (golden_thm th))
    (rev (definitions()));
  let names = ref [] in
  let ic = open_in (Sys.getenv "HOL_GOLDEN_NAMES") in
  (try while true do
     let l = String.trim (input_line ic) in
     if l <> "" && not (mem l !names) then names := l :: !names
   done with End_of_file -> close_in ic);
  List.iter (fun (n,_) -> if not (mem n !names) then names := n :: !names)
    !theorems;
  List.iter (fun name ->
    match golden_lookup name with
      Some th -> emit "thm" name (golden_thm th)
    | None -> ())
    (sort (<) !names);
  close_out out;;

if (try Sys.getenv "HOL_GOLDEN_OUT" <> "" with Not_found -> false)
then golden_dump ();;

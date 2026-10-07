(* ========================================================================= *)
(* Offline quotation expansion: print a parsed HOL Light term as the        *)
(* Rhombus hol_term(...) constructor syntax of private/quoted_ast.rhm.       *)
(* Used to port upstream tests; the output contains no theorems.            *)
(* ========================================================================= *)

let rhombus_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter (fun c ->
    match c with
      '"' -> Buffer.add_string b "\\\""
    | '\\' -> Buffer.add_string b "\\\\"
    | '\n' -> Buffer.add_string b "\\n"
    | '\t' -> Buffer.add_string b "\\t"
    | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"';
  Buffer.contents b;;

let rec rhombus_type ty =
  if is_vartype ty then "Tvar(" ^ rhombus_string (dest_vartype ty) ^ ")" else
  match dest_type ty with
    "bool",[] -> "Bool"
  | "num",[] -> "Num"
  | "fun",[a;b] -> "Fun(" ^ rhombus_type a ^ ", " ^ rhombus_type b ^ ")"
  | s,args -> "Tyapp(" ^ rhombus_string s ^ ", [" ^
              String.concat ", " (map rhombus_type args) ^ "])";;

let rec rhombus_term tm =
  if is_var tm then
    let n,ty = dest_var tm in
    "Var(" ^ rhombus_string n ^ ", " ^ rhombus_type ty ^ ")"
  else if is_const tm then
    let n,ty = dest_const tm in
    "Const(" ^ rhombus_string n ^ ", " ^ rhombus_type ty ^ ")"
  else if is_comb tm then
    let f,args = strip_comb tm in
    "App(" ^ rhombus_term f ^ ", [" ^
    String.concat ", " (map rhombus_term args) ^ "])"
  else
    let v,b = dest_abs tm in
    "Abs(" ^ rhombus_term v ^ ", " ^ rhombus_term b ^ ")";;

let rhombus_quote tm = "hol_term(" ^ rhombus_term tm ^ ")";;

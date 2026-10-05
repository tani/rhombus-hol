(* Loaded in the unmodified upstream OCaml proof environment, after parser.ml.
   Record the inferred AST of each literal quotation, never a theorem axiom. *)
let quote_stage = try Sys.getenv "HOL_PORT_STAGE" with Not_found -> "/tmp/hol-port";;
let quote_channel = open_out (Filename.concat quote_stage "quotes.jsonl");;
let recorded_quotes = Hashtbl.create 4096;;
let json_string s = Printf.sprintf "%S" s;;
let json_list f xs = "[" ^ String.concat "," (List.map f xs) ^ "]";;
let rec quote_type = function
 | Tyvar s -> "[\"Tyvar\"," ^ json_string s ^ "]"
 | Tyapp(s,args) -> "[\"Tyapp\"," ^ json_string s ^ "," ^ json_list quote_type args ^ "]";;
let rec quote_term = function
 | Var(s,ty) -> "[\"Var\"," ^ json_string s ^ "," ^ quote_type ty ^ "]"
 | Const(s,ty) -> "[\"Const\"," ^ json_string s ^ "," ^ quote_type ty ^ "]"
 | Comb(f,a) -> "[\"Comb\"," ^ quote_term f ^ "," ^ quote_term a ^ "]"
 | Abs(v,b) -> "[\"Abs\"," ^ quote_term v ^ "," ^ quote_term b ^ "]";;
let record_quote key source ast =
 Hashtbl.replace recorded_quotes key ();
 output_string quote_channel ("[" ^ json_string key ^ "," ^ json_string source ^ "," ^ ast ^ "]\n");
 flush quote_channel;;
let record_parse_term key source =
 let t = parse_term source in record_quote key source (quote_term t); t;;
let record_parse_type key source =
 let t = parse_type source in record_quote key source (quote_type t); t;;
let record_unused_term key source =
 if Hashtbl.mem recorded_quotes key then () else ignore(record_parse_term key source);;
let record_unused_type key source =
 if Hashtbl.mem recorded_quotes key then () else ignore(record_parse_type key source);;
let record_theorem key th =
 record_quote key "theorem" ("[" ^ json_list quote_term (hyp th) ^ "," ^ quote_term (concl th) ^ "]");;
let record_export key name =
 try
  (* Only the oracle inspects the original abstract Sequent representation.
     Runtime translation uses no reflection and no new theorem constructor. *)
  let v = Toploop.getvalue name in
  let rec is_list x =
    if Obj.is_int x then (Obj.obj x:int) = 0 else
    Obj.tag x = 0 && Obj.size x = 2 && is_list(Obj.field x 1) in
  if Obj.is_block v && Obj.tag v = 0 && Obj.size v = 1 then
   let p = Obj.field v 0 in
   if Obj.is_block p && Obj.tag p = 0 && Obj.size p = 2 &&
      is_list(Obj.field p 0) && Obj.is_block(Obj.field p 1) &&
      Obj.tag(Obj.field p 1) <= 3 && Obj.size(Obj.field p 1) = 2
   then record_theorem key (Obj.obj v:thm)
   else ()
  else ()
 with Not_found -> ();;

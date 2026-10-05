(* Mechanical bridge from Camlp5's HOL Light AST to an explicit JSON tree.
   No proof rules or theorem constructors are supplied by this tool. *)
open Parsetree
open Asttypes
let str s = Printf.sprintf "%S" s
let arr xs = "[" ^ String.concat "," xs ^ "]"
let node k xs = arr (str k :: xs)
let rec lid = function Longident.Lident s -> s | Ldot(l,s) -> lid l ^ "." ^ s | Lapply _ -> failwith "applicative path"
let id l = str (lid l.Location.txt)
let constant = function
 | Pconst_integer(s,_) -> node "int" [str s]
 | Pconst_string(s,_,_) -> node "string" [str s]
 | Pconst_char c -> node "string" [str(String.make 1 c)]
 | Pconst_float(s,_) -> node "float" [str s]
let unsupported loc kind = failwith(Printf.sprintf "%s:%d: unsupported %s" loc.Location.loc_start.Lexing.pos_fname loc.loc_start.pos_lnum kind)
let rec pat p = match p.ppat_desc with
 | Ppat_any -> node "any" []
 | Ppat_var s -> node "var" [str s.txt]
 | Ppat_constant c -> constant c
 | Ppat_tuple ps -> node "tuple" [arr(List.map pat ps)]
 | Ppat_construct(l,None) -> node "construct" [id l; "null"]
 | Ppat_construct(l,Some(_,p)) -> node "construct" [id l;pat p]
 | Ppat_alias(p,s) -> node "alias" [pat p;str s.txt]
 | Ppat_or(p,q) -> node "or" [pat p;pat q]
 | Ppat_constraint(p,_) -> pat p
 | Ppat_record(fs,_) -> node "record" [arr(List.map(fun(l,p)->arr[id l;pat p]) fs)]
 | _ -> unsupported p.ppat_loc "pattern"
and exp e = match e.pexp_desc with
 | Pexp_apply({pexp_desc=Pexp_ident {txt=Longident.Lident ("parse_term"|"parse_type" as f);_};_},[(Nolabel,{pexp_desc=Pexp_constant(Pconst_string(s,_,_));_})]) -> node "quote" [str f;str s;string_of_int e.pexp_loc.loc_start.pos_cnum]
 | Pexp_ident l -> node "id" [id l]
 | Pexp_constant c -> constant c
 | Pexp_apply(f,args) ->
    let values=arr(List.map(fun (_,e)->exp e) args) in
    if List.for_all(fun(l,_)->l=Nolabel) args then node "apply" [exp f;values]
    else node "apply" [exp f;values;arr(List.map(fun(l,_)->str(match l with Nolabel->""|Labelled s->"~"^s|Optional s->"?"^s)) args)]
 | Pexp_tuple es -> node "tuple" [arr(List.map exp es)]
 | Pexp_construct(l,None) -> node "construct" [id l;"null"]
 | Pexp_construct(l,Some e) -> node "construct" [id l;exp e]
 | Pexp_fun(Nolabel,None,p,e) -> node "fun" [pat p;exp e]
 | Pexp_fun(l,d,p,e) -> node "labelfun" [str(match l with Labelled s|Optional s->s|Nolabel->"");str(match l with Optional _->"optional"|_->"labelled");(match d with None->"null"|Some e->exp e);pat p;exp e]
 | Pexp_function cs -> node "function" [arr(List.map case cs)]
 | Pexp_let(r,bs,e) -> node "let" [str(if r=Recursive then "rec" else "nonrec");arr(List.map binding bs);exp e]
 | Pexp_ifthenelse(c,t,f) -> node "if" [exp c;exp t;(match f with None -> "null" | Some e -> exp e)]
 | Pexp_match(e,cs) -> node "match" [exp e;arr(List.map case cs)]
 | Pexp_try(e,cs) -> node "try" [exp e;arr(List.map case cs)]
 | Pexp_sequence(a,b) -> node "seq" [exp a;exp b]
 | Pexp_constraint(e,_) -> exp e
 | Pexp_open(_,e) -> exp e
 | Pexp_array es -> node "array" [arr(List.map exp es)]
 | Pexp_while(c,e) -> node "while" [exp c;exp e]
 | Pexp_for(p,a,b,d,e) -> node "for" [pat p;exp a;exp b;str(if d=Upto then "up" else "down");exp e]
 | Pexp_field(e,l) -> node "field" [exp e;id l]
 | Pexp_setfield(e,l,v) -> node "setfield" [exp e;id l;exp v]
 | Pexp_assert e -> node "assert" [exp e]
 | Pexp_record(fs,b) -> node "record" [arr(List.map(fun(l,e)->arr[id l;exp e]) fs);(match b with None->"null"|Some e->exp e)]
 | Pexp_letmodule(s,m,e) -> node "letmodule" [str(Option.get s.txt);modexp m;exp e]
 | Pexp_lazy e -> node "lazy" [exp e]
 | _ -> unsupported e.pexp_loc "expression"
and case c = arr [pat c.pc_lhs;(match c.pc_guard with None->"null"|Some e->exp e);exp c.pc_rhs]
and binding b = arr [pat b.pvb_pat;exp b.pvb_expr]
and modexp m = match m.pmod_desc with
 | Pmod_structure xs -> node "struct" [arr(List.map item xs)]
 | Pmod_constraint(m,_) -> modexp m
 | Pmod_ident l -> node "moduleid" [id l]
 | Pmod_apply(f,a) -> node "moduleapply" [modexp f;modexp a]
 | Pmod_functor(Named(n,_),b) -> node "functor" [str(Option.get n.txt);modexp b]
 | _ -> unsupported m.pmod_loc "module expression"
and item i = match i.pstr_desc with
 | Pstr_value(r,bs) -> node "value" [str(if r=Recursive then "rec" else "nonrec");arr(List.map binding bs)]
 | Pstr_eval(e,_) -> node "eval" [exp e]
 | Pstr_type(_,ds) -> node "types" [arr(List.concat_map(fun d ->
     match d.ptype_kind with
     | Ptype_variant cs ->
         let records=List.filter_map(fun c->match c.pcd_args with
           | Pcstr_record fs -> Some(arr[str (d.ptype_name.txt^"_"^c.pcd_name.txt);arr(List.map(fun f->arr[str f.pld_name.txt;str(if f.pld_mutable=Mutable then "mutable" else "immutable")]) fs)])
           | _ -> None) cs in
         records @ [arr[str d.ptype_name.txt;arr(List.map(fun c->
         let n=match c.pcd_args with Pcstr_tuple xs->List.length xs | Pcstr_record _->1 in
         arr[str c.pcd_name.txt;string_of_int n]) cs)]]
     | Ptype_abstract -> [arr[str d.ptype_name.txt;"[]"]]
     | Ptype_record fs -> [arr[str d.ptype_name.txt;arr(List.map(fun f->arr[str f.pld_name.txt;str(if f.pld_mutable=Mutable then "mutable" else "immutable")]) fs)]]
     | _ -> unsupported d.ptype_loc "type") ds)]
 | Pstr_exception x -> let c=x.ptyexn_constructor in
   let n=match c.pext_kind with Pext_decl(_,Pcstr_tuple xs,_)->List.length xs|_->0 in
   node "exception" [str c.pext_name.txt;string_of_int n]
 | Pstr_open o -> node "open" [modexp o.popen_expr]
 | Pstr_module m -> node "module" [str(Option.get m.pmb_name.txt);modexp m.pmb_expr]
 | Pstr_modtype _ -> node "modtype" []
 | Pstr_include i -> node "include" [modexp i.pincl_mod]
 | _ -> unsupported i.pstr_loc "structure item"
let parse path : structure =
 let ch = open_in_bin path in
 let magic = really_input_string ch (String.length Config.ast_impl_magic_number) in
 if magic <> Config.ast_impl_magic_number then failwith "wrong OCaml AST version";
 let (_ : string) = input_value ch in
 let ast = input_value ch in close_in ch; ast
let () =
 let mode=Sys.argv.(1) and path=Sys.argv.(2) in
 let ast=if mode="source-json" then (
   let ch=open_in path in let lexbuf=Lexing.from_channel ch in
   Location.init lexbuf path; let ast=Parse.implementation lexbuf in close_in ch; ast
 ) else parse path in
 if mode="json" || mode="source-json" then print_endline(arr(List.map item ast))
 else if mode="instrument" then (
  let module_name=Sys.argv.(3) in
  let mapper = { Ast_mapper.default_mapper with expr=(fun self e ->
   let e=Ast_mapper.default_mapper.expr self e in
   match e.pexp_desc with
   | Pexp_ident ({txt=Longident.Lident "o";_} as l) -> {e with pexp_desc=Pexp_ident {l with txt=Longident.Lident "offline_compose"}}
   | Pexp_ident ({txt=Longident.Lident "upto";_} as l) -> {e with pexp_desc=Pexp_ident {l with txt=Longident.Lident "offline_upto"}}
   | Pexp_apply({pexp_desc=Pexp_ident {txt=Longident.Lident ("parse_term"|"parse_type" as f);_};_},[(Nolabel,{pexp_desc=Pexp_constant(Pconst_string(s,_,_));_})]) ->
      let key=Printf.sprintf "%s:%d" module_name e.pexp_loc.loc_start.pos_cnum in
      let c s = Ast_helper.Exp.constant(Pconst_string(s,Location.none,None)) in
      Ast_helper.Exp.apply (Ast_helper.Exp.ident(Location.mknoloc(Longident.Lident("record_"^f)))) [(Nolabel,c key);(Nolabel,c s)]
   | _ -> e) } in
  let ast=mapper.structure mapper ast in
  List.iter(fun i -> match i.pstr_desc with
   | Pstr_eval(e,_) -> Format.printf "%a;;@." Pprintast.expression e
   | _ -> Format.printf "%a;;@." Pprintast.structure [i]) ast
 ) else failwith "expected json or instrument"

(* SPDX-License-Identifier: 0BSD *)

signature RHOMBUS_CODE_TARGET =
sig
  val target: string
end;

structure Rhombus_Code_Target : RHOMBUS_CODE_TARGET =
struct

open Basic_Code_Symbol;
open Basic_Code_Thingol;
open Code_Printer;

infixr 5 @@;
infixr 5 @|;

val target = "Rhombus";

fun print_rhombus_string s =
  quote (translate_string (fn c =>
    if c = "\\" then "\\\\"
    else if c = "\"" then "\\\""
    else if c = "\n" then "\\n"
    else if c = "\r" then "\\r"
    else if c = "\t" then "\\t"
    else if Symbol.is_ascii c then c
    else error "non-ASCII symbol in Rhombus string literal") s);

fun suite head body = Pretty.block
  [head, Pretty.str " \194\171", Pretty.fbrk, body, Pretty.fbrk,
   Pretty.str "\194\187"];

fun vertical ps = Pretty.blk (0, Pretty.fbreaks ps);
fun branch_suite head body = vertical [head, body];

datatype mapped_constructor =
    Mapped_Call of {expression: string, pattern: string}
  | Mapped_Fixed of {expression: string, pattern: string}
  | Mapped_Identity
  | Mapped_User_Name;

fun mapped_constructor_of c =
  (case Long_Name.base_name c of
    "NFun" =>
      SOME (Mapped_Fixed {expression = "abi.name_fun", pattern = "#'fun"})
  | "NBool" =>
      SOME (Mapped_Fixed {expression = "abi.name_bool", pattern = "#'bool"})
  | "NEq" =>
      SOME (Mapped_Fixed {expression = "abi.name_eq", pattern = "#'eq"})
  | "NAlpha" =>
      SOME (Mapped_Fixed {expression = "abi.name_alpha", pattern = "#'a"})
  | "NRepVar" =>
      SOME (Mapped_Fixed {expression = "abi.name_rep", pattern = "#'r"})
  | "NUser" => SOME Mapped_User_Name
  | "TyVar" =>
      SOME (Mapped_Call {expression = "abi.raw.tyvar", pattern = "abi.TyVar"})
  | "TyApp" =>
      SOME (Mapped_Call {expression = "abi.raw.tyapp", pattern = "abi.TyApp"})
  | "FVar" =>
      SOME (Mapped_Call {expression = "abi.raw.fvar", pattern = "abi.FVar"})
  | "BVar" =>
      SOME (Mapped_Call {expression = "abi.raw.bvar", pattern = "abi.BVar"})
  | "Const" =>
      SOME (Mapped_Call {expression = "abi.raw.const", pattern = "abi.Const"})
  | "Comb" =>
      SOME (Mapped_Call {expression = "abi.raw.comb", pattern = "abi.Comb"})
  | "Abs" =>
      SOME (Mapped_Call {expression = "abi.raw.abs", pattern = "abi.Abs"})
  | "Nil" =>
      SOME (Mapped_Fixed {expression = "abi.list_nil()", pattern = "[]"})
  | "Cons" =>
      SOME (Mapped_Call {expression = "abi.list_cons", pattern = "List.cons"})
  | "Nat" => SOME Mapped_Identity
  | _ => NONE);
fun mapped_type tyco = member (op =)
  ["Rhombus_HOL_Syntax.hname", "Rhombus_HOL_Syntax.htype",
   "Rhombus_HOL_Syntax.hterm", "List.list", "Nat.nat"] tyco;

fun rhombus_program_of_program ctxt module_name reserved identifiers exports program =
  let
    fun namify upper base nsp =
      Name.variant (Name.enforce_case upper base) nsp;
    fun namify_stmt (Code_Thingol.Fun (_, SOME _)) = namify false
      | namify_stmt (Code_Thingol.Fun _) = namify false
      | namify_stmt (Code_Thingol.Datatype _) = namify true
      | namify_stmt (Code_Thingol.Datatypecons _) = namify true
      | namify_stmt (Code_Thingol.Class _) = namify true
      | namify_stmt (Code_Thingol.Classrel _) = namify false
      | namify_stmt (Code_Thingol.Classparam _) = namify false
      | namify_stmt (Code_Thingol.Classinst _) = namify false
      | namify_stmt Code_Thingol.NoStmt =
          error "Rhombus target: unsupported empty statement";
    fun modify_stmt (Code_Thingol.Fun (_, SOME _)) = NONE
      | modify_stmt (stmt as Code_Thingol.Fun _) = SOME stmt
      | modify_stmt (stmt as Code_Thingol.Datatype _) = SOME stmt
      | modify_stmt (Code_Thingol.Datatypecons _) = NONE
      | modify_stmt (stmt as Code_Thingol.Class _) = SOME stmt
      | modify_stmt (Code_Thingol.Classrel _) = NONE
      | modify_stmt (Code_Thingol.Classparam _) = NONE
      | modify_stmt (stmt as Code_Thingol.Classinst _) = SOME stmt
      | modify_stmt Code_Thingol.NoStmt =
          error "Rhombus target: unsupported empty statement";
  in
    Code_Namespace.flat_program ctxt
      {module_prefix = "", module_name = module_name, reserved = reserved,
       identifiers = identifiers, empty_nsp = reserved,
       namify_stmt = namify_stmt, modify_stmt = modify_stmt}
      exports program
  end;

fun print_rhombus_program ctxt reserved const_syntax program deresolve =
  let
    val base_vars = make_vars reserved;

    fun dict_name var index = "dict_" ^ var ^ "_" ^ string_of_int index;
    fun dict_names vs = maps (fn (var, sort) =>
      map_index (fn (index, _) => dict_name var index) sort) vs;
    fun apply p arg = Pretty.block [Pretty.enclose "(" ")" [p],
      Pretty.enclose "(" ")" [arg]];
    fun apply_all p args = fold (fn arg => fn f => apply f arg) args p;
    fun comma ps = Pretty.unbreakable (Pretty.enum "," "" "" ps);
    fun error_expr message = concat [Pretty.str "error",
      Pretty.enclose "(" ")" [Pretty.str (print_rhombus_string message)]];

    fun print_dict vars (Dict (classrels, plain)) =
          fold (fn classrel => fn p => Pretty.block [Pretty.enclose "(" ")" [p],
            Pretty.str ".", (Pretty.str o deresolve o Class_Relation) classrel])
            classrels (print_plain_dict vars plain)
    and print_plain_dict vars (Dict_Const (inst, dictss)) =
          let
            val p = (Pretty.str o deresolve o Class_Instance) inst;
            val args = maps (map (print_dict vars) o snd) dictss;
          in if null args then Pretty.block [p, Pretty.str "()"] else apply_all p args end
      | print_plain_dict vars (Dict_Var {var, index, ...}) =
          (Pretty.str o lookup_var vars) (dict_name var index);

    fun print_term is_pat some_thm vars fxy (IConst const) =
          print_app is_pat some_thm vars fxy (const, [])
      | print_term _ _ _ _ (IVar NONE) = Pretty.str "_"
      | print_term _ _ vars _ (IVar (SOME v)) =
          (Pretty.str o lookup_var vars) v
      | print_term is_pat some_thm vars fxy (t as t1 `$ t2) =
          (case Code_Thingol.unfold_const_app t of
            SOME app => print_app is_pat some_thm vars fxy app
          | NONE => apply (print_term false some_thm vars BR t1)
              (print_term false some_thm vars NOBR t2))
      | print_term _ some_thm vars _ (t as _ `|=> _) =
          let
            val (binds, body) = Code_Thingol.unfold_pat_abs t;
            fun add_bind (pat, _) (ps, vars') =
              let val (p, vars'') = print_bind some_thm pat vars'
              in (ps @ [p], vars'') end;
            val (ps, vars') = fold add_bind binds ([], vars);
            fun abstract p body' = suite
              (concat [Pretty.str "fun", Pretty.enclose "(" ")" [p], Pretty.str ":"])
              body';
          in Pretty.enclose "(" ")"
            [fold_rev abstract ps (print_term false some_thm vars' NOBR body)] end
      | print_term _ some_thm vars _ (ICase case_expr) =
          (case Code_Thingol.unfold_const_app (#primitive case_expr) of
            SOME (app as ({sym = Constant c, ...}, _)) =>
              if is_some (const_syntax c) then print_app false some_thm vars NOBR app
              else print_case some_thm vars case_expr
          | _ => print_case some_thm vars case_expr)
    and print_app_regular is_pat some_thm vars
          (const as {sym, dictss, dom, ...}, ts) =
          let
            val name = (Pretty.str o deresolve) sym;
            val dictionaries = maps (map (print_dict vars)) dictss;
            fun regular_constructor () =
              Pretty.block [name, Pretty.enclose "(" ")"
                [comma (map (print_term is_pat some_thm vars NOBR) ts)]];
            fun mapped_constructor c =
              (case mapped_constructor_of c of
                NONE => regular_constructor ()
              | SOME (Mapped_Call {expression, pattern}) =>
                  Pretty.block [Pretty.str (if is_pat then pattern else expression),
                    Pretty.enclose "(" ")"
                      [comma (map (print_term is_pat some_thm vars NOBR) ts)]]
              | SOME (Mapped_Fixed {expression, pattern}) =>
                  if null ts then Pretty.str (if is_pat then pattern else expression)
                  else error ("Rhombus target: bad mapped nullary constructor " ^ c)
              | SOME Mapped_Identity =>
                  (case ts of
                    [t] => print_term is_pat some_thm vars NOBR t
                  | _ => error ("Rhombus target: bad mapped identity constructor " ^ c))
              | SOME Mapped_User_Name =>
                  if is_pat then Pretty.str "_"
                  else error "Rhombus target: NUser construction is unreachable");
          in
            if Code_Thingol.is_constr program sym then
              let
                val wanted = length dom;
                val missing = wanted - length ts;
              in
                if missing < 0 then
                  error ("Rhombus target: over-applied constructor " ^
                    Code_Symbol.quote ctxt sym)
                else if missing = 0 then
                  (case sym of
                    Constant c => mapped_constructor c
                  | _ => regular_constructor ())
                else
                  let
                    val raw = Name.invent (snd vars) "arg" missing;
                    val vars' = intro_vars raw vars;
                    val fresh = map (IVar o SOME) raw;
                    val body = print_app_regular false some_thm vars'
                      (const, ts @ fresh);
                    fun abstract v body' = suite
                      (Pretty.str ("fun (" ^ lookup_var vars' v ^ "):")) body';
                  in Pretty.enclose "(" ")" [fold_rev abstract raw body] end
              end
            else
              let
                val p = apply_all name (dictionaries @
                  map (print_term false some_thm vars NOBR) ts);
              in if null dictionaries andalso null ts andalso null dom
                then Pretty.block [name, Pretty.str "()"] else p
              end
          end
    and print_app is_pat some_thm vars fxy
          (app as (const as {sym, dom, ...}, ts)) =
          (case sym of
            Constant c => (case const_syntax c of
              NONE => print_app_regular is_pat some_thm vars app
            | SOME (_, Plain_printer s) =>
                apply_all (Pretty.str s)
                  (map (print_term false some_thm vars NOBR) ts)
            | SOME (wanted, Complex_printer print) =>
                let
                  val ((vs_tys, (ts1, rty)), ts2) =
                    Code_Thingol.satisfied_application wanted app;
                  fun printed fxy' = print (print_term false some_thm) some_thm vars fxy'
                    (ts1 ~~ take wanted dom);
                in
                  if null vs_tys then apply_all (printed fxy)
                    (map (print_term false some_thm vars NOBR) ts2)
                  else print_term false some_thm vars fxy
                    (vs_tys `|==> (IConst const `$$ ts1, rty))
                end)
          | _ => print_app_regular is_pat some_thm vars app)
    and print_bind some_thm pat vars =
      gen_print_bind (print_term true) some_thm NOBR pat vars
    and print_case _ _ {clauses = [], ...} = error_expr "empty case"
      | print_case some_thm vars {term, clauses, ...} =
          let
            fun print_clause (pat, body) =
              let
                val (p, vars') = print_bind some_thm pat vars;
              in suite (concat [Pretty.str "|", p, Pretty.str ":"])
                (print_term false some_thm vars' NOBR body) end;
            val match = branch_suite (concat [Pretty.str "match",
              print_term false some_thm vars NOBR term])
              (vertical (map print_clause clauses));
          in Pretty.enclose "(" ")" [suite (Pretty.str "block:") match] end;

    fun curried_definition name params body =
      (case params of
        [] => suite (Pretty.str ("fun " ^ name ^ "():")) body
      | p :: ps => suite
          (Pretty.str ("fun " ^ name ^ "(" ^ p ^ "):"))
          (fold_rev (fn q => fn body' => suite
            (Pretty.str ("fun (" ^ q ^ "):")) body') ps body));

    fun print_function const (vs, ty) raw_eqs =
      let
        val eqs = filter (snd o snd) raw_eqs;
        val raw_dicts = dict_names vs;
        val vars0 = intro_vars raw_dicts base_vars;
        val arity = (case eqs of
            ((ts, _), _) :: _ => length ts
          | [] => (length o fst o Code_Thingol.unfold_fun) ty);
        val raw_args = Name.invent (snd vars0) "arg" arity;
        val vars1 = intro_vars raw_args vars0;
        val params = map (lookup_var vars1) (raw_dicts @ raw_args);
        fun catchall ((ts, _), _) = forall Code_Thingol.is_IVar ts;
        fun print_eq (((ts, body), (some_thm, _))) =
          let
            val (patterns, vars') = fold_map
              (fn pat => print_bind some_thm pat) ts vars0;
          in suite (concat [Pretty.str "|",
              Pretty.enclose "[" "]" [comma patterns], Pretty.str ":"])
            (print_term false some_thm vars' NOBR body) end;
        val body = if null eqs then error_expr ("unimplemented function " ^ const)
          else if arity = 0 then
            print_term false (#1 (snd (hd eqs))) vars0 NOBR (#2 (fst (hd eqs)))
          else branch_suite (concat [Pretty.str "match",
              Pretty.enclose "[" "]" [comma (map (Pretty.str o lookup_var vars1) raw_args)]])
            (vertical (map print_eq eqs @
              (if exists catchall eqs then [] else
                [suite (Pretty.str "| ~else:")
                  (error_expr ("non-exhaustive match in " ^ const))])));
      in curried_definition (deresolve (Constant const)) params body end;

    fun print_datatype tyco cos =
      let
        val base = deresolve (Type_Constructor tyco);
        fun print_constructor ((co, _), tys) =
          let val fields = Name.invent Name.context "field" (length tys)
          in Pretty.chunks [
            suite (Pretty.str ("class " ^ deresolve (Constant co) ^
              "(" ^ commas fields ^ "):"))
              (Pretty.str ("extends " ^ base))]
          end;
      in Pretty.chunks
        (suite (Pretty.str ("class " ^ base ^ "():")) (Pretty.str "nonfinal")
          :: map print_constructor cos)
      end;

    fun print_class class (_, (classrels, classparams)) =
      let
        val class_name = deresolve (Type_Class class);
        val fields = map (deresolve o Class_Relation) classrels @
          map (deresolve o Constant o fst) classparams;
        fun projection (param, _) =
          let val p = deresolve (Constant param)
          in suite (Pretty.str ("fun " ^ p ^ "(dictionary):"))
            (Pretty.str ("dictionary." ^ p)) end;
      in Pretty.chunks
        (Pretty.str ("class " ^ class_name ^ "(" ^ commas fields ^ ")")
          :: map projection classparams)
      end;

    fun print_instance inst ({class, tyco, vs, superinsts, inst_params, ...}:
          {class: string, tyco: string, vs: (vname * sort) list,
           superinsts: (class * (itype * dict list) list) list,
           inst_params: ((string * (const * int)) * (thm * bool)) list,
           superinst_params: ((string * (const * int)) * (thm * bool)) list}) =
      let
        val raw_dicts = dict_names vs;
        val vars = intro_vars raw_dicts base_vars;
        val params = map (lookup_var vars) raw_dicts;
        fun super_value (superclass, dictss) =
          print_dict vars (Dict ([], Dict_Const ((tyco, superclass), dictss)));
        fun param_value ((_, (c, _)), (thm, _)) =
          print_app false (SOME thm) vars NOBR (c, []);
        val values = map super_value superinsts @ map param_value inst_params;
        val body = Pretty.block [(Pretty.str o deresolve o Type_Class) class,
          Pretty.enclose "(" ")" [comma values]];
      in curried_definition (deresolve (Class_Instance inst)) params body end;

    fun print_stmt (Constant const, Code_Thingol.Fun (((vs, ty), eqs), _)) =
          print_function const (vs, ty) eqs
      | print_stmt (Type_Constructor tyco, Code_Thingol.Datatype (_, cos)) =
          print_datatype tyco cos
      | print_stmt (Type_Class class, Code_Thingol.Class stmt) =
          print_class class stmt
      | print_stmt (Class_Instance inst, Code_Thingol.Classinst stmt) =
          print_instance inst stmt
      | print_stmt (sym, stmt) =
          error ("Rhombus target: unsupported statement " ^
            Code_Symbol.quote ctxt sym ^ " (" ^
            (case stmt of
              Code_Thingol.NoStmt => "NoStmt"
            | Code_Thingol.Fun _ => "Fun"
            | Code_Thingol.Datatype _ => "Datatype"
            | Code_Thingol.Datatypecons _ => "Datatypecons"
            | Code_Thingol.Class _ => "Class"
            | Code_Thingol.Classrel _ => "Classrel"
            | Code_Thingol.Classparam _ => "Classparam"
            | Code_Thingol.Classinst _ => "Classinst") ^ ")");
  in print_stmt end;

fun serialize ctxt {module_name, reserved_syms, identifiers, includes,
    class_syntax = _, tyco_syntax = _, const_syntax} program exports =
  let
    val reserved = fold (insert (op =) o fst) includes reserved_syms;
    val {deresolver, flat_program} = rhombus_program_of_program ctxt module_name
      (Name.make_context reserved) identifiers exports program;
    val modules = (flat o rev o Graph.strong_conn) flat_program;
    val module = (case modules of
        [name] => name
      | [] => error "Rhombus target: empty generated program"
      | _ => error "Rhombus target: expected one flat generated module");
    val (gr, imports) = Graph.get_node flat_program module;
    val _ = if null imports then ()
      else error "Rhombus target: unexpected imports in singleton module";
    val print_stmt = print_rhombus_program ctxt reserved const_syntax program
      (deresolver module);
    fun emit (sym as Type_Constructor tyco) =
          if mapped_type tyco then NONE
          else (case Code_Symbol.Graph.get_node gr sym of
            (_, NONE) => NONE
          | (_, SOME (_, stmt)) => SOME (markup_stmt sym (print_stmt (sym, stmt))))
      | emit sym = (case Code_Symbol.Graph.get_node gr sym of
          (_, NONE) => NONE
        | (_, SOME (_, stmt)) => SOME (markup_stmt sym (print_stmt (sym, stmt))));
    val body = map_filter emit ((flat o rev o Code_Symbol.Graph.strong_conn) gr);
    val export_names = distinct (op =) (map (deresolver module) exports);
    val export_block = suite (Pretty.str "export:")
      (Pretty.chunks (map Pretty.str export_names));
    val generated_header = vertical
      [Pretty.str "// GENERATED FILE - DO NOT EDIT.",
       Pretty.str "// Source: isabelle-hol-kernel/Rhombus_HOL_Code.thy",
       Pretty.str "// Regenerate: isabelle-hol-kernel/export-kernel.sh",
       Pretty.str "// Kernel ABI: 1",
       Pretty.str "// SPDX-License-Identifier: 0BSD AND BSD-2-Clause"];
     val abi_import = vertical
       [Pretty.str "import:",
        Pretty.str "  rhombus/hol/kernel_abi as abi",
        Pretty.str "",
        Pretty.str "unless abi.kernel_abi_version == 1",
        Pretty.str "| error(\"generated kernel ABI mismatch\")"];
     val p = Pretty.chunks2
      ([Pretty.str "#lang rhombus", generated_header, abi_import, export_block] @
        map snd includes @ body);  in (Code_Target.Singleton ("rhm", p), try (deresolver "")) end;

val serializer : Code_Target.serializer =
  Code_Target.parse_args (Scan.succeed ()) #> K serialize;

val literals = Literals {
  literal_string = print_rhombus_string,
  literal_numeral = signed_string_of_int,
  literal_list = Pretty.enum "," "[" "]",
  infix_cons = (5, "List.cons")
};

fun print_unary operator print _ [(term, _)] =
      Pretty.enclose "(" ")" [Pretty.block
        [Pretty.str operator, print NOBR term]]
  | print_unary operator _ _ _ =
      error ("Rhombus target: bad arity for " ^ quote operator);

fun print_infix operator print _ [(left, _), (right, _)] =
      Pretty.enclose "(" ")" [Pretty.block
        [print NOBR left, Pretty.str (" " ^ operator ^ " "), print NOBR right]]
  | print_infix operator _ _ _ =
      error ("Rhombus target: bad arity for " ^ quote operator);

fun print_if print _ [(test, _), (yes, _), (no, _)] =
      Pretty.enclose "(" ")" [Pretty.block
        [Pretty.str "if ", Pretty.enclose "(" ")" [print NOBR test],
         Pretty.str " | ", Pretty.enclose "(" ")" [print NOBR yes],
         Pretty.str " | ", Pretty.enclose "(" ")" [print NOBR no]]]
  | print_if _ _ _ = error "Rhombus target: bad arity for conditional";

fun print_implies print _ [(left, _), (right, _)] =
      Pretty.enclose "(" ")" [Pretty.block
        [Pretty.str "if ", print NOBR left, Pretty.str " | ",
         print NOBR right, Pretty.str " | #true"]]
  | print_implies _ _ _ = error "Rhombus target: bad arity for implication";

fun fun_syntax _ _ [_ , _] = Pretty.str "Function"
  | fun_syntax _ _ _ = error "Rhombus target: malformed function type";

val reserved = [
  "#lang", "class", "nonfinal", "extends", "fun", "def", "match",
  "export", "import", "namespace", "interface", "private", "protected",
  "let", "if", "cond", "else", "when", "unless", "for", "while",
  "recur", "values", "error", "Boolean", "Int", "String", "List",
  "Map", "Set", "Pair", "Void", "Function", "dictionary",
  "rhombus_fun_upd", "RhombusFunUpdateState", "RhombusFunUpdateValue",
  "rhombus_fun_update_states", "RhombusMemoValue",
  "rhombus_binary_memos", "rhombus_ternary_memos",
  "rhombus_memoized_binary", "rhombus_memoized_ternary"
];

val _ = Theory.setup
  (Code_Target.add_language
    (target, {serializer = serializer, literals = literals,
      check = {env_var = "",
        make_destination = fn p => p + Path.explode "ROOT.rhm",
        run_command = Code_Target.run_command_bash (fn _ => "raco make ROOT.rhm")},
      evaluation_args = []})
  #> Code_Target.set_printings (Type_Constructor ("fun",
      [(target, SOME (2, fun_syntax))]))
  #> Code_Target.set_printings (Type_Constructor (\<^type_name>\<open>bool\<close>,
      [(target, SOME (0, (K o K o K) (Pretty.str "Boolean")))]))
  #> Code_Target.set_printings (Constant (\<^const_name>\<open>True\<close>,
      [(target, SOME (Code_Printer.plain_const_syntax "#true"))]))
  #> Code_Target.set_printings (Constant (\<^const_name>\<open>False\<close>,
      [(target, SOME (Code_Printer.plain_const_syntax "#false"))]))
  #> Code_Target.set_printings (Constant (\<^const_name>\<open>If\<close>,
      [(target, SOME (Code_Printer.simple_const_syntax (3, print_if)))]))
  #> Code_Target.set_printings (Constant (\<^const_name>\<open>Not\<close>,
      [(target, SOME (Code_Printer.simple_const_syntax (1, print_unary "!")))]))
  #> Code_Target.set_printings (Constant (\<^const_name>\<open>conj\<close>,
      [(target, SOME (Code_Printer.simple_const_syntax (2, print_infix "&&")))]))
  #> Code_Target.set_printings (Constant (\<^const_name>\<open>disj\<close>,
      [(target, SOME (Code_Printer.simple_const_syntax (2, print_infix "||")))]))
  #> Code_Target.set_printings (Constant (\<^const_name>\<open>implies\<close>,
      [(target, SOME (Code_Printer.simple_const_syntax (2, print_implies)))]))
  #> fold (Code_Target.add_reserved target) reserved);

end;

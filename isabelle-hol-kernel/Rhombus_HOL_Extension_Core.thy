(* SPDX-License-Identifier: 0BSD AND BSD-2-Clause AND BSD-3-Clause *)
(* Conservatively covered by HOL Light and HOL4 notices; see THIRD_PARTY_NOTICES. *)

theory Rhombus_HOL_Extension_Core
  imports Rhombus_HOL_Soundness
begin

section \<open>Executable theory extensions\<close>

text \<open>Rhombus correspondence: kernel.rhm theory extension operations.
The explicit natural supplies the fresh stamp identifier.\<close>

definition extend_theory ::
  "nat \<Rightarrow> htheory \<Rightarrow> (hname \<Rightarrow> nat option) \<Rightarrow> (hname \<Rightarrow> htype option) \<Rightarrow>
    hthm list \<Rightarrow> (hname \<Rightarrow> hthm option) \<Rightarrow> htheory" where
  "extend_theory fresh thy ts cs axs ds =
    \<lparr>tyops = ts, const_tab = cs, axiom_list = axs, def_tab = ds,
      thy_stamp = next_stamp fresh (thy_stamp thy)\<rparr>"

definition new_type :: "nat \<Rightarrow> htheory \<Rightarrow> hname \<Rightarrow> nat \<Rightarrow> htheory option" where
  "new_type fresh thy n arity =
    (if tyops thy n \<noteq> None then None
     else Some (extend_theory fresh thy ((tyops thy)(n := Some arity))
       (const_tab thy) (axiom_list thy) (def_tab thy)))"

definition new_constant ::
  "nat \<Rightarrow> htheory \<Rightarrow> hname \<Rightarrow> htype \<Rightarrow> htheory option" where
  "new_constant fresh thy n ty =
    (if const_tab thy n \<noteq> None \<or> \<not> check_type thy ty then None
     else Some (extend_theory fresh thy (tyops thy)
       ((const_tab thy)(n := Some ty)) (axiom_list thy) (def_tab thy)))"

definition new_axiom ::
  "nat \<Rightarrow> htheory \<Rightarrow> hterm \<Rightarrow> (htheory \<times> hthm) option" where
  "new_axiom fresh thy p =
    (if \<not> check_prop thy p then None
     else let st = next_stamp fresh (thy_stamp thy);
              th = \<lparr>hyps = [], concl = p, thm_stamp = st\<rparr>;
              thy' = \<lparr>tyops = tyops thy, const_tab = const_tab thy,
                axiom_list = th # axiom_list thy, def_tab = def_tab thy,
                thy_stamp = st\<rparr>
          in Some (thy', th))"

lemma new_type_extract:
  "new_type fresh thy n arity = Some thy' \<Longrightarrow>
    tyops thy n = None \<and>
    thy' = extend_theory fresh thy ((tyops thy)(n := Some arity))
      (const_tab thy) (axiom_list thy) (def_tab thy)"
  by (auto simp: new_type_def split: if_splits)

lemma new_constant_extract:
  "new_constant fresh thy n ty = Some thy' \<Longrightarrow>
    const_tab thy n = None \<and> check_type thy ty \<and>
    thy' = extend_theory fresh thy (tyops thy) ((const_tab thy)(n := Some ty))
      (axiom_list thy) (def_tab thy)"
  by (auto simp: new_constant_def split: if_splits)

lemma new_axiom_extract:
  assumes "new_axiom fresh thy p = Some (thy', th)"
  shows "check_prop thy p \<and>
    th = \<lparr>hyps = [], concl = p,
      thm_stamp = next_stamp fresh (thy_stamp thy)\<rparr> \<and>
    thy' = \<lparr>tyops = tyops thy, const_tab = const_tab thy,
      axiom_list = th # axiom_list thy, def_tab = def_tab thy,
      thy_stamp = next_stamp fresh (thy_stamp thy)\<rparr>"
  using assms by (auto simp: new_axiom_def Let_def split: if_splits)

definition new_basic_definition ::
  "nat \<Rightarrow> htheory \<Rightarrow> hterm \<Rightarrow> (htheory \<times> hthm) option" where
  "new_basic_definition fresh thy tm =
    (case dest_eq tm of
       None \<Rightarrow> None
     | Some (lhs, rhs) \<Rightarrow>
         (case lhs of
            FVar n ty \<Rightarrow>
              if const_tab thy n \<noteq> None \<or> \<not> check_term thy rhs \<or>
                 free_vars rhs \<noteq> [] \<or> type_of rhs \<noteq> Some ty \<or>
                 \<not> set (term_type_vars rhs) \<subseteq> set (type_vars ty)
              then None
              else let st = next_stamp fresh (thy_stamp thy);
                       c = Const n ty;
                       dth = \<lparr>hyps = [], concl = eq_term ty c rhs,
                         thm_stamp = st\<rparr>;
                       thy' = \<lparr>tyops = tyops thy,
                         const_tab = (const_tab thy)(n := Some ty),
                         axiom_list = axiom_list thy,
                         def_tab = (def_tab thy)(n := Some dth),
                         thy_stamp = st\<rparr>
                   in if wf_thm thy' dth then Some (thy', dth) else None
          | _ \<Rightarrow> None))"

lemma new_basic_definition_extract:
  assumes run: "new_basic_definition fresh thy tm = Some (thy', dth)"
  obtains n ty rhs where
    "dest_eq tm = Some (FVar n ty, rhs)"
    "const_tab thy n = None" "check_term thy rhs" "free_vars rhs = []"
    "type_of rhs = Some ty"
    "set (term_type_vars rhs) \<subseteq> set (type_vars ty)"
    "dth = \<lparr>hyps = [], concl = eq_term ty (Const n ty) rhs,
      thm_stamp = next_stamp fresh (thy_stamp thy)\<rparr>"
    "thy' = \<lparr>tyops = tyops thy, const_tab = (const_tab thy)(n := Some ty),
      axiom_list = axiom_list thy, def_tab = (def_tab thy)(n := Some dth),
      thy_stamp = next_stamp fresh (thy_stamp thy)\<rparr>"
    "wf_thm thy' dth"
  using run that
  by (auto simp: new_basic_definition_def Let_def
      split: option.splits prod.splits hterm.splits if_splits)

definition new_basic_type_definition ::
  "nat \<Rightarrow> htheory \<Rightarrow> hname \<Rightarrow> hname \<Rightarrow> hname \<Rightarrow> hthm \<Rightarrow>
    (htheory \<times> hthm \<times> hthm) option" where
  "new_basic_type_definition fresh thy tyname absname repname wit =
    (if \<not> wf_thm thy wit \<or> hyps wit \<noteq> [] \<or>
        tyops thy tyname \<noteq> None \<or> const_tab thy absname \<noteq> None \<or>
        const_tab thy repname \<noteq> None \<or> absname = repname
     then None
     else case concl wit of
       Comb pred witness \<Rightarrow>
         (case type_of witness of
            None \<Rightarrow> None
          | Some rty \<Rightarrow>
              if free_vars pred \<noteq> [] \<or>
                 \<not> set (type_vars rty) \<subseteq> set (term_type_vars pred)
              then None
              else let tvs = term_type_vars pred;
                       aty = TyApp tyname (map TyVar tvs);
                       abst = Const absname (mk_fun rty aty);
                       rept = Const repname (mk_fun aty rty);
                       a = FVar NAlpha aty;
                       r = FVar NRepVar rty;
                       st = next_stamp fresh (thy_stamp thy);
                       th1 = \<lparr>hyps = [],
                         concl = eq_term aty (Comb abst (Comb rept a)) a,
                         thm_stamp = st\<rparr>;
                       th2 = \<lparr>hyps = [],
                         concl = eq_term bool_ty (Comb pred r)
                           (eq_term rty (Comb rept (Comb abst r)) r),
                         thm_stamp = st\<rparr>;
                       thy' = \<lparr>tyops = (tyops thy)(tyname := Some (length tvs)),
                         const_tab = (const_tab thy)
                           (absname := Some (mk_fun rty aty),
                            repname := Some (mk_fun aty rty)),
                         axiom_list = axiom_list thy, def_tab = def_tab thy,
                         thy_stamp = st\<rparr>
                   in if wf_thm thy' th1 \<and> wf_thm thy' th2
                      then Some (thy', th1, th2) else None)
     | _ \<Rightarrow> None)"

lemma new_basic_type_definition_extract:
  assumes run: "new_basic_type_definition fresh thy tn an rn wit =
    Some (thy', th1, th2)"
  shows "wf_thm thy wit \<and> hyps wit = [] \<and> tyops thy tn = None \<and>
    const_tab thy an = None \<and> const_tab thy rn = None \<and> an \<noteq> rn \<and>
    wf_thm thy' th1 \<and> wf_thm thy' th2 \<and>
    axiom_list thy' = axiom_list thy \<and> def_tab thy' = def_tab thy \<and>
    gen (thy_stamp thy') = Suc (gen (thy_stamp thy))"
  using run
  by (auto simp: new_basic_type_definition_def Let_def next_stamp_def
      split: hterm.splits option.splits if_splits)

lemma new_basic_type_definition_obtain:
  assumes run: "new_basic_type_definition fresh thy tn an rn wit =
      Some (thy', th1, th2)"
  obtains pred witness rty tvs aty where
    "wf_thm thy wit" "hyps wit = []"
    "tyops thy tn = None" "const_tab thy an = None"
    "const_tab thy rn = None" "an \<noteq> rn"
    "concl wit = Comb pred witness" "type_of witness = Some rty"
    "free_vars pred = []"
    "set (type_vars rty) \<subseteq> set (term_type_vars pred)"
    "tvs = term_type_vars pred" "aty = TyApp tn (map TyVar tvs)"
    "th1 = \<lparr>hyps = [],
      concl = eq_term aty
        (Comb (Const an (mk_fun rty aty))
          (Comb (Const rn (mk_fun aty rty)) (FVar NAlpha aty)))
        (FVar NAlpha aty),
      thm_stamp = next_stamp fresh (thy_stamp thy)\<rparr>"
    "th2 = \<lparr>hyps = [],
      concl = eq_term bool_ty (Comb pred (FVar NRepVar rty))
        (eq_term rty
          (Comb (Const rn (mk_fun aty rty))
            (Comb (Const an (mk_fun rty aty)) (FVar NRepVar rty)))
          (FVar NRepVar rty)),
      thm_stamp = next_stamp fresh (thy_stamp thy)\<rparr>"
    "thy' = \<lparr>tyops = (tyops thy)(tn := Some (length tvs)),
      const_tab = (const_tab thy)
        (an := Some (mk_fun rty aty), rn := Some (mk_fun aty rty)),
      axiom_list = axiom_list thy, def_tab = def_tab thy,
      thy_stamp = next_stamp fresh (thy_stamp thy)\<rparr>"
    "wf_thm thy' th1" "wf_thm thy' th2"
  using run that
  by (auto simp: new_basic_type_definition_def Let_def
      split: hterm.splits option.splits if_splits)
section \<open>Generation and declaration invariants\<close>

definition preserves_old_model_obligations ::
  "frame \<Rightarrow> htheory \<Rightarrow> htheory \<Rightarrow> bool" where
  "preserves_old_model_obligations F old new \<longleftrightarrow>
    frame_wf F \<and>
    (\<forall>\<rho>. type_valuation_ok \<rho> \<longrightarrow> const_interpretation_ok F new \<rho>) \<and>
    (\<forall>th\<in>set (axiom_list old). valid_sequent F new (hyps th) (concl th)) \<and>
    (\<forall>n th. def_tab old n = Some th \<longrightarrow>
      valid_sequent F new (hyps th) (concl th))"

lemma new_type_one_generation:
  "new_type fresh thy n arity = Some thy' \<Longrightarrow>
    gen (thy_stamp thy') = Suc (gen (thy_stamp thy))"
  by (auto simp: new_type_def extend_theory_def next_stamp_def split: if_splits)

lemma new_constant_one_generation:
  "new_constant fresh thy n ty = Some thy' \<Longrightarrow>
    gen (thy_stamp thy') = Suc (gen (thy_stamp thy))"
  by (auto simp: new_constant_def extend_theory_def next_stamp_def split: if_splits)

lemma new_axiom_one_generation:
  "new_axiom fresh thy p = Some (thy', th) \<Longrightarrow>
    gen (thy_stamp thy') = Suc (gen (thy_stamp thy))"
  by (auto simp: new_axiom_def Let_def next_stamp_def split: if_splits)

lemma new_basic_definition_one_generation:
  "new_basic_definition fresh thy tm = Some (thy', th) \<Longrightarrow>
    gen (thy_stamp thy') = Suc (gen (thy_stamp thy))"
  by (elim new_basic_definition_extract) (simp add: next_stamp_def)


end

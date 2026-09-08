theory Rhombus_HOL_Soundness
  imports Rhombus_HOL_Semantics
begin

section \<open>Well-formed equality sequents\<close>

lemma dest_eq_shape:
  assumes "dest_eq p = Some (l, r)"
  obtains eqty where "p = Comb (Comb (Const NEq eqty) l) r"
  using assms
  by (induction p rule: dest_eq.induct) auto

lemma check_prop_dest_eq:
  assumes thy_wf: "wf_theory thy" and prop_ok: "check_prop thy p"
    and dest: "dest_eq p = Some (l, r)"
  obtains ty where
    "p = eq_term ty l r"
    "check_term thy l" "type_of l = Some ty"
    "check_term thy r" "type_of r = Some ty"
proof -
  obtain eqty where shape: "p = Comb (Comb (Const NEq eqty) l) r"
    using dest_eq_shape[OF dest] .
  have const_checked: "check_open_term thy [] (Const NEq eqty)"
    using prop_ok shape by (auto simp: check_prop_def check_term_def)
  have match: "type_match (mk_fun (TyVar NAlpha)
      (mk_fun (TyVar NAlpha) bool_ty)) eqty (\<lambda>_. None) \<noteq> None"
    using const_checked thy_wf by (simp add: wf_theory_def)
  obtain ty where eqty: "eqty = mk_fun ty (mk_fun ty bool_ty)"
    using equality_match_shape[OF match] by blast
  have checks: "check_term thy l" "check_term thy r"
    using prop_ok shape by (auto simp: check_prop_def check_term_def)
  have inner_typed: "type_of (Comb (Const NEq eqty) l) \<noteq> None"
    using prop_ok shape by (auto simp: check_prop_def check_term_def)
  have l_type: "type_of l = Some ty"
    using inner_typed eqty
    by (auto simp: mk_fun_def split: option.splits if_splits)
  have outer_typed: "type_of (Comb (Comb (Const NEq eqty) l) r) \<noteq> None"
    using prop_ok shape by (auto simp: check_prop_def check_term_def)
  have r_type: "type_of r = Some ty"
    using outer_typed eqty l_type
    by (auto simp: mk_fun_def split: option.splits if_splits)
  have term_shape: "p = eq_term ty l r"
    using shape eqty by (simp add: eq_term_def eq_const_def)
  show thesis using that[OF term_shape checks(1) l_type checks(2) r_type] .
qed

lemma wf_thm_dest_eq:
  assumes thy_wf: "wf_theory thy" and th_wf: "wf_thm thy th"
    and dest: "dest_eq (concl th) = Some (l, r)"
  obtains ty where
    "concl th = eq_term ty l r"
    "check_term thy l" "type_of l = Some ty"
    "check_term thy r" "type_of r = Some ty"
proof -
  have prop_ok: "check_prop thy (concl th)"
    using th_wf by (simp add: wf_thm_def)
  show thesis using check_prop_dest_eq[OF thy_wf prop_ok dest] that .
qed

lemma eq_shape_parts:
  assumes "eq_shape thy hs l r st th"
  obtains ty where
    "type_of l = Some ty" "type_of r = Some ty"
    "th = \<lparr>hyps = hs, concl = eq_term ty l r, thm_stamp = st\<rparr>"
    "wf_thm thy th"
  using assms by (auto simp: eq_shape_def thm_shape_def)

section \<open>Primitive rule soundness\<close>

lemma models_frame: "models_theory F thy \<Longrightarrow> frame_wf F"
  by (simp add: models_theory_def)

lemma valid_equality_elim:
  assumes thy_wf: "wf_theory thy" and model: "models_theory F thy"
    and th_wf: "wf_thm thy th"
    and valid: "valid_sequent F thy (hyps th) (concl th)"
    and dest: "dest_eq (concl th) = Some (l, r)"
    and type_ok: "type_valuation_ok \<rho>"
    and const_ok: "const_interpretation_ok F thy \<rho>"
    and free_ok: "free_valuation_ok F \<rho> \<nu>"
    and hyps_ok: "\<forall>h\<in>set (hyps th). holds F \<rho> \<nu> h"
  shows "eval_term F \<rho> \<nu> [] l = eval_term F \<rho> \<nu> [] r"
proof -
  obtain ty where concl: "concl th = eq_term ty l r"
    and left: "check_term thy l" "type_of l = Some ty"
    and right: "check_term thy r" "type_of r = Some ty"
    using wf_thm_dest_eq[OF thy_wf th_wf dest] .
  have "holds F \<rho> \<nu> (concl th)"
    using valid type_ok const_ok free_ok hyps_ok
    by (auto simp: valid_sequent_def)
  then show ?thesis unfolding concl
    using holds_eq_iff[OF thy_wf models_frame[OF model] type_ok free_ok const_ok
        left right]
    by blast
qed

lemma refl_valid:
  assumes thy_wf: "wf_theory thy" and model: "models_theory F thy"
    and shape: "eq_shape thy [] t t (thy_stamp thy) th"
  shows "valid_sequent F thy (hyps th) (concl th)"
proof -
  obtain ty where type: "type_of t = Some ty"
    and out: "th = \<lparr>hyps = [], concl = eq_term ty t t,
      thm_stamp = thy_stamp thy\<rparr>"
    and out_wf: "wf_thm thy th"
    using eq_shape_parts[OF shape] by blast
  have dest: "dest_eq (concl th) = Some (t, t)"
    using out by (simp add: eq_term_def eq_const_def)
  have checked: "check_term thy t"
    using wf_thm_dest_eq[OF thy_wf out_wf dest] by blast
  show ?thesis
    unfolding out valid_sequent_def
  proof (simp, intro allI impI)
    fix \<rho> \<nu>
    assume type_ok: "type_valuation_ok \<rho>"
      and const_ok: "const_interpretation_ok F thy \<rho>"
      and free_ok: "free_valuation_ok F \<rho> \<nu>"
    show "holds F \<rho> \<nu> (eq_term ty t t)"
      using holds_eq_iff[OF thy_wf models_frame[OF model] type_ok free_ok const_ok
          checked type checked type]
      by simp
  qed
qed

lemma trans_valid:
  assumes thy_wf: "wf_theory thy" and model: "models_theory F thy"
    and a_wf: "wf_thm thy a" and b_wf: "wf_thm thy b"
    and a_valid: "valid_sequent F thy (hyps a) (concl a)"
    and b_valid: "valid_sequent F thy (hyps b) (concl b)"
    and a_dest: "dest_eq (concl a) = Some (l, m)"
    and b_dest: "dest_eq (concl b) = Some (m, r)"
    and shape: "eq_shape thy (hyp_union (hyps a) (hyps b)) l r st th"
  shows "valid_sequent F thy (hyps th) (concl th)"
proof -
  obtain aty where left: "check_term thy l" "type_of l = Some aty"
    and middle: "check_term thy m" "type_of m = Some aty"
    using wf_thm_dest_eq[OF thy_wf a_wf a_dest] by blast
  obtain bty where middle': "type_of m = Some bty"
    and right: "check_term thy r" "type_of r = Some bty"
    using wf_thm_dest_eq[OF thy_wf b_wf b_dest] by blast
  have types: "aty = bty" using middle(2) middle' by simp
  obtain oty where out_types: "type_of l = Some oty" "type_of r = Some oty"
    and out: "th = \<lparr>hyps = hyp_union (hyps a) (hyps b),
      concl = eq_term oty l r, thm_stamp = st\<rparr>"
    using eq_shape_parts[OF shape] by blast
  have out_ty: "oty = aty" using out_types(1) left(2) by simp
  show ?thesis unfolding out valid_sequent_def
  proof (simp, intro allI impI)
    fix \<rho> \<nu>
    assume type_ok: "type_valuation_ok \<rho>"
      and const_ok: "const_interpretation_ok F thy \<rho>"
      and free_ok: "free_valuation_ok F \<rho> \<nu>"
      and hyps_ok: "\<forall>h\<in>set (hyps a) \<union> set (hyps b). holds F \<rho> \<nu> h"
    have a_hyps: "\<forall>h\<in>set (hyps a). holds F \<rho> \<nu> h"
      using hyps_ok by auto
    have b_hyps: "\<forall>h\<in>set (hyps b). holds F \<rho> \<nu> h"
      using hyps_ok by auto
    have lm: "eval_term F \<rho> \<nu> [] l = eval_term F \<rho> \<nu> [] m"
      using valid_equality_elim[OF thy_wf model a_wf a_valid a_dest
          type_ok const_ok free_ok a_hyps] .
    have mr: "eval_term F \<rho> \<nu> [] m = eval_term F \<rho> \<nu> [] r"
      using valid_equality_elim[OF thy_wf model b_wf b_valid b_dest
          type_ok const_ok free_ok b_hyps] .
    have lr: "eval_term F \<rho> \<nu> [] l = eval_term F \<rho> \<nu> [] r"
      using lm mr by simp
    show "holds F \<rho> \<nu> (eq_term oty l r)"
      using holds_eq_iff[OF thy_wf models_frame[OF model] type_ok free_ok const_ok
          left(1) out_types(1) right(1) out_types(2)] lr by simp
  qed
qed

lemma mk_comb_valid:
  assumes thy_wf: "wf_theory thy" and model: "models_theory F thy"
    and a_wf: "wf_thm thy a" and b_wf: "wf_thm thy b"
    and a_valid: "valid_sequent F thy (hyps a) (concl a)"
    and b_valid: "valid_sequent F thy (hyps b) (concl b)"
    and a_dest: "dest_eq (concl a) = Some (f, g)"
    and b_dest: "dest_eq (concl b) = Some (x, y)"
    and shape: "eq_shape thy (hyp_union (hyps a) (hyps b))
      (Comb f x) (Comb g y) st th"
  shows "valid_sequent F thy (hyps th) (concl th)"
proof -
  obtain oty where out_types:
      "type_of (Comb f x) = Some oty" "type_of (Comb g y) = Some oty"
    and out: "th = \<lparr>hyps = hyp_union (hyps a) (hyps b),
      concl = eq_term oty (Comb f x) (Comb g y), thm_stamp = st\<rparr>"
    and out_wf: "wf_thm thy th"
    using eq_shape_parts[OF shape] .
  have out_dest: "dest_eq (concl th) = Some (Comb f x, Comb g y)"
    using out by (simp add: eq_term_def eq_const_def)
  obtain qty where left: "check_term thy (Comb f x)"
      "type_of (Comb f x) = Some qty"
    and right: "check_term thy (Comb g y)"
      "type_of (Comb g y) = Some qty"
    using wf_thm_dest_eq[OF thy_wf out_wf out_dest] by blast
  show ?thesis unfolding out valid_sequent_def
  proof (simp, intro allI impI)
    fix \<rho> \<nu>
    assume type_ok: "type_valuation_ok \<rho>"
      and const_ok: "const_interpretation_ok F thy \<rho>"
      and free_ok: "free_valuation_ok F \<rho> \<nu>"
      and hyps_ok: "\<forall>h\<in>set (hyps a) \<union> set (hyps b). holds F \<rho> \<nu> h"
    have fg: "eval_term F \<rho> \<nu> [] f = eval_term F \<rho> \<nu> [] g"
      using valid_equality_elim[OF thy_wf model a_wf a_valid a_dest
          type_ok const_ok free_ok] hyps_ok by auto
    have xy: "eval_term F \<rho> \<nu> [] x = eval_term F \<rho> \<nu> [] y"
      using valid_equality_elim[OF thy_wf model b_wf b_valid b_dest
          type_ok const_ok free_ok] hyps_ok by auto
    have apps: "eval_term F \<rho> \<nu> [] (Comb f x) =
        eval_term F \<rho> \<nu> [] (Comb g y)"
      using fg xy by simp
    show "holds F \<rho> \<nu> (eq_term oty (Comb f x) (Comb g y))"
      using holds_eq_iff[OF thy_wf models_frame[OF model] type_ok free_ok const_ok
          left(1) out_types(1) right(1) out_types(2)] apps by simp
  qed
qed

lemma abs_valid:
  assumes thy_wf: "wf_theory thy" and model: "models_theory F thy"
    and old_wf: "wf_thm thy old"
    and old_valid: "valid_sequent F thy (hyps old) (concl old)"
    and old_dest: "dest_eq (concl old) = Some (l, r)"
    and var_checked: "check_term thy (FVar n ty)"
    and fresh: "\<forall>h\<in>set (hyps old). \<not> vfree_in n ty h"
    and shape: "eq_shape thy (hyps old) (Abs ty (abstract_fvar n ty l))
      (Abs ty (abstract_fvar n ty r)) st th"
  shows "valid_sequent F thy (hyps th) (concl th)"
proof -
  obtain bty where left: "check_term thy l" "type_of l = Some bty"
    and right: "check_term thy r" "type_of r = Some bty"
    using wf_thm_dest_eq[OF thy_wf old_wf old_dest] by blast
  obtain oty where out_types:
      "type_of (Abs ty (abstract_fvar n ty l)) = Some oty"
      "type_of (Abs ty (abstract_fvar n ty r)) = Some oty"
    and out: "th = \<lparr>hyps = hyps old,
      concl = eq_term oty (Abs ty (abstract_fvar n ty l))
        (Abs ty (abstract_fvar n ty r)), thm_stamp = st\<rparr>"
    and out_wf: "wf_thm thy th"
    using eq_shape_parts[OF shape] .
  have out_dest: "dest_eq (concl th) =
      Some (Abs ty (abstract_fvar n ty l), Abs ty (abstract_fvar n ty r))"
    using out by (simp add: eq_term_def eq_const_def)
  obtain qty where out_left: "check_term thy (Abs ty (abstract_fvar n ty l))"
      "type_of (Abs ty (abstract_fvar n ty l)) = Some qty"
    and out_right: "check_term thy (Abs ty (abstract_fvar n ty r))"
      "type_of (Abs ty (abstract_fvar n ty r)) = Some qty"
    using wf_thm_dest_eq[OF thy_wf out_wf out_dest] by blast
  show ?thesis unfolding out valid_sequent_def
  proof (simp, intro allI impI)
    fix \<rho> \<nu>
    assume type_ok: "type_valuation_ok \<rho>"
      and const_ok: "const_interpretation_ok F thy \<rho>"
      and free_ok: "free_valuation_ok F \<rho> \<nu>"
      and hyps_ok: "\<forall>h\<in>set (hyps old). holds F \<rho> \<nu> h"
    have pointwise: "eval_term F \<rho> \<nu> [z] (abstract_fvar n ty l) =
        eval_term F \<rho> \<nu> [z] (abstract_fvar n ty r)"
      if z_in: "Elem z (interp_type F \<rho> ty)" for z
    proof -
      let ?\<nu>z = "\<nu>((n, ty) := z)"
      have free_z: "free_valuation_ok F \<rho> ?\<nu>z"
        using free_valuation_update[OF free_ok z_in] .
      have hyps_z: "\<forall>h\<in>set (hyps old). holds F \<rho> ?\<nu>z h"
      proof
        fix h
        assume member: "h \<in> set (hyps old)"
        have unchanged: "eval_term F \<rho> ?\<nu>z [] h = eval_term F \<rho> \<nu> [] h"
          using eval_not_vfree_update[OF fresh[rule_format, OF member],
              of F \<rho> \<nu> z "[]"] .
        show "holds F \<rho> ?\<nu>z h"
          using hyps_ok member unchanged by (simp add: holds_def)
      qed
      have lr: "eval_term F \<rho> ?\<nu>z [] l = eval_term F \<rho> ?\<nu>z [] r"
        using valid_equality_elim[OF thy_wf model old_wf old_valid old_dest
            type_ok const_ok free_z hyps_z] .
      have abstract_l: "eval_term F \<rho> \<nu> [z] (abstract_fvar n ty l) =
          eval_term F \<rho> ?\<nu>z [] l"
      proof -
        have invariant: "eval_term F \<rho> ?\<nu>z [z] (abstract_fvar n ty l) =
            eval_term F \<rho> \<nu> [z] (abstract_fvar n ty l)"
          using eval_not_vfree_update[OF abstract_fvar_removes_fvar,
              where F=F and \<rho>=\<rho> and \<nu>=\<nu> and z=z and env="[z]"
                and n=n and ty=ty] .
        have abstract: "eval_term F \<rho> ?\<nu>z [z] (abstract_fvar n ty l) =
            eval_term F \<rho> ?\<nu>z [] l"
          using eval_abstract_fvar[OF left(1), of F \<rho> ?\<nu>z n ty] by simp
        show ?thesis using invariant abstract by simp
      qed
      have abstract_r: "eval_term F \<rho> \<nu> [z] (abstract_fvar n ty r) =
          eval_term F \<rho> ?\<nu>z [] r"
      proof -
        have invariant: "eval_term F \<rho> ?\<nu>z [z] (abstract_fvar n ty r) =
            eval_term F \<rho> \<nu> [z] (abstract_fvar n ty r)"
          using eval_not_vfree_update[OF abstract_fvar_removes_fvar,
              where F=F and \<rho>=\<rho> and \<nu>=\<nu> and z=z and env="[z]"
                and n=n and ty=ty] .
        have abstract: "eval_term F \<rho> ?\<nu>z [z] (abstract_fvar n ty r) =
            eval_term F \<rho> ?\<nu>z [] r"
          using eval_abstract_fvar[OF right(1), of F \<rho> ?\<nu>z n ty] by simp
        show ?thesis using invariant abstract by simp
      qed
      show ?thesis using abstract_l abstract_r lr by simp
    qed
    have abstractions: "eval_term F \<rho> \<nu> [] (Abs ty (abstract_fvar n ty l)) =
        eval_term F \<rho> \<nu> [] (Abs ty (abstract_fvar n ty r))"
      using pointwise by (simp add: Lambda_ext)
    show "holds F \<rho> \<nu> (eq_term oty (Abs ty (abstract_fvar n ty l))
        (Abs ty (abstract_fvar n ty r)))"
      using holds_eq_iff[OF thy_wf models_frame[OF model] type_ok free_ok const_ok
          out_left(1) out_types(1) out_right(1) out_types(2)] abstractions by simp
  qed
qed

lemma beta_valid:
  assumes thy_wf: "wf_theory thy" and model: "models_theory F thy"
    and redex: "check_term thy (Comb (Abs aty body) arg)"
    and shape: "eq_shape thy [] (Comb (Abs aty body) arg)
      (subst_bvar arg body) st th"
  shows "valid_sequent F thy (hyps th) (concl th)"
proof -
  have body_checked: "check_open_term thy [aty] body"
    and arg_checked: "check_term thy arg"
    and arg_type: "type_of arg = Some aty"
    using redex by (auto simp: check_term_def mk_fun_def
        split: htype.splits option.splits prod.splits if_splits)
  have reduct: "check_term thy (subst_bvar arg body)"
    using beta_subject_reduction[OF redex] by blast
  obtain oty where out_types:
      "type_of (Comb (Abs aty body) arg) = Some oty"
      "type_of (subst_bvar arg body) = Some oty"
    and out: "th = \<lparr>hyps = [],
      concl = eq_term oty (Comb (Abs aty body) arg) (subst_bvar arg body),
      thm_stamp = st\<rparr>"
    using eq_shape_parts[OF shape] by blast
  show ?thesis unfolding out valid_sequent_def
  proof (simp, intro allI impI)
    fix \<rho> \<nu>
    assume type_ok: "type_valuation_ok \<rho>"
      and const_ok: "const_interpretation_ok F thy \<rho>"
      and free_ok: "free_valuation_ok F \<rho> \<nu>"
    have empty: "bound_valuation_ok F \<rho> [] []"
      by (simp add: bound_valuation_ok_def)
    have arg_in: "Elem (eval_term F \<rho> \<nu> [] arg) (interp_type F \<rho> aty)"
      using eval_type_sound[OF thy_wf models_frame[OF model] type_ok free_ok
          const_ok empty] arg_checked arg_type
      unfolding check_term_def by blast
    have red: "eval_term F \<rho> \<nu> [] (Comb (Abs aty body) arg) =
        eval_term F \<rho> \<nu> [] (subst_bvar arg body)"
      using Lambda_app[OF arg_in] eval_subst_bvar[OF body_checked arg_checked,
          of F \<rho> \<nu>]
      by simp
    show "holds F \<rho> \<nu> (eq_term oty (Comb (Abs aty body) arg)
        (subst_bvar arg body))"
      using holds_eq_iff[OF thy_wf models_frame[OF model] type_ok free_ok const_ok
          redex out_types(1) reduct out_types(2)] red by simp
  qed
qed

lemma assume_valid:
  assumes shape: "thm_shape thy [p] p (thy_stamp thy) th"
  shows "valid_sequent F thy (hyps th) (concl th)"
  using shape by (auto simp: thm_shape_def valid_sequent_def)

lemma eq_mp_valid:
  assumes thy_wf: "wf_theory thy" and model: "models_theory F thy"
    and eq_wf: "wf_thm thy eqth" and old_wf: "wf_thm thy old"
    and eq_valid: "valid_sequent F thy (hyps eqth) (concl eqth)"
    and old_valid: "valid_sequent F thy (hyps old) (concl old)"
    and dest: "dest_eq (concl eqth) = Some (p, q)"
    and premise: "p = concl old"
    and shape: "thm_shape thy (hyp_union (hyps eqth) (hyps old)) q st th"
  shows "valid_sequent F thy (hyps th) (concl th)"
proof -
  have out: "th = \<lparr>hyps = hyp_union (hyps eqth) (hyps old),
      concl = q, thm_stamp = st\<rparr>"
    using shape by (simp add: thm_shape_def)
  show ?thesis unfolding out valid_sequent_def
  proof (simp, intro allI impI)
    fix \<rho> \<nu>
    assume type_ok: "type_valuation_ok \<rho>"
      and const_ok: "const_interpretation_ok F thy \<rho>"
      and free_ok: "free_valuation_ok F \<rho> \<nu>"
      and all_hyps: "\<forall>h\<in>set (hyps eqth) \<union> set (hyps old). holds F \<rho> \<nu> h"
    have eq_hyps: "\<forall>h\<in>set (hyps eqth). holds F \<rho> \<nu> h"
      and old_hyps: "\<forall>h\<in>set (hyps old). holds F \<rho> \<nu> h"
      using all_hyps by auto
    have pq: "eval_term F \<rho> \<nu> [] p = eval_term F \<rho> \<nu> [] q"
      using valid_equality_elim[OF thy_wf model eq_wf eq_valid dest
          type_ok const_ok free_ok eq_hyps] .
    have "holds F \<rho> \<nu> (concl old)"
      using old_valid type_ok const_ok free_ok old_hyps
      by (auto simp: valid_sequent_def)
    then show "holds F \<rho> \<nu> q"
      using pq premise by (simp add: holds_def)
  qed
qed

lemma wf_thm_concl_in_zbool:
  assumes thy_wf: "wf_theory thy" and frame: "frame_wf F"
    and type_ok: "type_valuation_ok \<rho>"
    and free_ok: "free_valuation_ok F \<rho> \<nu>"
    and const_ok: "const_interpretation_ok F thy \<rho>"
    and th_wf: "wf_thm thy th"
  shows "Elem (eval_term F \<rho> \<nu> [] (concl th)) zbool"
proof -
  have checked: "check_term thy (concl th)"
    and typed: "type_of (concl th) = Some bool_ty"
    using th_wf by (auto simp: wf_thm_def check_prop_def is_bool_def)
  have empty: "bound_valuation_ok F \<rho> [] []"
    by (simp add: bound_valuation_ok_def)
  have result: "Elem (eval_term F \<rho> \<nu> [] (concl th))
      (interp_type F \<rho> bool_ty)"
    using eval_type_sound[OF thy_wf frame type_ok free_ok const_ok empty]
      checked typed unfolding check_term_def by blast
  show ?thesis using result
    by (simp only: interp_type_bool_ty)
qed

lemma deduct_antisym_valid:
  assumes thy_wf: "wf_theory thy" and model: "models_theory F thy"
    and a_wf: "wf_thm thy a" and b_wf: "wf_thm thy b"
    and a_valid: "valid_sequent F thy (hyps a) (concl a)"
    and b_valid: "valid_sequent F thy (hyps b) (concl b)"
    and shape: "eq_shape thy
      (hyp_union (hyp_remove (concl b) (hyps a))
        (hyp_remove (concl a) (hyps b)))
      (concl a) (concl b) st th"
  shows "valid_sequent F thy (hyps th) (concl th)"
proof -
  obtain oty where out_types:
      "type_of (concl a) = Some oty" "type_of (concl b) = Some oty"
    and out: "th = \<lparr>hyps =
        hyp_union (hyp_remove (concl b) (hyps a))
          (hyp_remove (concl a) (hyps b)),
      concl = eq_term oty (concl a) (concl b), thm_stamp = st\<rparr>"
    using eq_shape_parts[OF shape] by blast
  have a_checked: "check_term thy (concl a)"
    and b_checked: "check_term thy (concl b)"
    using a_wf b_wf by (auto simp: wf_thm_def check_prop_def)
  show ?thesis unfolding out valid_sequent_def
  proof (simp, intro allI impI)
    fix \<rho> \<nu>
    assume type_ok: "type_valuation_ok \<rho>"
      and const_ok: "const_interpretation_ok F thy \<rho>"
      and free_ok: "free_valuation_ok F \<rho> \<nu>"
      and base_hyps: "\<forall>h\<in>(set (hyps a) - {concl b}) \<union>
          (set (hyps b) - {concl a}). holds F \<rho> \<nu> h"
    have iff: "holds F \<rho> \<nu> (concl a) \<longleftrightarrow> holds F \<rho> \<nu> (concl b)"
    proof
      assume a_true: "holds F \<rho> \<nu> (concl a)"
      have b_hyps: "\<forall>h\<in>set (hyps b). holds F \<rho> \<nu> h"
      proof (intro ballI)
        fix h
        assume member: "h \<in> set (hyps b)"
        show "holds F \<rho> \<nu> h"
        proof (cases "h = concl a")
          case True
          then show ?thesis using a_true by simp
        next
          case False
          then show ?thesis using base_hyps member by auto
        qed
      qed
      show "holds F \<rho> \<nu> (concl b)"
        using b_valid type_ok const_ok free_ok b_hyps
        by (auto simp: valid_sequent_def)
    next
      assume b_true: "holds F \<rho> \<nu> (concl b)"
      have a_hyps: "\<forall>h\<in>set (hyps a). holds F \<rho> \<nu> h"
      proof (intro ballI)
        fix h
        assume member: "h \<in> set (hyps a)"
        show "holds F \<rho> \<nu> h"
        proof (cases "h = concl b")
          case True
          then show ?thesis using b_true by simp
        next
          case False
          then show ?thesis using base_hyps member by auto
        qed
      qed
      show "holds F \<rho> \<nu> (concl a)"
        using a_valid type_ok const_ok free_ok a_hyps
        by (auto simp: valid_sequent_def)
    qed
    have a_bool: "Elem (eval_term F \<rho> \<nu> [] (concl a)) zbool"
      using wf_thm_concl_in_zbool[OF thy_wf models_frame[OF model] type_ok
          free_ok const_ok a_wf] .
    have b_bool: "Elem (eval_term F \<rho> \<nu> [] (concl b)) zbool"
      using wf_thm_concl_in_zbool[OF thy_wf models_frame[OF model] type_ok
          free_ok const_ok b_wf] .
    have same: "eval_term F \<rho> \<nu> [] (concl a) =
        eval_term F \<rho> \<nu> [] (concl b)"
      using iff a_bool b_bool ztrue_neq_zfalse
      by (auto simp: holds_def)
    show "holds F \<rho> \<nu> (eq_term oty (concl a) (concl b))"
      using holds_eq_iff[OF thy_wf models_frame[OF model] type_ok free_ok const_ok
          a_checked out_types(1) b_checked out_types(2)] same by simp
  qed
qed

lemma inst_valid:
  assumes thy_wf: "wf_theory thy" and model: "models_theory F thy"
    and old_valid: "valid_sequent F thy (hyps old) (concl old)"
    and subst_ok: "wf_term_subst thy \<theta>"
    and shape: "thm_shape thy (rehash_hyps (map (inst_fvar \<theta>) (hyps old)))
      (inst_fvar \<theta> (concl old)) st th"
  shows "valid_sequent F thy (hyps th) (concl th)"
proof -
  have out: "th = \<lparr>hyps = rehash_hyps (map (inst_fvar \<theta>) (hyps old)),
      concl = inst_fvar \<theta> (concl old), thm_stamp = st\<rparr>"
    using shape by (simp add: thm_shape_def)
  show ?thesis unfolding out valid_sequent_def
  proof (simp only: hthm.select_convs, intro allI impI)
    fix \<rho> \<nu>
    assume type_ok: "type_valuation_ok \<rho>"
      and const_ok: "const_interpretation_ok F thy \<rho>"
      and free_ok: "free_valuation_ok F \<rho> \<nu>"
      and mapped_hyps: "\<forall>h\<in>set (rehash_hyps (map (inst_fvar \<theta>)
        (hyps old))). holds F \<rho> \<nu> h"
    let ?\<nu>s = "semantic_fvar_subst F \<rho> \<nu> \<theta>"
    have subst_free: "free_valuation_ok F \<rho> ?\<nu>s"
      using semantic_fvar_subst_ok[OF thy_wf models_frame[OF model] type_ok
          free_ok const_ok subst_ok] .
    have old_hyps: "\<forall>h\<in>set (hyps old). holds F \<rho> ?\<nu>s h"
    proof (intro ballI)
      fix h
      assume member: "h \<in> set (hyps old)"
      have "holds F \<rho> \<nu> (inst_fvar \<theta> h)"
        using mapped_hyps member by auto
      then show "holds F \<rho> ?\<nu>s h"
        using eval_inst_fvar[OF subst_ok, where F=F and \<rho>=\<rho> and \<nu>=\<nu> and t=h]
        by (simp add: holds_def)
    qed
    have old_concl: "holds F \<rho> ?\<nu>s (concl old)"
      using old_valid type_ok const_ok subst_free old_hyps
      by (auto simp: valid_sequent_def)
    show "holds F \<rho> \<nu> (inst_fvar \<theta> (concl old))"
      using old_concl eval_inst_fvar[OF subst_ok,
          where F=F and \<rho>=\<rho> and \<nu>=\<nu> and t="concl old"]
      by (simp add: holds_def)
  qed
qed

lemma inst_type_valid:
  assumes thy_wf: "wf_theory thy" and model: "models_theory F thy"
    and old_wf: "wf_thm thy old"
    and old_valid: "valid_sequent F thy (hyps old) (concl old)"
    and subst_ok: "type_subst_ok thy \<theta>"
    and shape: "thm_shape thy (rehash_hyps (map (inst_type \<theta>) (hyps old)))
      (inst_type \<theta> (concl old)) st th"
  shows "valid_sequent F thy (hyps th) (concl th)"
proof -
  have out: "th = \<lparr>hyps = rehash_hyps (map (inst_type \<theta>) (hyps old)),
      concl = inst_type \<theta> (concl old), thm_stamp = st\<rparr>"
    using shape by (simp add: thm_shape_def)
  show ?thesis unfolding out valid_sequent_def
  proof (simp only: hthm.select_convs, intro allI impI)
    fix \<rho> \<nu>
    assume type_ok: "type_valuation_ok \<rho>"
      and target_const: "const_interpretation_ok F thy \<rho>"
      and free_ok: "free_valuation_ok F \<rho> \<nu>"
      and mapped_hyps: "\<forall>h\<in>set (rehash_hyps (map (inst_type \<theta>)
        (hyps old))). holds F \<rho> \<nu> h"
    let ?\<rho>s = "subst_valuation F \<rho> \<theta>"
    let ?\<nu>s = "semantic_type_fvars \<theta> \<nu>"
    have subst_type: "type_valuation_ok ?\<rho>s"
      using subst_valuation_ok[OF models_frame[OF model] type_ok] .
    have subst_free: "free_valuation_ok F ?\<rho>s ?\<nu>s"
      using semantic_type_fvars_ok[OF free_ok] .
    have subst_const: "const_interpretation_ok F thy ?\<rho>s"
      using model subst_type by (auto simp: models_theory_def)
    have old_hyps: "\<forall>h\<in>set (hyps old). holds F ?\<rho>s ?\<nu>s h"
    proof (intro ballI)
      fix h
      assume member: "h \<in> set (hyps old)"
      have checked: "check_open_term thy [] h"
        using old_wf member
        by (auto simp: wf_thm_def list_all_iff check_prop_def check_term_def)
      have "holds F \<rho> \<nu> (inst_type \<theta> h)"
        using mapped_hyps member by auto
      then show "holds F ?\<rho>s ?\<nu>s h"
        using eval_inst_type[OF thy_wf models_frame[OF model] subst_ok target_const checked,
            where \<nu>=\<nu> and env="[]"]
        by (simp add: holds_def)
    qed
    have old_concl: "holds F ?\<rho>s ?\<nu>s (concl old)"
      using old_valid subst_type subst_const subst_free old_hyps
      by (auto simp: valid_sequent_def)
    have checked_concl: "check_open_term thy [] (concl old)"
      using old_wf by (auto simp: wf_thm_def check_prop_def check_term_def)
    show "holds F \<rho> \<nu> (inst_type \<theta> (concl old))"
      using old_concl eval_inst_type[OF thy_wf models_frame[OF model] subst_ok target_const checked_concl,
          where \<nu>=\<nu> and env="[]"]
      by (simp add: holds_def)
  qed
qed

lemma rule_spec_valid:
  assumes ambient: "ambient_theory i = thy"
    and thy_wf: "wf_theory thy" and model: "models_theory F thy"
    and spec: "rule_spec i th"
    and input_wf: "list_all (wf_thm thy) (input_thms i)"
    and input_valid: "list_all (\<lambda>old. valid_sequent F thy (hyps old)
      (concl old)) (input_thms i)"
  shows "valid_sequent F thy (hyps th) (concl th)"
  using spec ambient thy_wf model input_wf input_valid
  by cases
     (auto intro: refl_valid trans_valid mk_comb_valid abs_valid beta_valid
       assume_valid eq_mp_valid deduct_antisym_valid inst_valid inst_type_valid)

theorem derives_valid:
  assumes derived: "derives thy th"
    and thy_wf: "wf_theory thy" and model: "models_theory F thy"
  shows "valid_sequent F thy (hyps th) (concl th)"
proof -
  from derived have step: "wf_theory thy \<longrightarrow> models_theory F thy \<longrightarrow>
      valid_sequent F thy (hyps th) (concl th)"
  proof (induction rule: derives.induct)
    case (Axiom th)
    then show ?case by (auto simp: models_theory_def)
  next
    case (Primitive i thy th)
    show ?case
    proof (intro impI)
      assume local_wf: "wf_theory thy"
        and local_model: "models_theory F thy"
      have input_wf: "list_all (wf_thm thy) (input_thms i)"
        using Primitive.IH
        by (auto simp: list_all_iff dest: derives_wf)
      have input_valid: "list_all (\<lambda>old. valid_sequent F thy
          (hyps old) (concl old)) (input_thms i)"
        using Primitive.IH local_wf local_model
        by (auto simp: list_all_iff)
      show "valid_sequent F thy (hyps th) (concl th)"
        using rule_spec_valid[OF Primitive.hyps(1) local_wf local_model
            Primitive.hyps(2) input_wf input_valid] .
    qed
  qed
  show ?thesis using step thy_wf model by blast
qed

theorem kernel_soundness:
  "wf_theory thy \<Longrightarrow> derives thy th \<Longrightarrow> semantically_valid thy th"
  using derives_wf derives_valid
  by (auto simp: semantically_valid_def)

theorem run_rule_semantic_sound:
  assumes thy_wf: "wf_theory (ambient_theory i)"
    and model: "models_theory F (ambient_theory i)"
    and run: "run_rule i = Some th"
    and input_wf: "list_all (wf_thm (ambient_theory i)) (input_thms i)"
    and input_valid: "list_all (\<lambda>old. valid_sequent F (ambient_theory i)
      (hyps old) (concl old)) (input_thms i)"
  shows "valid_sequent F (ambient_theory i) (hyps th) (concl th)"
  using rule_spec_valid[OF refl thy_wf model run_rule_sound[OF run]
      input_wf input_valid] .

theorem primitive_rules_sound:
  assumes "wf_theory (ambient_theory i)"
    "models_theory F (ambient_theory i)"
    "run_rule i = Some th"
    "list_all (wf_thm (ambient_theory i)) (input_thms i)"
    "list_all (\<lambda>old. valid_sequent F (ambient_theory i)
      (hyps old) (concl old)) (input_thms i)"
  shows "valid_sequent F (ambient_theory i) (hyps th) (concl th)"
  using assms by (rule run_rule_semantic_sound)

theorem derives_sound:
  "derives thy th \<Longrightarrow> wf_theory thy \<Longrightarrow> models_theory F thy \<Longrightarrow>
    valid_sequent F thy (hyps th) (concl th)"
  by (rule derives_valid)

end

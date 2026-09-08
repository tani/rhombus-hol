theory Rhombus_HOL_Adequacy
  imports Rhombus_HOL_Base_Model
begin

section \<open>Finite trace replay\<close>

datatype trace_event =
    EvInitial nat
  | EvPrimitive inference
  | EvNewType nat hname nat
  | EvNewConstant nat hname htype
  | EvNewAxiom nat hterm
  | EvBasicDefinition nat hterm
  | EvBasicTypeDefinition nat hname hname hname hthm

record replay_state =
  active_theory :: "htheory option"
  replayed_theorems :: "hthm list"
  axiom_obligations :: "hterm list"

definition empty_replay_state :: replay_state where
  "empty_replay_state = \<lparr>active_theory = None, replayed_theorems = [],
    axiom_obligations = []\<rparr>"

fun trace_step :: "trace_event \<Rightarrow> replay_state \<Rightarrow> replay_state option" where
  "trace_step (EvInitial fresh) s =
    (if active_theory s = None then
       Some (s\<lparr>active_theory := Some (initial_theory fresh)\<rparr>) else None)"
| "trace_step (EvPrimitive i) s =
    (case active_theory s of
       None \<Rightarrow> None
     | Some thy \<Rightarrow> if ambient_theory i \<noteq> thy then None
       else (case run_rule i of None \<Rightarrow> None
       | Some th \<Rightarrow> Some (s\<lparr>replayed_theorems := th # replayed_theorems s\<rparr>)))"
| "trace_step (EvNewType fresh n arity) s =
    (case active_theory s of None \<Rightarrow> None | Some thy \<Rightarrow>
      map_option (\<lambda>thy'. s\<lparr>active_theory := Some thy'\<rparr>)
        (new_type fresh thy n arity))"
| "trace_step (EvNewConstant fresh n ty) s =
    (case active_theory s of None \<Rightarrow> None | Some thy \<Rightarrow>
      map_option (\<lambda>thy'. s\<lparr>active_theory := Some thy'\<rparr>)
        (new_constant fresh thy n ty))"
| "trace_step (EvNewAxiom fresh p) s =
    (case active_theory s of None \<Rightarrow> None | Some thy \<Rightarrow>
      (case new_axiom fresh thy p of None \<Rightarrow> None | Some (thy', th) \<Rightarrow>
        Some (s\<lparr>active_theory := Some thy',
          replayed_theorems := th # replayed_theorems s,
          axiom_obligations := p # axiom_obligations s\<rparr>)))"
| "trace_step (EvBasicDefinition fresh tm) s =
    (case active_theory s of None \<Rightarrow> None | Some thy \<Rightarrow>
      (case new_basic_definition fresh thy tm of None \<Rightarrow> None
       | Some (thy', th) \<Rightarrow> Some (s\<lparr>active_theory := Some thy',
           replayed_theorems := th # replayed_theorems s\<rparr>)))"
| "trace_step (EvBasicTypeDefinition fresh tn an rn wit) s =
    (case active_theory s of None \<Rightarrow> None | Some thy \<Rightarrow>
      (case new_basic_type_definition fresh thy tn an rn wit of None \<Rightarrow> None
       | Some (thy', th1, th2) \<Rightarrow> Some (s\<lparr>active_theory := Some thy',
           replayed_theorems := th2 # th1 # replayed_theorems s\<rparr>)))"

fun replay_trace ::
  "trace_event list \<Rightarrow> replay_state \<Rightarrow> replay_state option" where
  "replay_trace [] s = Some s"
| "replay_trace (e # es) s =
    (case trace_step e s of None \<Rightarrow> None | Some s' \<Rightarrow> replay_trace es s')"

inductive trace_step_spec ::
  "trace_event \<Rightarrow> replay_state \<Rightarrow> replay_state \<Rightarrow> bool" where
  certified_step: "trace_step e s = Some s' \<Longrightarrow> trace_step_spec e s s'"

inductive replay_spec ::
  "trace_event list \<Rightarrow> replay_state \<Rightarrow> replay_state \<Rightarrow> bool" where
  replay_nil: "replay_spec [] s s"
| replay_cons: "trace_step_spec e s s' \<Longrightarrow> replay_spec es s' s'' \<Longrightarrow>
    replay_spec (e # es) s s''"

lemma trace_step_adequate:
  "trace_step e s = Some s' \<longleftrightarrow> trace_step_spec e s s'"
  by (auto intro: trace_step_spec.certified_step elim: trace_step_spec.cases)

theorem replay_sound:
  "replay_trace es s = Some s' \<Longrightarrow> replay_spec es s s'"
proof (induction es arbitrary: s)
  case Nil
  then show ?case by (auto intro: replay_spec.replay_nil)
next
  case (Cons e es)
  then obtain mid where "trace_step e s = Some mid"
    "replay_trace es mid = Some s'"
    by (auto split: option.splits)
  then show ?case using Cons.IH trace_step_adequate
    by (auto intro: replay_spec.replay_cons)
qed

theorem replay_complete:
  "replay_spec es s s' \<Longrightarrow> replay_trace es s = Some s'"
proof (induction rule: replay_spec.induct)
  case (replay_nil s)
  then show ?case by simp
next
  case (replay_cons e s mid es out)
  have step: "trace_step e s = Some mid"
    using replay_cons.hyps(1) trace_step_adequate by blast
  show ?case using step replay_cons.IH by simp
qed

lemma axiom_events_record_obligations:
  assumes "trace_step (EvNewAxiom fresh p) s = Some s'"
  shows "axiom_obligations s' = p # axiom_obligations s"
  using assms by (auto split: option.splits prod.splits)

lemma primitive_events_do_not_add_axiom_obligations:
  assumes "trace_step (EvPrimitive i) s = Some s'"
  shows "axiom_obligations s' = axiom_obligations s"
  using assms by (auto split: option.splits if_splits)

section \<open>Keyed semantic replay\<close>

type_synonym theorem_key = "stamp \<times> hterm list \<times> hterm"

definition theorem_key :: "hthm \<Rightarrow> theorem_key" where
  "theorem_key th = (thm_stamp th, hyps th, concl th)"

lemma theorem_key_inject:
  "theorem_key a = theorem_key b \<Longrightarrow> a = b"
  by (cases a; cases b; simp add: theorem_key_def)

fun trace_input_theorems :: "trace_event \<Rightarrow> hthm list" where
  "trace_input_theorems (EvPrimitive i) = input_thms i"
| "trace_input_theorems (EvBasicTypeDefinition _ _ _ _ wit) = [wit]"
| "trace_input_theorems _ = []"

fun trace_output_count :: "trace_event \<Rightarrow> nat" where
  "trace_output_count (EvPrimitive _) = 1"
| "trace_output_count (EvNewAxiom _ _) = 1"
| "trace_output_count (EvBasicDefinition _ _) = 1"
| "trace_output_count (EvBasicTypeDefinition _ _ _ _ _) = 2"
| "trace_output_count _ = 0"

definition known_theorem_keys :: "replay_state \<Rightarrow> theorem_key set" where
  "known_theorem_keys s = theorem_key ` set (replayed_theorems s)"

record keyed_trace_event =
  payload :: trace_event
  declared_input_keys :: "theorem_key list"
  declared_output_keys :: "theorem_key list"

inductive keyed_trace_step ::
  "keyed_trace_event \<Rightarrow> replay_state \<Rightarrow> replay_state \<Rightarrow> bool" where
  certified_keyed_step:
    "\<lbrakk>declared_input_keys ke = map theorem_key (trace_input_theorems (payload ke));
      set (declared_input_keys ke) \<subseteq> known_theorem_keys s;
      trace_step (payload ke) s = Some s';
      declared_output_keys ke = map theorem_key
        (take (trace_output_count (payload ke)) (replayed_theorems s'))\<rbrakk>
     \<Longrightarrow> keyed_trace_step ke s s'"

inductive keyed_replay_spec ::
  "keyed_trace_event list \<Rightarrow> replay_state \<Rightarrow> replay_state \<Rightarrow> bool" where
  keyed_replay_nil: "keyed_replay_spec [] s s"
| keyed_replay_cons: "keyed_trace_step e s s' \<Longrightarrow>
    keyed_replay_spec es s' s'' \<Longrightarrow> keyed_replay_spec (e # es) s s''"

fun replay_keyed_trace ::
  "keyed_trace_event list \<Rightarrow> replay_state \<Rightarrow> replay_state option" where
  "replay_keyed_trace [] s = Some s"
| "replay_keyed_trace (ke # kes) s =
    (if declared_input_keys ke \<noteq> map theorem_key (trace_input_theorems (payload ke)) \<or>
        \<not> set (declared_input_keys ke) \<subseteq> known_theorem_keys s
     then None
     else case trace_step (payload ke) s of
       None \<Rightarrow> None
     | Some s' \<Rightarrow>
         if declared_output_keys ke \<noteq> map theorem_key
              (take (trace_output_count (payload ke)) (replayed_theorems s'))
         then None else replay_keyed_trace kes s')"

lemma keyed_trace_step_adequate:
  "replay_keyed_trace [ke] s = Some s' \<longleftrightarrow> keyed_trace_step ke s s'"
proof
  assume run: "replay_keyed_trace [ke] s = Some s'"
  have inputs: "declared_input_keys ke =
      map theorem_key (trace_input_theorems (payload ke))"
    and known: "set (declared_input_keys ke) \<subseteq> known_theorem_keys s"
    and step: "trace_step (payload ke) s = Some s'"
    and outputs: "declared_output_keys ke = map theorem_key
      (take (trace_output_count (payload ke)) (replayed_theorems s'))"
    using run by (auto split: option.splits if_splits)
  show "keyed_trace_step ke s s'"
    using inputs known step outputs by (rule keyed_trace_step.certified_keyed_step)
next
  assume relation: "keyed_trace_step ke s s'"
  from relation show "replay_keyed_trace [ke] s = Some s'"
    by (cases rule: keyed_trace_step.cases) simp
qed

theorem keyed_replay_sound:
  "replay_keyed_trace kes s = Some s' \<Longrightarrow> keyed_replay_spec kes s s'"
proof (induction kes arbitrary: s)
  case Nil
  then show ?case by (auto intro: keyed_replay_spec.keyed_replay_nil)
next
  case (Cons ke kes)
  then obtain mid where one: "replay_keyed_trace [ke] s = Some mid"
    and rest: "replay_keyed_trace kes mid = Some s'"
    by (auto split: option.splits if_splits)
  show ?case using keyed_trace_step_adequate[THEN iffD1, OF one]
      Cons.IH[OF rest]
    by (rule keyed_replay_spec.keyed_replay_cons)
qed

theorem keyed_replay_complete:
  "keyed_replay_spec kes s s' \<Longrightarrow> replay_keyed_trace kes s = Some s'"
proof (induction rule: keyed_replay_spec.induct)
  case (keyed_replay_nil s)
  then show ?case by simp
next
  case (keyed_replay_cons ke s mid kes out)
  have one: "replay_keyed_trace [ke] s = Some mid"
    using keyed_trace_step_adequate keyed_replay_cons.hyps(1) by blast
  show ?case using one keyed_replay_cons.IH
    by (auto split: option.splits if_splits)
qed

definition semantic_replay_state ::
  "frame \<Rightarrow> htheory \<Rightarrow> replay_state \<Rightarrow> bool" where
  "semantic_replay_state F thy s \<longleftrightarrow>
    active_theory s = Some thy \<and>
    list_all (wf_thm thy) (replayed_theorems s) \<and>
    list_all (\<lambda>th. valid_sequent F thy (hyps th) (concl th))
      (replayed_theorems s)"

lemma registered_input_theorem:
  assumes keys: "theorem_key ` set xs \<subseteq> known_theorem_keys s"
    and member: "x \<in> set xs"
  shows "x \<in> set (replayed_theorems s)"
proof -
  have "theorem_key x \<in> known_theorem_keys s" using keys member by blast
  then obtain old where old: "old \<in> set (replayed_theorems s)"
    "theorem_key x = theorem_key old"
    by (auto simp: known_theorem_keys_def)
  show ?thesis using old theorem_key_inject by blast
qed

theorem keyed_primitive_step_semantic_sound:
  assumes keyed: "keyed_trace_step ke s s'"
    and primitive: "payload ke = EvPrimitive i"
    and thy_wf: "wf_theory thy"
    and model: "models_theory F thy"
    and input_shape_wf: "wf_inputs i"
    and invariant: "semantic_replay_state F thy s"
  shows "semantic_replay_state F thy s'"
proof -
  have active: "active_theory s = Some thy"
    using invariant by (simp add: semantic_replay_state_def)
  have registered: "theorem_key ` set (input_thms i) \<subseteq> known_theorem_keys s"
    using keyed primitive by (cases rule: keyed_trace_step.cases) auto
  have step: "trace_step (EvPrimitive i) s = Some s'"
    using keyed primitive by (cases rule: keyed_trace_step.cases) auto
  obtain out where ambient: "ambient_theory i = thy"
    and run: "run_rule i = Some out"
    and state: "s' = s\<lparr>replayed_theorems := out # replayed_theorems s\<rparr>"
    using step active by (auto split: option.splits if_splits)
  have input_member: "\<forall>old\<in>set (input_thms i).
      old \<in> set (replayed_theorems s)"
    using registered registered_input_theorem by blast
  have input_wf: "list_all (wf_thm thy) (input_thms i)"
    using invariant input_member
    by (auto simp: semantic_replay_state_def list_all_iff)
  have input_valid: "list_all
      (\<lambda>old. valid_sequent F thy (hyps old) (concl old)) (input_thms i)"
    using invariant input_member
    by (auto simp: semantic_replay_state_def list_all_iff)
  have out_wf: "wf_thm thy out"
    using run_rule_preserves_wf[OF run input_shape_wf] ambient by simp
  have out_valid: "valid_sequent F thy (hyps out) (concl out)"
    using primitive_rules_sound[of i F out] thy_wf model run input_wf
      input_valid ambient by simp
  show ?thesis using invariant state out_wf out_valid
    by (simp add: semantic_replay_state_def)
qed

fun primitive_keyed_trace :: "keyed_trace_event list \<Rightarrow> bool" where
  "primitive_keyed_trace [] = True"
| "primitive_keyed_trace (ke # kes) =
    ((\<exists>i. payload ke = EvPrimitive i \<and> wf_inputs i) \<and> primitive_keyed_trace kes)"

theorem keyed_primitive_replay_semantic_sound:
  assumes replay: "keyed_replay_spec kes s s'"
    and primitive: "primitive_keyed_trace kes"
    and thy_wf: "wf_theory thy"
    and model: "models_theory F thy"
    and invariant: "semantic_replay_state F thy s"
  shows "semantic_replay_state F thy s'"
  using replay primitive invariant
proof (induction rule: keyed_replay_spec.induct)
  case (keyed_replay_nil s)
  then show ?case by simp
next
  case (keyed_replay_cons ke s mid kes out)
  then obtain i where event: "payload ke = EvPrimitive i"
    and input_shape_wf: "wf_inputs i"
    and tail: "primitive_keyed_trace kes" by auto
  have mid_invariant: "semantic_replay_state F thy mid"
    using keyed_primitive_step_semantic_sound[OF keyed_replay_cons.hyps(1)
        event thy_wf model input_shape_wf keyed_replay_cons.prems(2)] .
  show ?case using keyed_replay_cons.IH[OF tail mid_invariant] .
qed

fun extension_trace_event :: "trace_event \<Rightarrow> bool" where
  "extension_trace_event (EvNewType _ _ _) = True"
| "extension_trace_event (EvNewConstant _ _ _) = True"
| "extension_trace_event (EvNewAxiom _ _) = True"
| "extension_trace_event (EvBasicDefinition _ _) = True"
| "extension_trace_event (EvBasicTypeDefinition _ _ _ _ _) = True"
| "extension_trace_event _ = False"

definition recent_outputs_valid ::
  "frame \<Rightarrow> htheory \<Rightarrow> trace_event \<Rightarrow> replay_state \<Rightarrow> bool" where
  "recent_outputs_valid F thy e s \<longleftrightarrow>
    list_all (\<lambda>th. valid_sequent F thy (hyps th) (concl th))
      (take (trace_output_count e) (replayed_theorems s))"

definition axiom_event_valid ::
  "frame \<Rightarrow> keyed_trace_event \<Rightarrow> replay_state \<Rightarrow> bool" where
  "axiom_event_valid F ke s \<longleftrightarrow>
    (\<forall>fresh p thy thy' th. payload ke = EvNewAxiom fresh p \<longrightarrow>
      active_theory s = Some thy \<longrightarrow>
      new_axiom fresh thy p = Some (thy', th) \<longrightarrow>
      valid_sequent F thy' [] p)"

theorem keyed_extension_step_semantic_sound:
  assumes keyed: "keyed_trace_step ke s s'"
    and extension: "extension_trace_event (payload ke)"
    and thy_wf: "wf_theory thy"
    and contents_wf: "theory_contents_wf thy"
    and model: "models_theory F thy"
    and invariant: "semantic_replay_state F thy s"
    and axiom_valid: "axiom_event_valid F ke s"
  obtains F' thy' where
    "active_theory s' = Some thy'"
    "models_theory F' thy'"
    "recent_outputs_valid F' thy' (payload ke) s'"
proof -
  have active: "active_theory s = Some thy"
    using invariant by (simp add: semantic_replay_state_def)
  have step: "trace_step (payload ke) s = Some s'"
    using keyed by (cases rule: keyed_trace_step.cases) auto
  show thesis
  proof (cases "payload ke")
    case (EvInitial fresh)
    then show thesis using extension by simp
  next
    case (EvPrimitive i)
    then show thesis using extension by simp
  next
    case (EvNewType fresh n arity)
    then obtain thy' where run: "new_type fresh thy n arity = Some thy'"
      and state: "s' = s\<lparr>active_theory := Some thy'\<rparr>"
      using step active by (auto split: option.splits)
    let ?F' = "add_type_frame F n (\<lambda>_. zbool)"
    have model': "models_theory ?F' thy'"
      using new_type_conservative[OF run thy_wf contents_wf model] .
    show thesis
      using that[of thy' ?F'] state model' EvNewType
      by (simp add: recent_outputs_valid_def)
  next
    case (EvNewConstant fresh n ty)
    then obtain thy' where run: "new_constant fresh thy n ty = Some thy'"
      and state: "s' = s\<lparr>active_theory := Some thy'\<rparr>"
      using step active by (auto split: option.splits)
    let ?F' = "add_constant_frame F n ty"
    have model': "models_theory ?F' thy'"
      using new_constant_conservative[OF run thy_wf contents_wf model] .
    show thesis
      using that[of thy' ?F'] state model' EvNewConstant
      by (simp add: recent_outputs_valid_def)
  next
    case (EvNewAxiom fresh p)
    then obtain thy' th where run: "new_axiom fresh thy p = Some (thy', th)"
      and state: "s' = s\<lparr>active_theory := Some thy',
        replayed_theorems := th # replayed_theorems s,
        axiom_obligations := p # axiom_obligations s\<rparr>"
      using step active by (auto split: option.splits prod.splits)
    have p_valid: "valid_sequent F thy' [] p"
      using axiom_valid EvNewAxiom active run
      by (auto simp: axiom_event_valid_def)
    have model': "models_theory F thy'"
      using new_axiom_model_extension[OF run model p_valid] .
    have outputs: "hyps th = []" "concl th = p"
      using new_axiom_extract[OF run] by auto
    show thesis
      using that[of thy' F] state model' p_valid outputs EvNewAxiom
      by (simp add: recent_outputs_valid_def)
  next
    case (EvBasicDefinition fresh tm)
    then obtain thy' dth where run:
        "new_basic_definition fresh thy tm = Some (thy', dth)"
      and state: "s' = s\<lparr>active_theory := Some thy',
        replayed_theorems := dth # replayed_theorems s\<rparr>"
      using step active by (auto split: option.splits prod.splits)
    obtain n ty rhs where dth_shape:
        "dth = \<lparr>hyps = [], concl = eq_term ty (Const n ty) rhs,
          thm_stamp = next_stamp fresh (thy_stamp thy)\<rparr>"
      and model': "models_theory (add_definition_frame F n ty
          (closed_term_denote F rhs)) thy'"
      and output_valid: "valid_sequent (add_definition_frame F n ty
          (closed_term_denote F rhs)) thy' [] (concl dth)"
      using new_basic_definition_conservative[OF run thy_wf contents_wf model]
      by blast
    have dth_hyps: "hyps dth = []" using dth_shape by simp
    let ?F' = "add_definition_frame F n ty (closed_term_denote F rhs)"
    show thesis
      using that[of thy' ?F'] state model' output_valid dth_hyps
        EvBasicDefinition
      by (simp add: recent_outputs_valid_def)
  next
    case (EvBasicTypeDefinition fresh tn an rn wit)
    then obtain thy' th1 th2 where run:
        "new_basic_type_definition fresh thy tn an rn wit =
          Some (thy', th1, th2)"
      and state: "s' = s\<lparr>active_theory := Some thy',
        replayed_theorems := th2 # th1 # replayed_theorems s\<rparr>"
      using step active by (auto split: option.splits prod.splits)
    have registered: "theorem_key ` set [wit] \<subseteq> known_theorem_keys s"
      using keyed EvBasicTypeDefinition
      by (cases rule: keyed_trace_step.cases) auto
    have wit_member: "wit \<in> set (replayed_theorems s)"
      using registered_input_theorem[OF registered, of wit] by simp
    have wit_valid: "valid_sequent F thy (hyps wit) (concl wit)"
      using invariant wit_member
      by (auto simp: semantic_replay_state_def list_all_iff)
    obtain pred witness rty tvs aty where wit_shape:
        "concl wit = Comb pred witness"
      and model': "models_theory
          (add_type_definition_frame F tn
            (type_definition_carrier F pred rty tvs) an (mk_fun rty aty)
            (type_definition_abs F pred rty tvs) rn (mk_fun aty rty)
            (type_definition_rep F pred rty tvs)) thy'"
      and th1_valid: "valid_sequent
          (add_type_definition_frame F tn
            (type_definition_carrier F pred rty tvs) an (mk_fun rty aty)
            (type_definition_abs F pred rty tvs) rn (mk_fun aty rty)
            (type_definition_rep F pred rty tvs)) thy' [] (concl th1)"
      and th2_valid: "valid_sequent
          (add_type_definition_frame F tn
            (type_definition_carrier F pred rty tvs) an (mk_fun rty aty)
            (type_definition_abs F pred rty tvs) rn (mk_fun aty rty)
            (type_definition_rep F pred rty tvs)) thy' [] (concl th2)"
      by (rule new_basic_type_definition_conservative
          [OF run thy_wf contents_wf model wit_valid])
    have output_hyps: "hyps th1 = []" "hyps th2 = []"
      using run
      by (auto simp: new_basic_type_definition_def Let_def
          split: hterm.splits option.splits if_splits)
    let ?F' = "add_type_definition_frame F tn
      (type_definition_carrier F pred rty tvs) an (mk_fun rty aty)
      (type_definition_abs F pred rty tvs) rn (mk_fun aty rty)
      (type_definition_rep F pred rty tvs)"
    show thesis
      using that[of thy' ?F'] state model' th1_valid th2_valid output_hyps
        EvBasicTypeDefinition
      by (simp add: recent_outputs_valid_def)
  qed
qed

end

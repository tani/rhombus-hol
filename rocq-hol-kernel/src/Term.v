(** HOL terms, in locally nameless (de Bruijn) form.

    Transliteration of [rhombus-hol-kernel/rhombus/hol/term.rhm].  A
    [TmFVar] is a free variable: it has a name, and it is what hypotheses,
    goals and instantiations talk about.  A [TmBVar] is a bound variable:
    it has no name, only a de Bruijn index counting outwards from the
    innermost enclosing [TmAbs].  [Term] has no [seq Term]-valued field
    (unlike [HType]), so it is not a "nested" inductive and Coq's own
    auto-derived induction principle already gives the right induction
    hypotheses for [TmComb]'s two subterms and [TmAbs]'s body; no custom
    scheme is needed here.

    Alpha-equivalence disappears: two terms are equal exactly when their
    syntax trees are equal, so [==] is the only equality anyone needs. *)

From mathcomp Require Import all_boot finmap.
From HB Require Import structures.
From Stdlib Require Import ZArith PeanoNat.
From RocqHolKernel Require Import Names HType.

Open Scope fmap_scope.
Open Scope fset_scope.

(** * Free variables *)

(** [class FVar(...) extends Term] is a real, statically-checked subtype
    in Rhombus -- kernel functions like [ABS]/[mk_abs] take an [FVar]
    specifically, not an arbitrary [Term] -- so [FVar] is its own record
    here too, not merely "a [Term] known to be that shape". *)
Record FVar := mkFVar { fv_name : Name; fv_ty : HType }.

Definition FVar_eqb (a b : FVar) : bool :=
  (fv_name a == fv_name b) && (fv_ty a == fv_ty b).

Lemma FVar_eqP : Equality.axiom FVar_eqb.
Proof.
case=> [n1 t1] [n2 t2]; rewrite /FVar_eqb /=.
apply: (iffP andP) => [[/eqP -> /eqP ->] | [-> ->]] //.
Qed.

HB.instance Definition _ := hasDecEq.Build FVar FVar_eqP.

(** * Terms *)

Inductive Term : Type :=
  | TmFVar (v : FVar)
  | TmBVar (index : nat) (ty : HType)
  | TmConst (name : Name) (ty : HType)
  | TmComb (f x : Term)
  | TmAbs (arg_ty : HType) (body : Term).

(** [{fset Term}] ([Kernel.Thm]'s hypothesis set) needs [Term] to be a
    [choiceType].  Built, per the plan, via mathcomp's [GenTree] module --
    the standard idiom for giving a recursive type with self-valued
    fields a [choiceType] instance, rather than a bespoke encoding --
    encoding into [GenTree.tree nat] (atomic [Name]/[nat] data via
    [GenTree.Leaf], each constructor as a tagged [GenTree.Node]).
    [HType] is embedded the same way; it needs no [choiceType] instance
    of its own for anything else in this development, so this encoding
    is the only place [HType]'s [GenTree] round-trip is used.  This one
    instance gives [Term] its [eqType]/[choiceType]/[countType] together
    (so [==] on [Term] is defined via this encoding, not a separately
    hand-rolled comparison). *)
Fixpoint HType_to_tree (t : HType) : GenTree.tree nat :=
  match t with
  | HTyVar n => GenTree.Leaf (Name_to_nat n)
  | HTyApp n args => GenTree.Node (Name_to_nat n) (map HType_to_tree args)
  end.

Fixpoint tree_to_HType (t : GenTree.tree nat) : HType :=
  match t with
  | GenTree.Leaf k => HTyVar (nat_to_Name k)
  | GenTree.Node lbl args => HTyApp (nat_to_Name lbl) (map tree_to_HType args)
  end.

Lemma HType_treeK : cancel HType_to_tree tree_to_HType.
Proof.
elim/HType_rect => [n | n args IH] /=.
- by rewrite Name_natK.
- rewrite Name_natK; congr HTyApp.
  elim: args IH => [|x xs IHxs] //= [-> Pxs].
  by rewrite (IHxs Pxs).
Qed.

Fixpoint Term_to_tree (t : Term) : GenTree.tree nat :=
  match t with
  | TmFVar v =>
      GenTree.Node 0 [:: GenTree.Leaf (Name_to_nat (fv_name v)); HType_to_tree (fv_ty v)]
  | TmBVar i ty => GenTree.Node 1 [:: GenTree.Leaf i; HType_to_tree ty]
  | TmConst n ty => GenTree.Node 2 [:: GenTree.Leaf (Name_to_nat n); HType_to_tree ty]
  | TmComb f x => GenTree.Node 3 [:: Term_to_tree f; Term_to_tree x]
  | TmAbs aty b => GenTree.Node 4 [:: HType_to_tree aty; Term_to_tree b]
  end.

Fixpoint tree_to_Term (t : GenTree.tree nat) : Term :=
  match t with
  | GenTree.Node 0 [:: GenTree.Leaf nk; tyt] =>
      TmFVar (mkFVar (nat_to_Name nk) (tree_to_HType tyt))
  | GenTree.Node 1 [:: GenTree.Leaf i; tyt] => TmBVar i (tree_to_HType tyt)
  | GenTree.Node 2 [:: GenTree.Leaf nk; tyt] => TmConst (nat_to_Name nk) (tree_to_HType tyt)
  | GenTree.Node 3 [:: ft; xt] => TmComb (tree_to_Term ft) (tree_to_Term xt)
  | GenTree.Node 4 [:: atyt; bt] => TmAbs (tree_to_HType atyt) (tree_to_Term bt)
  | _ => TmConst NBool bool_ty (* unreachable: not in the image of [Term_to_tree] *)
  end.

Lemma Term_treeK : cancel Term_to_tree tree_to_Term.
Proof.
elim=> [v | i ty | n ty | f IHf x IHx | aty b IHb] /=.
- by rewrite Name_natK HType_treeK; case: v.
- by rewrite HType_treeK.
- by rewrite Name_natK HType_treeK.
- by rewrite IHf IHx.
- by rewrite HType_treeK IHb.
Qed.

HB.instance Definition _ := Countable.copy Term (can_type Term_treeK).

(** * Smart constructors *)

Definition mk_var (n : Name) (ty : HType) : FVar := mkFVar n ty.
Definition mk_const (n : Name) (ty : HType) : Term := TmConst n ty.

(** Total, meaningful only on a well-typed application -- the only type
    check [term.rhm] performs in this layer; [Kernel.check_open_term]'s
    [TmComb] case re-derives exactly the same condition as part of
    well-formedness, so nothing is lost by not gating construction here
    (see the [Kernel.Thm]/[Theory] sealing note for the general argument:
    no proof below can be fed a term that skipped this check and still
    satisfy a [WellFormedTerm] premise). *)
Definition mk_comb (func arg : Term) : Term := TmComb func arg.

Fixpoint type_of (t : Term) : HType :=
  match t with
  | TmFVar v => fv_ty v
  | TmBVar _ ty => ty
  | TmConst _ ty => ty
  | TmAbs aty body => mk_fun aty (type_of body)
  | TmComb f _ =>
      let fty := type_of f in
      if is_fun fty then (dest_fun fty).2 else bool_ty
  end.

Definition dest_comb (t : Term) : Term * Term :=
  match t with
  | TmComb f x => (f, x)
  | _ => (t, t)
  end.

(** * The locally nameless primitives *)

(** [d] ranges over all of [Z] ([term.rhm]'s [d :: Int]): [subst_at] shifts
    up by a nonnegative amount, [subst_bvar] shifts down by exactly [1].
    [kernel.rhm] raises "shift would produce a negative index" on an
    out-of-range shift; matching [idris-hol-kernel]'s own documented,
    harmless divergence on this point, [Z.to_nat] clamps a negative result
    to [0] instead of erroring.  Unreachable through the kernel's own
    checked paths -- [BETA] calls [check_term] first, which is what rules
    out the only shift that could go negative. *)
Fixpoint shift (d : Z) (cutoff : nat) (t : Term) : Term :=
  match t with
  | TmBVar i ty =>
      if i < cutoff then t else TmBVar (Z.to_nat (Z.of_nat i + d)) ty
  | TmComb f x => TmComb (shift d cutoff f) (shift d cutoff x)
  | TmAbs aty b => TmAbs aty (shift d cutoff.+1 b)
  | _ => t
  end.

Fixpoint subst_at (j : nat) (s t : Term) : Term :=
  match t with
  | TmBVar i _ => if i == j then shift (Z.of_nat j) 0 s else t
  | TmComb f x => TmComb (subst_at j s f) (subst_at j s x)
  | TmAbs aty b => TmAbs aty (subst_at j.+1 s b)
  | _ => t
  end.

(** Replace the innermost bound variable by [s], closing up the indices
    above it.  This is the whole of beta reduction, and it cannot capture
    anything. *)
Definition subst_bvar (s body : Term) : Term := shift (-1) 0 (subst_at 0 s body).

Fixpoint abstract_at (j : nat) (v : FVar) (t : Term) : Term :=
  match t with
  | TmFVar w => if w == v then TmBVar j (fv_ty v) else t
  | TmComb f x => TmComb (abstract_at j v f) (abstract_at j v x)
  | TmAbs aty b => TmAbs aty (abstract_at j.+1 v b)
  | _ => t
  end.

(** Turn every occurrence of the free variable [v] into a bound one, ready
    to be wrapped in a [TmAbs]. *)
Definition abstract_fvar (v : FVar) (body : Term) : Term := abstract_at 0 v body.

(** [\v. body], with [v]'s occurrences turned into [TmBVar 0]. *)
Definition mk_abs (v : FVar) (body : Term) : Term :=
  TmAbs (fv_ty v) (abstract_fvar v body).

(** Open an abstraction with a specific free variable.  Total: on a
    non-[TmAbs] argument it returns [t] unchanged, the same
    meaningful-only-under-a-precondition pattern as [type_of]. *)
Definition open_abs (v : FVar) (t : Term) : Term :=
  match t with
  | TmAbs _ body => subst_bvar (TmFVar v) body
  | _ => t
  end.

(** * Instantiation *)

(** [theta] is a list of [(replacement, variable)] pairs, applied
    simultaneously; the *first* entry matching a given variable wins, so a
    list with a shadowed duplicate entry has defined, order-dependent
    behaviour -- exactly [kernel.rhm]'s contract for [INST].  Represented
    as [seq (Term * FVar)], not [{fmap FVar -> Term}], because a finmap
    would silently discard that "first entry wins" semantics.  Dropped:
    the [===]-based short-circuit [kernel.rhm] uses purely to skip
    rebuilding an unchanged subtree; it changes no result, and Coq terms
    have no observable identity to exploit for it, so this port always
    rebuilds. *)
Fixpoint inst_fvar_lookup (theta : seq (Term * FVar)) (v : FVar) (depth : nat)
    : option Term :=
  match theta with
  | [::] => None
  | (rep, x) :: rest =>
      if x == v then Some (if depth == 0 then rep else shift (Z.of_nat depth) 0 rep)
      else inst_fvar_lookup rest v depth
  end.

Fixpoint inst_fvar_go (theta : seq (Term * FVar)) (t : Term) (depth : nat) : Term :=
  match t with
  | TmFVar v => odflt t (inst_fvar_lookup theta v depth)
  | TmComb f x => TmComb (inst_fvar_go theta f depth) (inst_fvar_go theta x depth)
  | TmAbs aty b => TmAbs aty (inst_fvar_go theta b depth.+1)
  | _ => t
  end.

Definition inst_fvar (theta : seq (Term * FVar)) (tm : Term) : Term :=
  inst_fvar_go theta tm 0.

(** Substitute for type variables throughout a term.  Two distinct free
    variables can be merged by this ([x :: 'a] and [x :: num] become the
    same variable when ['a := num]) -- standard HOL behaviour, and sound.
    A bound variable colliding with a free one, the case that ordinarily
    needs capture repair, cannot happen: bound variables have no names. *)
Fixpoint inst_type (tyin : {fmap Name -> HType}) (tm : Term) : Term :=
  match tm with
  | TmFVar v => TmFVar (mkFVar (fv_name v) (type_subst tyin (fv_ty v)))
  | TmBVar i ty => TmBVar i (type_subst tyin ty)
  | TmConst n ty => TmConst n (type_subst tyin ty)
  | TmComb f x => TmComb (inst_type tyin f) (inst_type tyin x)
  | TmAbs aty b => TmAbs (type_subst tyin aty) (inst_type tyin b)
  end.

(** No [TmBVar] index may escape its binder.  A term that fails this has
    no meaning; the kernel rejects it. *)
Fixpoint is_locally_closed_go (depth : nat) (t : Term) : bool :=
  match t with
  | TmBVar i _ => i < depth
  | TmComb f x => is_locally_closed_go depth f && is_locally_closed_go depth x
  | TmAbs _ b => is_locally_closed_go depth.+1 b
  | _ => true
  end.

Definition is_locally_closed (t : Term) : bool := is_locally_closed_go 0 t.

(** * Free variables *)

Fixpoint vfree_in (v : FVar) (t : Term) : bool :=
  match t with
  | TmFVar w => v == w
  | TmComb f x => vfree_in v f || vfree_in v x
  | TmAbs _ b => vfree_in v b
  | _ => false
  end.

(** Left-to-right order of first occurrence, without duplicates.  The
    order is part of the contract: generated axioms depend on it. *)
Fixpoint free_vars_acc (acc : seq FVar) (t : Term) : seq FVar :=
  match t with
  | TmFVar v => if v \in acc then acc else rcons acc v
  | TmComb f x => free_vars_acc (free_vars_acc acc f) x
  | TmAbs _ b => free_vars_acc acc b
  | _ => acc
  end.

Definition free_vars (t : Term) : seq FVar := free_vars_acc [::] t.

(** All type variable names occurring anywhere in [t] -- its own leaves'
    types ([FVar]/[BVar]/[Const]) and every binder's argument type --
    left-to-right, first-occurrence order, no duplicates.  Used by
    [new_basic_definition]'s "the body is no more polymorphic than its
    declared type" check and by [new_basic_type_definition]'s analogous
    check on the predicate. *)
Fixpoint term_type_vars_acc (acc : seq Name) (t : Term) : seq Name :=
  match t with
  | TmFVar v => type_vars_acc acc (fv_ty v)
  | TmBVar _ ty => type_vars_acc acc ty
  | TmConst _ ty => type_vars_acc acc ty
  | TmComb f x => term_type_vars_acc (term_type_vars_acc acc f) x
  | TmAbs aty b => term_type_vars_acc (type_vars_acc acc aty) b
  end.

Definition term_type_vars (t : Term) : seq Name := term_type_vars_acc [::] t.

(** A variant of [v] free in none of [avoid].  [kernel.rhm]'s own
    [fresh_for]/[variant] search increasing numeric suffixes on [v]'s
    *printed* name; [Name] has none, so (matching the [fresh_for] note
    below) this picks a numeric id strictly above every free variable's id
    across [avoid] in one step, rather than searching -- fresh by
    construction, not merely by convention. *)
Definition variant (avoid : seq Term) (v : FVar) : FVar :=
  if has (vfree_in v) avoid then
    let bump :=
      addn 1 (foldr (fun t acc =>
                    foldr (fun w a => maxn (Name_to_nat (fv_name w)) a)
                          acc (free_vars t))
                 0 avoid)
    in mkFVar (NUser bump) (fv_ty v)
  else v.

(** * Opening with a fresh variable *)

(** The name to give a binder being opened.  [kernel.rhm]'s own
    [fresh_for] picks the first of a fixed, readable name list not already
    free in the body, in lockstep with [printer.rhm]'s own naming policy
    ("the same policy the printer uses, so that a variable a user sees in
    a residue matches the one [SPEC_ALL] produces").  [printer.rhm] is out
    of scope here (see the README), and [dest_abs]'s *logical* content --
    open an abstraction with *some* fresh variable, whatever its name --
    does not depend on which name is picked, so this port uses a plain
    incrementing derivation instead: strictly greater than every free
    variable's id in the body, hence fresh by construction.  No proof
    below inspects *which* fresh name [dest_abs] picks, only that it is
    fresh. *)
Definition fresh_for (body : Term) (ty : HType) : FVar :=
  let bump := addn 1 (foldr (fun w a => maxn (Name_to_nat (fv_name w)) a)
                         0 (free_vars body))
  in mkFVar (NUser bump) ty.


(** Open an abstraction with a fresh variable. *)
Definition dest_abs (t : Term) : FVar * Term :=
  match t with
  | TmAbs aty body =>
      let v := fresh_for body aty in (v, subst_bvar (TmFVar v) body)
  | _ => (mkFVar NAlpha bool_ty, t)
  end.

(** * Deterministic ordering *)

Definition Term_rank (t : Term) : nat :=
  match t with
  | TmConst _ _ => 0
  | TmFVar _ => 1
  | TmBVar _ _ => 2
  | TmComb _ _ => 3
  | TmAbs _ _ => 4
  end.

(** A deterministic ordering on terms, for display and for orienting
    permutative rewrites -- not an equality test (use [==]).  Applies the
    [idris-hol-kernel]-discovered termination fix from the start: match
    directly on the two original arguments, never on a freshly built
    pair, so Coq's guard checker accepts the structural descent without
    [Program Fixpoint]/[Equations].  Unlike [kernel.rhm]'s own [term_ord]
    -- which compares names by print name and is therefore only a
    preorder -- comparing via [Name_cmp] (see [Names.v]) makes this a
    genuine total order: [term_ord a b = Eq -> a = b]
    ([term_ord_antisym] below). *)
Fixpoint term_ord (a b : Term) : comparison :=
  match Nat.compare (Term_rank a) (Term_rank b) with
  | Eq =>
      match a, b with
      | TmFVar v1, TmFVar v2 =>
          match Name_cmp (fv_name v1) (fv_name v2) with
          | Eq => type_ord (fv_ty v1) (fv_ty v2)
          | c => c
          end
      | TmConst n1 t1, TmConst n2 t2 =>
          match Name_cmp n1 n2 with
          | Eq => type_ord t1 t2
          | c => c
          end
      | TmBVar i1 t1, TmBVar i2 t2 =>
          match Nat.compare i1 i2 with
          | Eq => type_ord t1 t2
          | c => c
          end
      | TmComb f1 x1, TmComb f2 x2 =>
          match term_ord f1 f2 with
          | Eq => term_ord x1 x2
          | c => c
          end
      | TmAbs a1 b1, TmAbs a2 b2 =>
          match type_ord a1 a2 with
          | Eq => term_ord b1 b2
          | c => c
          end
      | _, _ => Eq (* unreachable: equal rank forces the same constructor *)
      end
  | c => c
  end.

Lemma term_ord_antisym a b : term_ord a b = Eq -> a = b.
Proof.
elim: a b => [v1 | i1 t1 | n1 t1 | f1 IHf x1 IHx | a1 b1 IHb]
             [v2 | i2 t2 | n2 t2 | f2 x2 | a2 b2] /=; try discriminate.
- case En: (Name_cmp (fv_name v1) (fv_name v2)) => //.
  move/Name_cmp_eq: En => Hn /type_ord_antisym Ht.
  by case: v1 v2 Hn Ht => [n1 t1] [n2 t2] /= -> ->.
- case Ei: (Nat.compare i1 i2) => // Hi.
  have {Ei} -> := proj1 (Nat.compare_eq_iff _ _) Ei.
  move: Hi => /type_ord_antisym ->; by [].
- case En: (Name_cmp n1 n2) => //.
  move/Name_cmp_eq: En => -> /type_ord_antisym ->; by [].
- case Ef: (term_ord f1 f2) => //.
  move/IHf: Ef => -> /IHx ->; by [].
- case Ea: (type_ord a1 a2) => //.
  move/type_ord_antisym: Ea => -> /IHb ->; by [].
Qed.

Corollary term_ord_refl a : term_ord a a = Eq.
Proof.
elim: a => [v | i t | n t | f IHf x IHx | at' bd IHbd] /=.
- by rewrite Name_cmp_refl type_ord_refl.
- by rewrite Nat.compare_refl type_ord_refl.
- by rewrite Name_cmp_refl type_ord_refl.
- by rewrite IHf IHx.
- by rewrite type_ord_refl IHbd.
Qed.

(** * Beta *)

Definition is_beta_redex (t : Term) : bool :=
  match t with
  | TmComb (TmAbs _ _) _ => true
  | _ => false
  end.

(** Raw, unjustified beta reduction.  The kernel's [BETA] rule is what
    turns this into a theorem; nothing else should call it to "prove"
    anything.  Total; meaningful only when [is_beta_redex] holds. *)
Definition beta_reduce (t : Term) : Term :=
  match t with
  | TmComb (TmAbs _ body) arg => subst_bvar arg body
  | _ => t
  end.

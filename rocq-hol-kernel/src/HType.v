(** HOL types.

    Transliteration of [rhombus-hol-kernel/rhombus/hol/htype.rhm].  Two
    constructors, HOL Light style: type variables and applications of a
    type constructor to arguments.  The function type is not special-cased
    -- it is just [HTyApp NFun [dom; rng]] -- and constructor arities live
    in the theory ([Kernel.v]), not in the type.

    [args : seq HType] makes [HType] a "nested" inductive (a constructor
    carries a list of the very type being defined), so Coq's own
    auto-derived induction principle gives no induction hypothesis about
    the elements of [args] at all.  [HType_rect] below supplies one, built
    exactly the way mathcomp's own [GenTree.tree] (boot/choice.v) --
    literally the same shape, [Leaf of T | Node of nat & seq tree] --
    builds its [tree_rect]/[tree_ind]: a fixpoint whose [HTyApp] branch
    runs a nested, internal fixpoint over [args] that calls back into the
    outer one on each element, which is a subterm of the original
    argument throughout. *)

From mathcomp Require Import all_boot finmap.
From HB Require Import structures.
From Stdlib Require Import PeanoNat.
From RocqHolKernel Require Import Names.

Open Scope fmap_scope.
Open Scope fset_scope.

Unset Elimination Schemes.
Inductive HType : Type :=
  | HTyVar (n : Name)
  | HTyApp (n : Name) (args : seq HType).
Set Elimination Schemes.

Section Rect.
Variable P : HType -> Type.
Hypothesis Hvar : forall n, P (HTyVar n).
Hypothesis Happ : forall n args,
  foldr (fun t k => (P t * k)%type) unit args -> P (HTyApp n args).

Fixpoint HType_rect (t : HType) : P t :=
  match t with
  | HTyVar n => Hvar n
  | HTyApp n args =>
    Happ n args
      ((fix iter (l : seq HType) : foldr (fun t k => (P t * k)%type) unit l :=
          match l with
          | [::] => tt
          | t :: l' => (HType_rect t, iter l')
          end) args)
  end.
End Rect.

Definition HType_rec (P : HType -> Set) := @HType_rect P.

(** * Decidable, structural equality *)

Fixpoint HType_eqb (a b : HType) : bool :=
  match a, b with
  | HTyVar n1, HTyVar n2 => n1 == n2
  | HTyApp n1 args1, HTyApp n2 args2 =>
      (n1 == n2) &&
      ((fix eqseq (xs ys : seq HType) : bool :=
          match xs, ys with
          | [::], [::] => true
          | x :: xs', y :: ys' => HType_eqb x y && eqseq xs' ys'
          | _, _ => false
          end) args1 args2)
  | _, _ => false
  end.

(** A standalone name for the inner loop above, definitionally equal to
    it (both are the identical recursive term, up to the bound name of
    the fixpoint), so that [HType_eqb_app] below closes by [Logic.eq_refl]
    and the induction proof can name and generalize over it. *)
Definition eqseq_HType : seq HType -> seq HType -> bool :=
  fix eqseq (xs ys : seq HType) : bool :=
    match xs, ys with
    | [::], [::] => true
    | x :: xs', y :: ys' => HType_eqb x y && eqseq xs' ys'
    | _, _ => false
    end.

Lemma HType_eqb_app n1 args1 n2 args2 :
  HType_eqb (HTyApp n1 args1) (HTyApp n2 args2)
    = (n1 == n2) && eqseq_HType args1 args2.
Proof. by []. Qed.

Lemma HType_eqP : Equality.axiom HType_eqb.
Proof.
move=> a; elim/HType_rect: a => [n1 | n1 args1 IH] [n2 | n2 args2];
  try by constructor.
- rewrite [HType_eqb _ _]/=.
  case: eqP => [<-|neq]; first by constructor.
  by constructor=> [[]].
- rewrite HType_eqb_app.
  have Hseq : reflect (args1 = args2) (eqseq_HType args1 args2).
  { elim: args1 args2 IH => [|x xs IHxs] [|y ys] IH /=; try by constructor.
    case: IH => [Px Pxs].
    case: (Px y) => [<- | neqx]; last first.
    { constructor=> [[]] *; subst; exact: neqx. }
    case: (IHxs ys Pxs) => [<- | neqxs]; last first.
    { constructor=> [[]] *; subst; exact: neqxs. }
    by constructor. }
  case: eqP => [<- | neqn] /=; last first.
  { constructor=> [[]] *; subst; exact: neqn. }
  case: Hseq => [<- | neqa]; first by constructor.
  by constructor=> [[]] *; subst; exact: neqa.
Qed.

HB.instance Definition _ := hasDecEq.Build HType HType_eqP.

(** * Smart constructors *)

Definition mk_tyvar (n : Name) : HType := HTyVar n.
Definition mk_tyapp (n : Name) (args : seq HType) : HType := HTyApp n args.
Definition bool_ty : HType := mk_tyapp NBool [::].
Definition mk_fun (dom rng : HType) : HType := mk_tyapp NFun [:: dom; rng].

Definition is_fun (t : HType) : bool :=
  match t with
  | HTyApp n [:: _; _] => n == NFun
  | _ => false
  end.

(** Total, meaningful only when [is_fun] holds first -- the same
    "total function, meaningful only under a well-formedness
    precondition" pattern used throughout this port (see [Term.type_of]).
    [kernel.rhm]'s [dest_fun] raises when [t] is not a function type;
    every call site here checks [is_fun] first. *)
Definition dest_fun (t : HType) : HType * HType :=
  match t with
  | HTyApp n [:: dom; rng] => if n == NFun then (dom, rng) else (t, t)
  | _ => (t, t)
  end.

(** * Type variables *)

(** Left-to-right order of first occurrence, without duplicates; order
    matters (generated axioms depend on it), so this is *not* replaced by
    an [{fset Name}] -- see the representation discussion in the plan. *)
Fixpoint type_vars_acc (acc : seq Name) (t : HType) : seq Name :=
  match t with
  | HTyVar n => if n \in acc then acc else rcons acc n
  | HTyApp _ args => foldl type_vars_acc acc args
  end.

Definition type_vars (t : HType) : seq Name := type_vars_acc [::] t.

(** * Substitution *)

(** [kernel.rhm]'s [type_subst] short-circuits with [===] when nothing
    changed, purely so callers can skip rebuilding an unchanged subtree;
    it changes no result and no proof here depends on it, so (per the
    plan) this port always rebuilds. *)
Fixpoint type_subst (theta : {fmap Name -> HType}) (t : HType) : HType :=
  match t with
  | HTyVar n => odflt t theta.[? n]
  | HTyApp n args => HTyApp n (map (type_subst theta) args)
  end.

(** * One-way matching *)

(** Extends [acc] so that [type_subst result pat = t]; [None] when no
    such extension exists. *)
Fixpoint type_match (pat t : HType) (acc : {fmap Name -> HType})
    : option {fmap Name -> HType} :=
  match pat with
  | HTyVar n =>
      match acc.[? n] with
      | None => Some (acc.[n <- t])
      | Some prev => if prev == t then Some acc else None
      end
  | HTyApp n pargs =>
      match t with
      | HTyApp n2 targs =>
          if (n == n2) && (size pargs == size targs) then
            (fix loop (ps qs : seq HType) (a : {fmap Name -> HType})
                : option {fmap Name -> HType} :=
               match ps, qs with
               | [::], [::] => Some a
               | p :: ps', q :: qs' =>
                   match type_match p q a with
                   | None => None
                   | Some a2 => loop ps' qs' a2
                   end
               | _, _ => None
               end) pargs targs acc
          else None
      | _ => None
      end
  end.

(** * Occurrence check *)

Fixpoint type_occurs (n : Name) (t : HType) : bool :=
  match t with
  | HTyVar m => n == m
  | HTyApp _ args => has (type_occurs n) args
  end.

(** * Deterministic ordering *)

(** Unlike [kernel.rhm]'s own [type_ord] -- which compares constructor
    names with [<]/[>] on [Symbol], i.e. by *print name*, so its own
    comment records that [0] means only "the comparison cannot tell two
    types apart", not "equal" -- [type_ord] here compares [Name]s via
    [Name_cmp], which is faithful (see [Names.v]).  So [type_ord] is
    provably a genuine total order: [type_ord a b = Eq -> a = b]
    ([type_ord_antisym] below), strictly stronger than what [kernel.rhm]
    documents about its own comparison. *)
Fixpoint type_ord (a b : HType) : comparison :=
  match a, b with
  | HTyVar na, HTyVar nb => Name_cmp na nb
  | HTyVar _, HTyApp _ _ => Lt
  | HTyApp _ _, HTyVar _ => Gt
  | HTyApp na aargs, HTyApp nb bargs =>
      match Name_cmp na nb with
      | Eq =>
          match Nat.compare (size aargs) (size bargs) with
          | Eq =>
              (fix lex (xs ys : seq HType) : comparison :=
                 match xs, ys with
                 | [::], [::] => Eq
                 | x :: xs', y :: ys' =>
                     match type_ord x y with
                     | Eq => lex xs' ys'
                     | c => c
                     end
                 | _, _ => Eq
                 end) aargs bargs
          | c => c
          end
      | c => c
      end
  end.

Definition lex_HType : seq HType -> seq HType -> comparison :=
  fix lex (xs ys : seq HType) : comparison :=
    match xs, ys with
    | [::], [::] => Eq
    | x :: xs', y :: ys' =>
        match type_ord x y with
        | Eq => lex xs' ys'
        | c => c
        end
    | _, _ => Eq
    end.

Lemma type_ord_app na aargs nb bargs :
  type_ord (HTyApp na aargs) (HTyApp nb bargs)
    = match Name_cmp na nb with
      | Eq =>
          match Nat.compare (size aargs) (size bargs) with
          | Eq => lex_HType aargs bargs
          | c => c
          end
      | c => c
      end.
Proof. by []. Qed.

Lemma type_ord_refl a : type_ord a a = Eq.
Proof.
elim/HType_rect: a => [n | n args IH].
- exact: Name_cmp_refl.
- rewrite type_ord_app Name_cmp_refl Nat.compare_refl.
  elim: args IH => [|x xs IHxs] //= [Px Pxs].
  by rewrite /lex_HType -/lex_HType Px -/(lex_HType xs xs) IHxs.
Qed.

Lemma type_ord_antisym a b : type_ord a b = Eq -> a = b.
Proof.
elim/HType_rect: a b => [n1 | n1 args1 IH] [n2 | n2 args2].
- move=> /Name_cmp_eq ->; by [].
- move=> Hc; discriminate.
- move=> Hc; discriminate.
- rewrite type_ord_app.
  case En: (Name_cmp n1 n2) => //; move/Name_cmp_eq: En => ->.
  case Es: (Nat.compare (size args1) (size args2)) => //.
  have {}Es := proj1 (Nat.compare_eq_iff _ _) Es.
  move=> Hlex; congr HTyApp.
  elim: args1 args2 IH Es Hlex => [|x xs IHxs] [|y ys] //= IH Es.
  have {}Es : size xs = size ys := Nat.succ_inj _ _ Es.
  rewrite /lex_HType -/lex_HType.
  case Ex: (type_ord x y) => //.
  case: IH => [Px Pxs] Hlexs.
  have -> := Px y Ex.
  congr cons; exact: (IHxs ys Pxs Es Hlexs).
Qed.

Corollary type_ord_eq_iff a b : type_ord a b = Eq <-> a = b.
Proof.
split; first exact: type_ord_antisym.
by move=> ->; exact: type_ord_refl.
Qed.

Corollary type_ord_Eq_trans a b c :
  type_ord a b = Eq -> type_ord b c = Eq -> type_ord a c = Eq.
Proof.
move=> /type_ord_antisym -> /type_ord_antisym ->; exact: type_ord_refl.
Qed.

(** * Substitution commutes with matching

    [type_match]'s accumulator only ever grows by binding fresh pattern
    variables to their matched targets, and never overwrites an existing
    binding with a different value (a repeated pattern variable is
    checked for consistency, not blindly rebound -- see [type_match]'s
    own [HTyVar] case).  Consequently, if [acc'] already agrees with
    [acc] under a substitution [tyin] (in the sense below), then matching
    the same pattern against the [tyin]-instantiated target, starting
    from [acc'], succeeds whenever the original match against the
    original target, starting from [acc], succeeds -- and the two
    resulting accumulators agree under [tyin] the same way.  This is
    exactly what [INST_TYPE]'s [check_open_term] preservation needs for
    its [TmConst] case: a constant's use only has to satisfy [type_match]
    up to [isSome], but proving even that much for the instantiated type
    needs this full accumulator-tracking statement to go through the
    induction. *)
Lemma type_match_subst_isSome tyin pat :
  forall (ty : HType) (acc acc' m : {fmap Name -> HType}),
  (forall n, acc'.[? n] = omap (type_subst tyin) (acc.[? n])) ->
  type_match pat ty acc = Some m ->
  exists m', type_match pat (type_subst tyin ty) acc' = Some m' /\
    forall n, m'.[? n] = omap (type_subst tyin) (m.[? n]).
Proof.
elim/HType_rect: pat => [n | n pargs IH] ty acc acc' m Hrel Hm.
- move: Hm => /=.
  case E: (acc.[? n]) => [prev|].
  + case: (@eqP _ prev ty) => [Hpt | Hne] //= [Em].
    have Hacc' : acc'.[? n] = Some (type_subst tyin ty).
      by rewrite (Hrel n) E /= Hpt.
    exists acc'; split.
    * rewrite /= Hacc'.
      by case: (@eqP _ (type_subst tyin ty) (type_subst tyin ty)) => [_ | []].
    * by rewrite -Em.
  + move=> [Em].
    exists (acc'.[n <- type_subst tyin ty]); split.
    * have Hacc'2 : acc'.[? n] = None by rewrite (Hrel n) E.
      by rewrite /= Hacc'2.
    * move=> n0; case: (@eqP _ n0 n) => [-> | Hne0].
      - by rewrite fnd_set eqxx -Em fnd_set eqxx.
      - by rewrite fnd_set (negbTE (introN eqP Hne0)) -Em fnd_set
             (negbTE (introN eqP Hne0)) (Hrel n0).
- move: Hm.
  case: ty => [n2 | n2 targs] //=.
  case: (@andP (n == n2) (size pargs == size targs)) => [[Hn Hsz] | _] //=.
  move: IH targs Hsz acc acc' m Hrel.
  elim: pargs => [| p ps IHps].
  + move=> _ targs Hsz acc acc' m Hrel Hm.
    case: targs Hsz Hm => [| t ts] //= _ [<-].
    rewrite (eqP Hn) eqxx /=.
    exists acc'; split=> //.
  + move=> [Hp Hps] targs Hsz acc acc' m Hrel Hm.
    case: targs Hsz Hm => [| t ts] //= Hsz Hm.
    rewrite (eqP Hn) eqxx /=.
    have Hsz' : size ps == size ts.
      by move: Hsz => /eqP [] /eqP.
    move: Hm.
    case E: (type_match p t acc) => [a2|] // Hm.
    have [a2' [Ea2' Hrela2]] := Hp t acc acc' a2 Hrel E.
    rewrite Ea2'.
    have := IHps Hps ts Hsz' a2 a2' m Hrela2 Hm.
    move=> [m' [Em' Hrelm']].
    exists m'; split.
    * rewrite (eqP Hn) eqxx /= in Em'.
      by rewrite eqSS.
    * exact: Hrelm'.
Qed.

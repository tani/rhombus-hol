(** Canonical names of the logical constants and type constructors.

    Transliteration of [rhombus-hol-kernel/rhombus/hol/names.rhm] as far as
    the kernel/term/type layer is concerned: nothing in [kernel.rhm],
    [term.rhm] or [htype.rhm] inspects a name's *text*, only its identity, so
    [Name] carries no string.  Every name the kernel writes for itself gets
    its own constructor ([NFun], [NBool], [NEq], [NAlpha], [NRepVar]);
    every caller-supplied [Symbol] becomes [NUser n] for some [n].

    Consequence, stated explicitly: because [Name] has no separate "print
    form", the historical soundness bug this project actually hit --
    [term_ord(a,b) = 0] for two *distinct*, same-printing symbols, fixed in
    [kernel.rhm] and documented at length in its own comments and in
    [tests/kernel.rhm]'s "Soundness regressions" section -- cannot be
    *stated* in this representation: [Name] equality is already faithful.
    [Term.term_ord]/[HType.type_ord] are consequently provable *genuine*
    total orders here, strictly stronger than what [kernel.rhm] itself
    documents about its own comparison. *)

From mathcomp Require Import all_boot.
From HB Require Import structures.
From Stdlib Require Import PeanoNat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive Name : Type :=
  | NFun
  | NBool
  | NEq
  | NAlpha
  | NRepVar
  | NUser (id : nat).

(** A bijection with [nat], used only to register [Name] as a [choiceType]
    (mathcomp's finite maps/sets need one for their keys); it carries no
    other meaning. *)
Definition Name_to_nat (n : Name) : nat :=
  match n with
  | NFun => 0
  | NBool => 1
  | NEq => 2
  | NAlpha => 3
  | NRepVar => 4
  | NUser k => k + 5
  end.

Definition nat_to_Name (k : nat) : Name :=
  match k with
  | 0 => NFun
  | 1 => NBool
  | 2 => NEq
  | 3 => NAlpha
  | 4 => NRepVar
  | k'.+4.+1 => NUser k'
  end.

Lemma Name_natK : cancel Name_to_nat nat_to_Name.
Proof. by case=> [| | | | | k] //=; rewrite addnC. Qed.

(* [Name] is [eqType]/[choiceType]/[countType] by transport along the
   bijection above -- the standard mathcomp idiom (see [boot/choice.v],
   e.g. its own [bool]/[unit] instances via [Choice.copy _ (can_type _)])
   for lifting a type with a known injection into an already-classified
   type, here [nat]. *)
HB.instance Definition _ := Countable.copy Name (can_type Name_natK).

Lemma Name_eqP (a b : Name) : reflect (a = b) (a == b).
Proof. exact: eqP. Qed.

(** A deterministic total-order comparator on [Name], used by
    [HType.type_ord]/[Term.term_ord].  Unlike [kernel.rhm]'s own
    [symbol_ord] (which compares *print names* and can therefore return
    [Eq] for two distinct, same-printing symbols -- the historical
    soundness bug documented on [Name] above), [Name_cmp] compares the
    bijection with [nat] directly, so it is a genuine antisymmetric
    order: [Name_cmp a b = Eq -> a = b]. *)
Definition Name_cmp (a b : Name) : comparison :=
  Nat.compare (Name_to_nat a) (Name_to_nat b).

Lemma Name_cmp_eq a b : Name_cmp a b = Eq -> a = b.
Proof.
rewrite /Name_cmp => /Nat.compare_eq_iff eq_nat.
by rewrite -(Name_natK a) -(Name_natK b) eq_nat.
Qed.

Lemma Name_cmp_refl a : Name_cmp a a = Eq.
Proof. exact: Nat.compare_refl. Qed.

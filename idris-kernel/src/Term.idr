module Term
-- HOL terms, in locally nameless (de Bruijn) form, ported from
-- rhombus-hol-lib/rhombus/hol/private/term.rhm.
--
-- Variables are split in two.  `FVar` is a free variable: it has a name, and
-- it is what hypotheses, goals and instantiations talk about.  `BVar` is a
-- bound variable: it has no name, only a de Bruijn index counting outwards
-- from the innermost enclosing `Abs`.  Alpha-equivalence is therefore plain
-- structural equality.

import Data.List
import Data.Maybe
import Data.SortedMap
import HType

%default total


public export
data Term : Type where
  FVar : Name -> HType -> Term
  BVar : Nat -> HType -> Term
  Const : Name -> HType -> Term
  Comb : Term -> Term -> Term
  Abs : HType -> Term -> Term

export
Eq Term where
  FVar n1 t1   == FVar n2 t2   = n1 == n2 && t1 == t2
  BVar i1 t1   == BVar i2 t2   = i1 == i2 && t1 == t2
  Const n1 t1  == Const n2 t2  = n1 == n2 && t1 == t2
  Comb f1 x1   == Comb f2 x2   = f1 == f2 && x1 == x2
  Abs t1 b1    == Abs t2 b2    = t1 == t2 && b1 == b2
  _            == _            = False

-- -- construction ------------------------------------------------------------

export
mkVar : Name -> HType -> Term
mkVar = FVar

export
mkConst : Name -> HType -> Term
mkConst = Const

public export
typeOf : Term -> Either String HType
typeOf (FVar _ ty)   = Right ty
typeOf (BVar _ ty)   = Right ty
typeOf (Const _ ty)  = Right ty
typeOf (Abs aty body) = map (mkFun aty) (typeOf body)
typeOf (Comb f _)    = do
  fty <- typeOf f
  case destFun fty of
    Right (_, rng) => Right rng
    Left err        => Left err

-- The only type check in the term layer: an application must be a function
-- applied to something of its domain type.
export
mkComb : Term -> Term -> Either String Term
mkComb func arg = do
  fty <- typeOf func
  if not (isFun fty)
    then Left ("operator is not a function: " ++ show fty)
    else do
      (dom, _) <- destFun fty
      aty <- typeOf arg
      if dom == aty
        then Right (Comb func arg)
        else Left "operand type does not match operator domain"

-- -- locally nameless primitives ----------------------------------------------

-- Add `d` to every `BVar` index at or above `cutoff`.
public export
shift : Integer -> Nat -> Term -> Term
shift d cutoff tm@(BVar i ty) =
  if i < cutoff
    then tm
    else BVar (integerToNat (natToInteger i + d)) ty
shift d cutoff (Comb f x)   = Comb (shift d cutoff f) (shift d cutoff x)
shift d cutoff (Abs aty b)  = Abs aty (shift d (S cutoff) b)
shift _ _ tm                = tm

-- -- soundness proof: `shift` never changes a term's type ---------------
--
-- `shift` only ever rewrites a `BVar`'s de Bruijn *index*; it never touches
-- a type annotation anywhere in the term (`ty` on `FVar`/`BVar`/`Const`,
-- `arg_ty` on `Abs`). `typeOf`, in turn, never inspects a `BVar`'s index at
-- all -- it just returns the annotation stored on whichever node it's at.
-- So `typeOf` is unconditionally invariant under `shift`, with no
-- well-formedness hypothesis needed (unlike the substitution lemmas this
-- sets up, which do need one -- a `BVar`'s annotation only reflects reality
-- once `checkOpenTerm`'s `env` has confirmed it).
export
shiftPreservesType : (d : Integer) -> (cutoff : Nat) -> (t : Term) ->
                      typeOf (shift d cutoff t) = typeOf t
shiftPreservesType d cutoff (FVar n ty) = Refl
shiftPreservesType d cutoff (Const n ty) = Refl
shiftPreservesType d cutoff (BVar i ty) with (i < cutoff)
  shiftPreservesType d cutoff (BVar i ty) | False = Refl
  shiftPreservesType d cutoff (BVar i ty) | True = Refl
shiftPreservesType d cutoff (Comb f x) =
  -- `typeOf`'s `Comb` case only ever inspects `f`'s type -- `x`'s type is
  -- checked elsewhere (`checkOpenTerm`/`mkComb`), not by `typeOf` itself.
  -- `cong` here, rather than `rewrite`, sidesteps `rewrite`'s
  -- occurrence-finding needing to see through both `shift`'s and
  -- `typeOf`'s unfolding at once to spot the rewritable subterm.
  cong (\ety => ety >>= (\fty => case destFun fty of
                                    Right (_, rng) => Right rng
                                    Left err => Left err))
       (shiftPreservesType d cutoff f)
shiftPreservesType d cutoff (Abs aty b) =
  rewrite shiftPreservesType d (S cutoff) b in Refl

public export
substAt : Nat -> Term -> Term -> Term
substAt j s t@(BVar i _) = if i == j then shift (natToInteger j) 0 s else t
substAt j s (Comb f x)   = Comb (substAt j s f) (substAt j s x)
substAt j s (Abs aty b)  = Abs aty (substAt (S j) s b)
substAt _ _ t            = t

-- Replace the innermost bound variable by `s`, closing up the indices above
-- it.  This is the whole of beta reduction, and it cannot capture anything.
public export
substBvar : Term -> Term -> Term
substBvar s body = shift (-1) 0 (substAt 0 s body)

-- `Eq Term` is sound: terms that compare equal are equal.  Structural, so
-- no axiom of its own beyond the `String` ones `nameEqSound` and the
-- `HType`/`Nat` soundness lemmas already rest on.
export
termEqSound : (a, b : Term) -> a == b = True -> a = b
termEqSound (FVar n1 t1) (FVar n2 t2) prf =
  let (pn, pt) = andTrueBoth (n1 == n2) (t1 == t2) prf in
  rewrite nameEqSound n1 n2 pn in rewrite htypeEqSound t1 t2 pt in Refl
termEqSound (BVar i1 t1) (BVar i2 t2) prf =
  let (pi, pt) = andTrueBoth (i1 == i2) (t1 == t2) prf in
  rewrite natEqSound i1 i2 pi in rewrite htypeEqSound t1 t2 pt in Refl
termEqSound (Const n1 t1) (Const n2 t2) prf =
  let (pn, pt) = andTrueBoth (n1 == n2) (t1 == t2) prf in
  rewrite nameEqSound n1 n2 pn in rewrite htypeEqSound t1 t2 pt in Refl
termEqSound (Comb f1 x1) (Comb f2 x2) prf =
  let (pf, px) = andTrueBoth (f1 == f2) (x1 == x2) prf in
  rewrite termEqSound f1 f2 pf in rewrite termEqSound x1 x2 px in Refl
termEqSound (Abs t1 b1) (Abs t2 b2) prf =
  let (pt, pb) = andTrueBoth (t1 == t2) (b1 == b2) prf in
  rewrite htypeEqSound t1 t2 pt in rewrite termEqSound b1 b2 pb in Refl
termEqSound (FVar _ _) (BVar _ _) prf = absurd prf
termEqSound (FVar _ _) (Const _ _) prf = absurd prf
termEqSound (FVar _ _) (Comb _ _) prf = absurd prf
termEqSound (FVar _ _) (Abs _ _) prf = absurd prf
termEqSound (BVar _ _) (FVar _ _) prf = absurd prf
termEqSound (BVar _ _) (Const _ _) prf = absurd prf
termEqSound (BVar _ _) (Comb _ _) prf = absurd prf
termEqSound (BVar _ _) (Abs _ _) prf = absurd prf
termEqSound (Const _ _) (FVar _ _) prf = absurd prf
termEqSound (Const _ _) (BVar _ _) prf = absurd prf
termEqSound (Const _ _) (Comb _ _) prf = absurd prf
termEqSound (Const _ _) (Abs _ _) prf = absurd prf
termEqSound (Comb _ _) (FVar _ _) prf = absurd prf
termEqSound (Comb _ _) (BVar _ _) prf = absurd prf
termEqSound (Comb _ _) (Const _ _) prf = absurd prf
termEqSound (Comb _ _) (Abs _ _) prf = absurd prf
termEqSound (Abs _ _) (FVar _ _) prf = absurd prf
termEqSound (Abs _ _) (BVar _ _) prf = absurd prf
termEqSound (Abs _ _) (Const _ _) prf = absurd prf
termEqSound (Abs _ _) (Comb _ _) prf = absurd prf

public export
abstractAt : Nat -> Term -> Term -> Term
abstractAt j v t@(FVar _ vty) = if t == v then BVar j vty else t
abstractAt j v (Comb f x)     = Comb (abstractAt j v f) (abstractAt j v x)
abstractAt j v (Abs aty b)    = Abs aty (abstractAt (S j) v b)
abstractAt _ _ t              = t

-- Abstraction cannot change a type either: it swaps an `FVar` for a `BVar`
-- carrying *that same annotation* (`t@(FVar _ vty)` -> `BVar j vty`), so
-- like `shift` it is invisible to `typeOf` -- and, again like `shift`, this
-- needs no hypothesis at all.
export
abstractPreservesType : (j : Nat) -> (v : Term) -> (t : Term) ->
                         typeOf (abstractAt j v t) = typeOf t
abstractPreservesType j v (FVar n ty) with (FVar n ty == v)
  abstractPreservesType j v (FVar n ty) | True = Refl
  abstractPreservesType j v (FVar n ty) | False = Refl
abstractPreservesType j v (BVar _ _) = Refl
abstractPreservesType j v (Const _ _) = Refl
abstractPreservesType j v (Comb f x) =
  cong (\ety => ety >>= (\fty => case destFun fty of
                                    Right (_, rng) => Right rng
                                    Left err => Left err))
       (abstractPreservesType j v f)
abstractPreservesType j v (Abs aty b) =
  rewrite abstractPreservesType (S j) v b in Refl

-- Turn every occurrence of the free variable `v` into a bound one, ready to
-- be wrapped in an `Abs`.  `v` must be an `FVar`; callers are the smart
-- constructors below.
public export
abstractFvar : Term -> Term -> Term
abstractFvar v body = abstractAt 0 v body

-- `\v. body`, with `v`'s occurrences turned into `BVar 0`.
public export
mkAbs : Term -> Term -> Either String Term
mkAbs v@(FVar _ vty) body = Right (Abs vty (abstractFvar v body))
mkAbs _ _                 = Left "mkAbs: not a free variable"

-- Substitute for free variables.  `theta` is a list of `(replacement,
-- variable)` pairs, applied simultaneously.
-- The two workers are top-level rather than `where`-local so the proofs
-- below can talk about them; the behaviour is exactly what the nested
-- version had.
public export
instFvarLookup : List (Term, Term) -> Term -> Nat -> Maybe Term
instFvarLookup [] v depth = Nothing
instFvarLookup ((rep, x) :: rest) v depth =
  if x == v
    then Just (if depth == 0 then rep else shift (natToInteger depth) 0 rep)
    else instFvarLookup rest v depth

public export
instFvarGo : List (Term, Term) -> Term -> Nat -> Term
instFvarGo theta t@(FVar _ _) depth = fromMaybe t (instFvarLookup theta t depth)
instFvarGo theta (Comb f x) depth   = Comb (instFvarGo theta f depth) (instFvarGo theta x depth)
instFvarGo theta (Abs aty b) depth  = Abs aty (instFvarGo theta b (S depth))
instFvarGo theta t _                = t

public export
instFvar : List (Term, Term) -> Term -> Term
instFvar [] tm = tm
instFvar theta tm = instFvarGo theta tm 0

-- Substitute for type variables throughout a term.
-- Worker lifted out of a `where` so the proofs can reason about it.  It
-- calls `typeSubst'` rather than `typeSubst`: identical whenever `tyin` is
-- non-empty (which is the only way `instType` calls it), and identical on
-- the empty substitution too, but without the `null` test that would not
-- reduce for an abstract `tyin` in a proof.
public export
instTypeGo : List (Name, HType) -> Term -> Term
instTypeGo tyin (FVar n ty)   = FVar n (typeSubst' tyin ty)
instTypeGo tyin (BVar i ty)   = BVar i (typeSubst' tyin ty)
instTypeGo tyin (Const n ty)  = Const n (typeSubst' tyin ty)
instTypeGo tyin (Comb f x)    = Comb (instTypeGo tyin f) (instTypeGo tyin x)
instTypeGo tyin (Abs aty b)   = Abs (typeSubst' tyin aty) (instTypeGo tyin b)

public export
instType : List (Name, HType) -> Term -> Term
instType tyin tm = if null tyin then tm else instTypeGo tyin tm

-- No `BVar` index may escape its binder, counting from `depth` binders
-- already in scope.  A top-level (`depth = 0`) term is *locally closed*.
--
-- This is a top-level definition rather than `isLocallyClosed`'s local
-- `where` helper so the substitution lemmas below can state properties
-- about the very function `isLocallyClosed` calls, at an arbitrary depth --
-- the induction descends under binders, so it has to talk about depths
-- other than 0.
public export
closedAt : Nat -> Term -> Bool
closedAt depth (BVar i _) = i < depth
closedAt depth (Comb f x) = closedAt depth f && closedAt depth x
closedAt depth (Abs _ b)  = closedAt (S depth) b
closedAt _ _              = True

export
isLocallyClosed : Term -> Bool
isLocallyClosed t = closedAt 0 t

-- -- soundness proofs: substitution preserves local closedness -----------
--
-- `BETA` rewrites `Comb (Abs ty body) arg` to `substBvar arg body` without
-- re-checking the result.  These lemmas establish that it need not: the
-- reduct of a locally closed redex is locally closed, so beta reduction can
-- never manufacture the "dangling de Bruijn index" the Rhombus kernel's
-- comment calls "a term with no meaning at all".
--
-- Everything here stays clear of `shift`'s `Integer` arithmetic on
-- indices.  That is not an accident: `shiftClosedId` shows `shift` is the
-- *identity* on a term already closed at the cutoff (every `BVar` takes the
-- `i < cutoff` branch, which returns the node untouched), and the two
-- places the BETA proof shifts anything are both of that shape.  So no
-- reasoning about `integerToNat (natToInteger i + d)` -- which would need
-- axioms about primitive `Integer` operations -- is required anywhere.

ltWeakenSucc : (i, d : Nat) -> i < d = True -> i < S d = True
ltWeakenSucc Z     Z     prf = absurd prf
ltWeakenSucc Z     (S _) prf = Refl
ltWeakenSucc (S _) Z     prf = absurd prf
ltWeakenSucc (S i) (S d) prf = ltWeakenSucc i d prf

-- `i < S j` and `i /= j` force `i < j`: the only index below `S j` that is
-- not below `j` is `j` itself.
export
ltSuccNeq : (i, j : Nat) -> i < S j = True -> i == j = False -> i < j = True
ltSuccNeq Z         Z     lt neq = absurd neq
ltSuccNeq Z         (S _) lt neq = Refl
-- `i < Z` is only definitionally `False` once `i`'s own constructor is
-- known, so this case needs one more split than the others.
ltSuccNeq (S Z)     Z     lt neq = absurd lt
ltSuccNeq (S (S _)) Z     lt neq = absurd lt
ltSuccNeq (S i)     (S j) lt neq = ltSuccNeq i j lt neq

-- Closedness only ever gets easier as more binders come into scope.
export
closedAtMono : (d : Nat) -> (t : Term) -> closedAt d t = True -> closedAt (S d) t = True
closedAtMono d (FVar _ _) prf = Refl
closedAtMono d (Const _ _) prf = Refl
closedAtMono d (BVar i _) prf = ltWeakenSucc i d prf
closedAtMono d (Comb f x) prf =
  let (pf, px) = andTrueBoth (closedAt d f) (closedAt d x) prf in
  rewrite closedAtMono d f pf in
  rewrite closedAtMono d x px in Refl
closedAtMono d (Abs aty b) prf = closedAtMono (S d) b prf

export
closedAtFromZero : (d : Nat) -> (t : Term) -> closedAt 0 t = True -> closedAt d t = True
closedAtFromZero Z     t prf = prf
closedAtFromZero (S d) t prf = closedAtMono d t (closedAtFromZero d t prf)

-- `shift` is the identity on a term with nothing loose at the cutoff.
export
shiftClosedId : (d : Integer) -> (cutoff : Nat) -> (t : Term) ->
                 closedAt cutoff t = True -> shift d cutoff t = t
shiftClosedId d cutoff (FVar _ _) prf = Refl
shiftClosedId d cutoff (Const _ _) prf = Refl
shiftClosedId d cutoff (BVar i ty) prf = rewrite prf in Refl
shiftClosedId d cutoff (Comb f x) prf =
  let (pf, px) = andTrueBoth (closedAt cutoff f) (closedAt cutoff x) prf in
  rewrite shiftClosedId d cutoff f pf in
  rewrite shiftClosedId d cutoff x px in Refl
shiftClosedId d cutoff (Abs aty b) prf =
  rewrite shiftClosedId d (S cutoff) b prf in Refl

-- The closedness counterpart of `substAtTypeSound`: substituting a closed
-- term for the binder at depth `j`, then closing the gap it left with
-- `shift (-1) j`, lands back inside `j` binders.
export
substShiftClosed : (j : Nat) -> (s, t : Term) ->
                    closedAt (S j) t = True -> closedAt 0 s = True ->
                    closedAt j (shift (-1) j (substAt j s t)) = True
substShiftClosed j s (FVar _ _) tPrf sPrf = Refl
substShiftClosed j s (Const _ _) tPrf sPrf = Refl
substShiftClosed j s (BVar i ty) tPrf sPrf with (i == j) proof pij
  substShiftClosed j s (BVar i ty) tPrf sPrf | True =
    -- The substituted copy is `shift j 0 s`, but `s` is closed, so both
    -- that shift and the outer `shift (-1) j` are the identity on it.
    rewrite shiftClosedId (natToInteger j) 0 s sPrf in
    rewrite shiftClosedId (-1) j s (closedAtFromZero j s sPrf) in
    closedAtFromZero j s sPrf
  substShiftClosed j s (BVar i ty) tPrf sPrf | False =
    -- Not the substituted index, so it survives; `i < S j` and `i /= j`
    -- put it strictly below `j`, so `shift (-1) j` leaves it alone too.
    let iLtJ = ltSuccNeq i j tPrf pij in
    rewrite iLtJ in iLtJ
substShiftClosed j s (Comb f x) tPrf sPrf =
  let (pf, px) = andTrueBoth (closedAt (S j) f) (closedAt (S j) x) tPrf in
  rewrite substShiftClosed j s f pf sPrf in
  rewrite substShiftClosed j s x px sPrf in Refl
substShiftClosed j s (Abs aty b) tPrf sPrf =
  substShiftClosed (S j) s b tPrf sPrf

-- `BETA`'s reduct of a locally closed redex is locally closed.
export
substBvarClosed : (body, arg : Term) ->
                   closedAt 1 body = True -> closedAt 0 arg = True ->
                   isLocallyClosed (substBvar arg body) = True
substBvarClosed body arg bodyPrf argPrf = substShiftClosed 0 arg body bodyPrf argPrf

-- -- free variables ------------------------------------------------------------

export
vfreeIn : Term -> Term -> Bool
vfreeIn v t@(FVar _ _) = v == t
vfreeIn v (Comb f x)   = vfreeIn v f || vfreeIn v x
vfreeIn v (Abs _ b)    = vfreeIn v b
vfreeIn _ _            = False

export
freeVars : Term -> List Term
freeVars t = walk t []
  where
    walk : Term -> List Term -> List Term
    walk t@(FVar _ _) acc = if t `elem` acc then acc else acc ++ [t]
    walk (Comb f x) acc   = walk x (walk f acc)
    walk (Abs _ b) acc    = walk b acc
    walk _ acc             = acc

-- -- ordering -------------------------------------------------------------------

rank : Term -> Int
rank (Const _ _) = 0
rank (FVar _ _)  = 1
rank (BVar _ _)  = 2
rank (Comb _ _)  = 3
rank (Abs _ _)   = 4

-- A total order on terms, used to keep hypothesis lists canonical.
public export
thenOrd : Ordering -> Ordering -> Ordering
thenOrd EQ o2 = o2
thenOrd o1 _  = o1

public export
termOrd : Term -> Term -> Ordering
termOrd (FVar n ty)     (FVar n2 ty2)     = thenOrd (compare n n2) (typeOrd ty ty2)
termOrd (Const n ty)    (Const n2 ty2)    = thenOrd (compare n n2) (typeOrd ty ty2)
termOrd (BVar i ty)     (BVar i2 ty2)     = thenOrd (compare i i2) (typeOrd ty ty2)
termOrd (Comb f x)      (Comb f2 x2)      = thenOrd (termOrd f f2) (termOrd x x2)
termOrd (Abs aty body)  (Abs aty2 body2)  = thenOrd (typeOrd aty aty2) (termOrd body body2)
termOrd a b = compare (rank a) (rank b)

-- -- beta -------------------------------------------------------------------

export
isBetaRedex : Term -> Bool
isBetaRedex (Comb (Abs _ _) _) = True
isBetaRedex _                   = False

export
Show Term where
  show (FVar n _)  = show n
  show (BVar i _)  = "#" ++ show i
  show (Const n _) = show n
  show (Comb f x)  = "(" ++ show f ++ " " ++ show x ++ ")"
  show (Abs aty b) = "\\" ++ show aty ++ ". " ++ show b

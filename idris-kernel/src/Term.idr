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

%default covering


public export
data Term : Type where
  FVar : String -> HType -> Term
  BVar : Nat -> HType -> Term
  Const : String -> HType -> Term
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
mkVar : String -> HType -> Term
mkVar = FVar

export
mkConst : String -> HType -> Term
mkConst = Const

export
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
export
shift : Integer -> Nat -> Term -> Term
shift d cutoff tm@(BVar i ty) =
  if i < cutoff
    then tm
    else BVar (integerToNat (natToInteger i + d)) ty
shift d cutoff (Comb f x)   = Comb (shift d cutoff f) (shift d cutoff x)
shift d cutoff (Abs aty b)  = Abs aty (shift d (S cutoff) b)
shift _ _ tm                = tm

substAt : Nat -> Term -> Term -> Term
substAt j s t@(BVar i _) = if i == j then shift (natToInteger j) 0 s else t
substAt j s (Comb f x)   = Comb (substAt j s f) (substAt j s x)
substAt j s (Abs aty b)  = Abs aty (substAt (S j) s b)
substAt _ _ t            = t

-- Replace the innermost bound variable by `s`, closing up the indices above
-- it.  This is the whole of beta reduction, and it cannot capture anything.
export
substBvar : Term -> Term -> Term
substBvar s body = shift (-1) 0 (substAt 0 s body)

abstractAt : Nat -> Term -> Term -> Term
abstractAt j v t@(FVar _ vty) = if t == v then BVar j vty else t
abstractAt j v (Comb f x)     = Comb (abstractAt j v f) (abstractAt j v x)
abstractAt j v (Abs aty b)    = Abs aty (abstractAt (S j) v b)
abstractAt _ _ t              = t

-- Turn every occurrence of the free variable `v` into a bound one, ready to
-- be wrapped in an `Abs`.  `v` must be an `FVar`; callers are the smart
-- constructors below.
export
abstractFvar : Term -> Term -> Term
abstractFvar v body = abstractAt 0 v body

-- `\v. body`, with `v`'s occurrences turned into `BVar 0`.
export
mkAbs : Term -> Term -> Either String Term
mkAbs v@(FVar _ vty) body = Right (Abs vty (abstractFvar v body))
mkAbs _ _                 = Left "mkAbs: not a free variable"

-- Substitute for free variables.  `theta` is a list of `(replacement,
-- variable)` pairs, applied simultaneously.
export
instFvar : List (Term, Term) -> Term -> Term
instFvar [] tm = tm
instFvar theta tm = go tm 0
  where
    lookup' : Term -> Nat -> Maybe Term
    lookup' v depth = go' theta
      where
        go' : List (Term, Term) -> Maybe Term
        go' [] = Nothing
        go' ((rep, x) :: rest) =
          if x == v
            then Just (if depth == 0 then rep else shift (natToInteger depth) 0 rep)
            else go' rest
    go : Term -> Nat -> Term
    go t@(FVar _ _) depth = fromMaybe t (lookup' t depth)
    go (Comb f x) depth   = Comb (go f depth) (go x depth)
    go (Abs aty b) depth  = Abs aty (go b (S depth))
    go t _                = t

-- Substitute for type variables throughout a term.
export
instType : SortedMap String HType -> Term -> Term
instType tyin tm = if null (SortedMap.toList tyin) then tm else go tm
  where
    go : Term -> Term
    go (FVar n ty)   = FVar n (typeSubst tyin ty)
    go (BVar i ty)   = BVar i (typeSubst tyin ty)
    go (Const n ty)  = Const n (typeSubst tyin ty)
    go (Comb f x)    = Comb (go f) (go x)
    go (Abs aty b)   = Abs (typeSubst tyin aty) (go b)

-- No `BVar` index may escape its binder.
export
isLocallyClosed : Term -> Bool
isLocallyClosed t = go t 0
  where
    go : Term -> Nat -> Bool
    go (BVar i _) depth = i < depth
    go (Comb f x) depth = go f depth && go x depth
    go (Abs _ b) depth  = go b (S depth)
    go _ _               = True

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
export
termOrd : Term -> Term -> Ordering
termOrd a b =
  case compare (rank a) (rank b) of
    EQ => case (a, b) of
            (FVar n ty, FVar n2 ty2) => thenOrd (compare n n2) (typeOrd ty ty2)
            (Const n ty, Const n2 ty2) => thenOrd (compare n n2) (typeOrd ty ty2)
            (BVar i ty, BVar i2 ty2) => thenOrd (compare i i2) (typeOrd ty ty2)
            (Comb f x, Comb f2 x2) => thenOrd (termOrd f f2) (termOrd x x2)
            (Abs aty body, Abs aty2 body2) => thenOrd (typeOrd aty aty2) (termOrd body body2)
            _ => EQ -- unreachable: same rank forces same constructor
    o  => o
  where
    thenOrd : Ordering -> Ordering -> Ordering
    thenOrd EQ o2 = o2
    thenOrd o1 _  = o1

-- -- beta -------------------------------------------------------------------

export
isBetaRedex : Term -> Bool
isBetaRedex (Comb (Abs _ _) _) = True
isBetaRedex _                   = False

export
Show Term where
  show (FVar n _)  = n
  show (BVar i _)  = "#" ++ show i
  show (Const n _) = n
  show (Comb f x)  = "(" ++ show f ++ " " ++ show x ++ ")"
  show (Abs aty b) = "\\" ++ show aty ++ ". " ++ show b

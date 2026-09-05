module Name

-- The names the kernel compares: type constructors, type variables,
-- constants and free variables.
--
-- Why not `String`.  `String` is a primitive: it has no constructors, so
-- for abstract `x` and `y` a proof of `x = y` cannot be built by matching
-- on anything -- it can only be coerced into existence with `believe_me`.
-- That is why an earlier version of this development assumed two axioms
-- (`s == s = True` and `a == b = True -> a = b`), and it is also how
-- `Data.String`'s own `DecEq` instance in base is implemented, so
-- borrowing that would have relocated the assumption rather than removed
-- it.  Making the name type *inductive* removes it: both facts below are
-- ordinary structural inductions, and this development now contains no
-- `believe_me` at all.
--
-- The shape mirrors `rhombus-hol-lib/rhombus/hol/private/names.rhm`, which
-- likewise fixes the logical constants' canonical names once and lets
-- everything else be an ordinary user symbol.  `NUser` carries a `Nat`
-- rather than text because that is what the Rhombus side's `Symbol`
-- equality actually is -- interned identity, not a character-by-character
-- comparison.  A wiring back to Rhombus would intern at the boundary; see
-- ../README.md.

%default total

public export
data Name : Type where
  ||| The function type constructor, `fun` (`->`).
  NFun   : Name
  ||| The type of propositions, `bool`.
  NBool  : Name
  ||| Equality, the one logical constant this kernel knows about.
  NEq    : Name
  ||| The type variable in `eq`'s generic type, `'a`.
  NAlpha : Name
  ||| Everything a user declares.
  NUser  : Nat -> Name

-- `Nat`, unlike `String`, is inductive, so both directions are provable.
export
natEqRefl : (n : Nat) -> n == n = True
natEqRefl Z     = Refl
natEqRefl (S k) = natEqRefl k

export
natEqSound : (a, b : Nat) -> a == b = True -> a = b
natEqSound Z     Z     prf = Refl
natEqSound Z     (S _) prf = absurd prf
natEqSound (S _) Z     prf = absurd prf
natEqSound (S a) (S b) prf = rewrite natEqSound a b prf in Refl

-- Needed because `elem` tests `e == x` with the list element on the left,
-- while a caller supplying distinct stamp tokens naturally states the
-- inequality the other way round.
export
natEqSym : (a, b : Nat) -> a == b = False -> b == a = False
natEqSym Z     Z     prf = absurd prf
natEqSym Z     (S _) prf = Refl
natEqSym (S _) Z     prf = Refl
natEqSym (S a) (S b) prf = natEqSym a b prf

public export
nameEq : Name -> Name -> Bool
nameEq NFun      NFun      = True
nameEq NBool     NBool     = True
nameEq NEq       NEq       = True
nameEq NAlpha    NAlpha    = True
nameEq (NUser a) (NUser b) = a == b
nameEq _         _         = False

public export
Eq Name where
  (==) = nameEq

export
nameEqRefl : (n : Name) -> n == n = True
nameEqRefl NFun      = Refl
nameEqRefl NBool     = Refl
nameEqRefl NEq       = Refl
nameEqRefl NAlpha    = Refl
nameEqRefl (NUser k) = natEqRefl k

export
nameEqSound : (a, b : Name) -> a == b = True -> a = b
nameEqSound NFun      NFun      prf = Refl
nameEqSound NBool     NBool     prf = Refl
nameEqSound NEq       NEq       prf = Refl
nameEqSound NAlpha    NAlpha    prf = Refl
nameEqSound (NUser a) (NUser b) prf = rewrite natEqSound a b prf in Refl
nameEqSound NFun      NBool     prf = absurd prf
nameEqSound NFun      NEq       prf = absurd prf
nameEqSound NFun      NAlpha    prf = absurd prf
nameEqSound NFun      (NUser _) prf = absurd prf
nameEqSound NBool     NFun      prf = absurd prf
nameEqSound NBool     NEq       prf = absurd prf
nameEqSound NBool     NAlpha    prf = absurd prf
nameEqSound NBool     (NUser _) prf = absurd prf
nameEqSound NEq       NFun      prf = absurd prf
nameEqSound NEq       NBool     prf = absurd prf
nameEqSound NEq       NAlpha    prf = absurd prf
nameEqSound NEq       (NUser _) prf = absurd prf
nameEqSound NAlpha    NFun      prf = absurd prf
nameEqSound NAlpha    NBool     prf = absurd prf
nameEqSound NAlpha    NEq       prf = absurd prf
nameEqSound NAlpha    (NUser _) prf = absurd prf
nameEqSound (NUser _) NFun      prf = absurd prf
nameEqSound (NUser _) NBool     prf = absurd prf
nameEqSound (NUser _) NEq       prf = absurd prf
nameEqSound (NUser _) NAlpha    prf = absurd prf

-- A total order, used only to keep hypothesis lists canonical (`termOrd`
-- in `Term.idr`); nothing is proved about it.
nameRank : Name -> Nat
nameRank NFun      = 0
nameRank NBool     = 1
nameRank NEq       = 2
nameRank NAlpha    = 3
nameRank (NUser _) = 4

public export
Ord Name where
  compare (NUser a) (NUser b) = compare a b
  compare a b = compare (nameRank a) (nameRank b)

export
Show Name where
  show NFun      = "fun"
  show NBool     = "bool"
  show NEq       = "eq"
  show NAlpha    = "a"
  show (NUser k) = "u" ++ show k

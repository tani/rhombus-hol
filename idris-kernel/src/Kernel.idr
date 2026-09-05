module Kernel
-- The LCF kernel, ported from
-- rhombus-hol-lib/rhombus/hol/private/kernel.rhm.
--
-- This is a prototype only: `Thm` and `Theory` are ordinary Idris values, not
-- yet guarded the way the Rhombus kernel guards `Thm` (`authentic`,
-- `constructor ~none`, an unexported `internal` constructor).  Idris2's
-- export lists (`export` vs `public export`) give the same shape of
-- boundary -- a module that does not `export` a constructor cannot pattern
-- match or build it -- but wiring that up, and replacing the Rhombus kernel
-- with code generated from here, is future work.  See ../../PLAN.md.

import Data.List
import Data.Maybe
import Data.SortedMap
import HType
import Term

%default covering


-- -- lineage --------------------------------------------------------------

-- Every theory node has a unique identity, and carries the set of identities
-- of all its ancestors (itself included).  A linear counter is not enough:
-- two sibling extensions of one base theory must stay incomparable, or a
-- theorem from one can be combined with a theorem from the other to prove
-- something false.  See the Rhombus kernel's comment for the concrete
-- example.
--
-- Identity is a caller-supplied opaque `String` token, not a counter Idris
-- mints itself: Idris has no pure "uninterned symbol" primitive, and a
-- kernel that minted its own identities would need either global mutable
-- state (ruled out -- see the Rhombus kernel's comment on why) or a counter
-- threaded through every caller. The Racket host already has exactly the
-- right primitive (`gensym`), used for this same purpose by the Rhombus
-- kernel today, so extension functions below take the fresh token as a
-- plain argument instead of returning one.  `ancestors` is a plain `List
-- String` rather than a `SortedSet`: it stays small (one entry per
-- extension in a lineage), and a `List` compiles to a bare Racket list with
-- no embedded interface-dictionary closures, which is what makes
-- constructing kernel values from the Racket side of the FFI boundary
-- tractable.
public export
record Stamp where
  constructor MkStamp
  stampId    : String
  stampGen   : Nat
  ancestors  : List String

export
descends : Stamp -> Stamp -> Bool
descends a b = stampId a `elem` ancestors b

export
freshStamp : String -> Stamp
freshStamp fresh = MkStamp fresh 0 [fresh]

export
nextStamp : String -> Stamp -> Stamp
nextStamp fresh prev = MkStamp fresh (S (stampGen prev)) (fresh :: ancestors prev)

-- Two theorems may be combined only when their theories lie on one line of
-- extension.  The result belongs to the later of the two.
export
combineStamps : Stamp -> Stamp -> Either String Stamp
combineStamps a b =
  if descends a b then Right b
  else if descends b a then Right a
  else Left "theorems come from different theories"

-- -- soundness proofs: lineage ------------------------------------------
--
-- These are not exercised by any rule -- they exist to check, at
-- `idris2 --build` time (i.e. whenever this file's proofs are re-checked,
-- decoupled from any Rhombus build), that the lineage argument the Rhombus
-- kernel's module comment makes in prose actually holds. This is the
-- "verify at the appropriate time" half of the idris-kernel/Rhombus split:
-- the Rhombus kernel is what runs; this file is what gets proved about the
-- same logic, on its own schedule (`idris2 --build kernel.ipkg`), not on
-- every `raco make`.

-- Idris cannot derive `s == s = True` for an abstract `String` by
-- computation: the underlying equality is a primitive/opaque operation on
-- the Racket backend, not something built from constructors Idris can
-- pattern-match on. This is the one place that fact is assumed rather than
-- derived -- an axiom about the primitive, stated explicitly rather than
-- left implicit.
export
stringEqRefl : (s : String) -> s == s = True
stringEqRefl s = believe_me (Refl {x = True})

-- `elem` here folds with `||` seeded at `True` once the head matches, and
-- `foldl` does not short-circuit -- it walks every remaining element
-- regardless of the accumulator -- so showing the fold "stays `True`" over
-- an arbitrary tail needs its own induction, not just unfolding `stringEqRefl`.
orTrueAbsorbs : (p : a -> Bool) -> (xs : List a) -> foldl (\acc, e => acc || p e) True xs = True
orTrueAbsorbs p [] = Refl
orTrueAbsorbs p (x :: xs) = orTrueAbsorbs p xs

export
elemSelf : (x : String) -> (xs : List String) -> elem x (x :: xs) = True
elemSelf x xs = rewrite stringEqRefl x in orTrueAbsorbs _ xs

-- Every `Stamp` this kernel ever constructs contains its own identity in
-- its own ancestor set -- by construction, `freshStamp`/`nextStamp` always
-- cons the fresh id onto the front of `ancestors`. This is exactly what
-- makes `descends` reflexive for any stamp this kernel could actually
-- produce (an arbitrary hand-built `Stamp` need not satisfy it, but
-- nothing in `Kernel` builds one any other way).
export
descendsSelfFresh : (fresh : String) -> descends (freshStamp fresh) (freshStamp fresh) = True
descendsSelfFresh fresh = elemSelf fresh []

export
descendsSelfNext : (fresh : String) -> (prev : Stamp) ->
                    descends (nextStamp fresh prev) (nextStamp fresh prev) = True
descendsSelfNext fresh prev = elemSelf fresh (ancestors prev)

-- The heart of the kernel's lineage argument (see the big comment at the
-- top of this section): whichever stamp `combineStamps` picks is reachable
-- from *both* inputs' provenance, given each input is itself
-- self-reachable (true of every stamp `Kernel` can build -- see the two
-- lemmas above). This is what makes the Rhombus kernel's "later of the
-- two, or reject" strategy actually sound and not merely deterministic:
-- a theorem re-stamped with the combined lineage is provably still usable
-- everywhere either of its two inputs was.
export
combineStampsSound : (a, b : Stamp) -> descends a a = True -> descends b b = True ->
                      (st : Stamp) -> combineStamps a b = Right st ->
                      (descends a st = True, descends b st = True)
combineStampsSound a b aSelf bSelf st eq with (descends a b) proof pab
  combineStampsSound a b aSelf bSelf b Refl | True = (pab, bSelf)
  combineStampsSound a b aSelf bSelf st eq | False with (descends b a) proof pba
    combineStampsSound a b aSelf bSelf a Refl | False | True = (aSelf, pba)
    combineStampsSound a b aSelf bSelf st eq | False | False = absurd eq

-- -- theorems ---------------------------------------------------------------

public export
record Thm where
  constructor MkThm
  thmHyps  : List Term
  thmConcl : Term
  thmStamp : Stamp

export
hypsOf : Thm -> List Term
hypsOf = thmHyps

export
conclOf : Thm -> Term
conclOf = thmConcl

export
stampOf : Thm -> Stamp
stampOf = thmStamp

export
Show Thm where
  show th = show (thmHyps th) ++ " |- " ++ show (thmConcl th)

-- -- hypothesis sets ---------------------------------------------------------
--
-- Kept as a list sorted by `termOrd` and deduplicated.

export
hypInsert : Term -> List Term -> List Term
hypInsert t [] = [t]
hypInsert t (h :: rest) =
  case termOrd t h of
    EQ => h :: rest
    LT => t :: h :: rest
    GT => h :: hypInsert t rest

export
hypUnion : List Term -> List Term -> List Term
hypUnion [] b = b
hypUnion a [] = a
hypUnion a b = foldl (flip hypInsert) b a

export
hypRemove : Term -> List Term -> List Term
hypRemove t = filter (/= t)

export
rehashHyps : List Term -> List Term
rehashHyps = foldl (flip hypInsert) []

-- -- theories -----------------------------------------------------------------
--
-- `tyops`/`consts`/`defs` are plain association lists, not `SortedMap`s, for
-- the same reason `Stamp.ancestors` is a plain `List` above: a `SortedMap`'s
-- runtime representation carries an embedded `Ord`-dictionary closure that
-- is impractical to construct from the Racket side of the FFI boundary.
-- These maps are small (one entry per declaration in a theory, not a
-- hot-path structure), so linear lookup is the right trade.
public export
record Theory where
  constructor MkTheory
  tyops  : List (String, Nat)
  consts : List (String, HType)
  axioms : List Thm
  defs   : List (String, Thm)
  thyStamp : Stamp

export
typeArity : Theory -> String -> Maybe Nat
typeArity thy n = lookup n (tyops thy)

export
constType : Theory -> String -> Maybe HType
constType thy n = lookup n (consts thy)

export
axiomsOf : Theory -> List Thm
axiomsOf = axioms

export
definitionOf : Theory -> String -> Maybe Thm
definitionOf thy n = lookup n (defs thy)

inTheory : Theory -> Thm -> Either String ()
inTheory thy th =
  if descends (thmStamp th) (thyStamp thy)
    then Right ()
    else Left "theorem was not proved in this theory or an ancestor of it"

-- `fresh` is an opaque identity token supplied by the caller (see the
-- comment on `Stamp` above) -- one per theory-extending call, never reused.
export
initialTheory : String -> Theory
initialTheory fresh =
  MkTheory [("bool", 0), ("fun", 2)]
           [("eq", mkFun (TyVar "a") (mkFun (TyVar "a") boolTy))]
           []
           []
           (freshStamp fresh)

extend : Theory -> String
       -> List (String, Nat) -> List (String, HType)
       -> List Thm -> List (String, Thm)
       -> Theory
extend thy fresh tyops' consts' axioms' defs' =
  MkTheory tyops' consts' axioms' defs' (nextStamp fresh (thyStamp thy))

-- -- well-formedness ----------------------------------------------------------

export
checkType : Theory -> HType -> Either String ()
checkType _   (TyVar _)    = Right ()
checkType thy (TyApp n args) =
  case typeArity thy n of
    Nothing => Left ("undeclared type constructor: " ++ n)
    Just ar =>
      if ar /= length args
        then Left "type constructor arity mismatch"
        else traverse_ (checkType thy) args

-- `env` holds the argument types of the enclosing binders, innermost first.
checkOpenTerm : Theory -> Term -> List HType -> Either String ()
checkOpenTerm thy (FVar _ ty) _ = checkType thy ty
checkOpenTerm thy (BVar i ty) env =
  case inBounds i env of
    Nothing => Left "term has an unbound de Bruijn index"
    Just ety =>
      if ety == ty
        then checkType thy ty
        else Left "bound variable's type does not match its binder"
  where
    inBounds : Nat -> List HType -> Maybe HType
    inBounds Z (x :: _) = Just x
    inBounds (S k) (_ :: xs) = inBounds k xs
    inBounds _ [] = Nothing
checkOpenTerm thy (Const n ty) _ = do
  checkType thy ty
  case constType thy n of
    Nothing => Left ("undeclared constant: " ++ n)
    Just gty => case typeMatch gty ty empty of
                  Nothing => Left "constant used at a non-instance type"
                  Just _  => Right ()
checkOpenTerm thy (Abs aty b) env = do
  checkType thy aty
  checkOpenTerm thy b (aty :: env)
checkOpenTerm thy (Comb f x) env = do
  checkOpenTerm thy f env
  checkOpenTerm thy x env
  fty <- typeOf f
  if not (isFun fty)
    then Left "operator is not a function"
    else do
      (dom, _) <- destFun fty
      xty <- typeOf x
      if dom == xty then Right () else Left "ill-typed application"

export
checkTerm : Theory -> Term -> Either String ()
checkTerm thy t = checkOpenTerm thy t []

export
isBool : Term -> Either String Bool
isBool t = map (== boolTy) (typeOf t)

checkProp : Theory -> Term -> Either String ()
checkProp thy t = do
  checkTerm thy t
  ok <- isBool t
  if ok then Right () else Left "term is not a proposition"

-- -- equality --------------------------------------------------------------

export
mkEq : Term -> Term -> Either String Term
mkEq l r = do
  lty <- typeOf l
  rty <- typeOf r
  if lty /= rty
    then Left "sides of an equation have different types"
    else Right (Comb (Comb (Const "eq" (mkFun lty (mkFun lty boolTy))) l) r)

export
destEq : Term -> Maybe (Term, Term)
destEq (Comb (Comb (Const "eq" _) l) r) = Just (l, r)
destEq _                                 = Nothing

export
isEq : Term -> Bool
isEq t = isJust (destEq t)

needEq : Thm -> Either String (Term, Term)
needEq th = case destEq (thmConcl th) of
              Nothing => Left "theorem is not an equation"
              Just pr => Right pr

-- -- the ten primitive rules --------------------------------------------------
--
-- HOL Light's set, unchanged in content.  What the locally nameless
-- representation changes is only that the side conditions get simpler: no
-- alpha comparisons, and `BETA` is no longer restricted to `(\v. b) v`.

-- |- t = t
export
reflR : Theory -> Term -> Either String Thm
reflR thy t = do
  checkTerm thy t
  eq <- mkEq t t
  Right (MkThm [] eq (thyStamp thy))

-- |- l = m   |- m = r
-- -------------------
--      |- l = r
export
transR : Thm -> Thm -> Either String Thm
transR a b = do
  st <- combineStamps (thmStamp a) (thmStamp b)
  (l, m1) <- needEq a
  (m2, r) <- needEq b
  if m1 /= m2
    then Left "middle terms do not match"
    else do
      eq <- mkEq l r
      Right (MkThm (hypUnion (thmHyps a) (thmHyps b)) eq st)

-- |- f = g   |- x = y
-- -------------------
--   |- f x = g y
export
mkCombR : Thm -> Thm -> Either String Thm
mkCombR fth xth = do
  st <- combineStamps (thmStamp fth) (thmStamp xth)
  (f, g) <- needEq fth
  (x, y) <- needEq xth
  fty <- typeOf f
  if not (isFun fty)
    then Left "operator is not a function"
    else do
      (dom, _) <- destFun fty
      xty <- typeOf x
      if dom /= xty
        then Left "types do not agree"
        else do
          eq <- mkEq (Comb f x) (Comb g y)
          Right (MkThm (hypUnion (thmHyps fth) (thmHyps xth)) eq st)

--        |- l = r          (v not free in the hypotheses)
-- -------------------------
--  |- (\v. l) = (\v. r)
export
absR : Theory -> Term -> Thm -> Either String Thm
absR thy v th = do
  inTheory thy th
  checkTerm thy v
  if any (vfreeIn v) (thmHyps th)
    then Left "abstracted variable is free in the hypotheses"
    else do
      (l, r) <- needEq th
      la <- mkAbs v l
      ra <- mkAbs v r
      eq <- mkEq la ra
      Right (MkThm (thmHyps th) eq (thyStamp thy))

-- |- (\x. body) arg = body[arg]
export
betaR : Theory -> Term -> Either String Thm
betaR thy t = do
  checkTerm thy t
  case t of
    Comb (Abs _ body) arg => do
      eq <- mkEq t (substBvar arg body)
      Right (MkThm [] eq (thyStamp thy))
    _ => Left "not a beta redex"

-- p |- p
export
assumeR : Theory -> Term -> Either String Thm
assumeR thy p = do
  checkProp thy p
  Right (MkThm [p] p (thyStamp thy))

-- |- p = q   |- p
-- ---------------
--      |- q
export
eqMpR : Thm -> Thm -> Either String Thm
eqMpR eqth th = do
  st <- combineStamps (thmStamp eqth) (thmStamp th)
  (p, q) <- needEq eqth
  if p /= thmConcl th
    then Left "antecedent does not match"
    else Right (MkThm (hypUnion (thmHyps eqth) (thmHyps th)) q st)

--  A |- p       B |- q
-- ---------------------------------
--  (A - q) u (B - p) |- p = q
export
deductAntisymRule : Thm -> Thm -> Either String Thm
deductAntisymRule a b = do
  st <- combineStamps (thmStamp a) (thmStamp b)
  eq <- mkEq (thmConcl a) (thmConcl b)
  Right (MkThm (hypUnion (hypRemove (thmConcl b) (thmHyps a))
                          (hypRemove (thmConcl a) (thmHyps b)))
               eq st)

-- Instantiate free variables.  `theta` is a list of `(replacement,
-- variable)` pairs.
export
instR : Theory -> List (Term, Term) -> Thm -> Either String Thm
instR thy theta th = do
  inTheory thy th
  checkTheta theta
  let hyps2 = rehashHyps (map (instFvar theta) (thmHyps th))
  Right (MkThm hyps2 (instFvar theta (thmConcl th)) (thyStamp thy))
  where
    checkTheta : List (Term, Term) -> Either String ()
    checkTheta [] = Right ()
    checkTheta ((rep, v) :: rest) = do
      case v of
        FVar _ _ => Right ()
        _        => Left "substitution target is not a free variable"
      checkTerm thy rep
      vty <- typeOf v
      rty <- typeOf rep
      if vty /= rty
        then Left "instantiation changes a variable's type"
        else checkTheta rest

-- Instantiate type variables.  `tyin` is a plain association list (see the
-- comment on `Theory` above for why); converted once to a `SortedMap` for
-- `instType`'s internal use, since that conversion never crosses the FFI
-- boundary.
export
instTypeR : Theory -> List (String, HType) -> Thm -> Either String Thm
instTypeR thy tyin th = do
  inTheory thy th
  traverse_ (checkType thy) (map snd tyin)
  let tyinMap = SortedMap.fromList tyin
  let hyps2 = rehashHyps (map (instType tyinMap) (thmHyps th))
  Right (MkThm hyps2 (instType tyinMap (thmConcl th)) (thyStamp thy))

-- -- theory extension -----------------------------------------------------

export
newType : Theory -> String -> String -> Nat -> Either String Theory
newType thy fresh n arity =
  case typeArity thy n of
    Just _  => Left ("type constructor is already declared: " ++ n)
    Nothing => Right (extend thy fresh ((n, arity) :: tyops thy) (consts thy)
                              (axioms thy) (defs thy))

export
newConstant : Theory -> String -> String -> HType -> Either String Theory
newConstant thy fresh n ty =
  case constType thy n of
    Just _  => Left ("constant is already declared: " ++ n)
    Nothing => do
      checkType thy ty
      Right (extend thy fresh (tyops thy) ((n, ty) :: consts thy)
                    (axioms thy) (defs thy))

-- The escape hatch: every use shows up in `axiomsOf`.
export
newAxiom : Theory -> String -> Term -> Either String (Theory, Thm)
newAxiom thy fresh p = do
  checkProp thy p
  let st = nextStamp fresh (thyStamp thy)
  let th = MkThm [] p st
  Right (MkTheory (tyops thy) (consts thy) (th :: axioms thy) (defs thy) st, th)

termTypeVars : Term -> List String
termTypeVars t = walk t []
  where
    add : HType -> List String -> List String
    add ty acc = foldl (\a, v => if v `elem` a then a else a ++ [v]) acc (typeVars ty)
    walk : Term -> List String -> List String
    walk (FVar _ ty) acc  = add ty acc
    walk (BVar _ ty) acc  = add ty acc
    walk (Const _ ty) acc = add ty acc
    walk (Comb f x) acc   = walk x (walk f acc)
    walk (Abs aty b) acc  = walk b (add aty acc)

-- A conservative definition: `c = rhs` where `c` is undeclared, `rhs` is
-- closed, and `rhs` has no type variables beyond those of its own type.
export
newBasicDefinition : Theory -> String -> Term -> Either String (Theory, Thm)
newBasicDefinition thy fresh tm =
  case destEq tm of
    Nothing => Left "definition is not an equation"
    Just (FVar n ty, rhs) => do
      case constType thy n of
        Just _  => Left ("constant is already declared: " ++ n)
        Nothing => do
          checkTerm thy rhs
          if not (null (freeVars rhs))
            then Left "right-hand side is not closed"
            else do
              rty <- typeOf rhs
              if ty /= rty
                then Left "type mismatch in definition"
                else do
                  let rhsTvs = termTypeVars rhs
                  let tyTvs  = typeVars ty
                  if not (all (\v => v `elem` tyTvs) rhsTvs)
                    then Left "right-hand side has type variables not in the type"
                    else do
                      let st = nextStamp fresh (thyStamp thy)
                      let c  = mkConst n ty
                      eq <- mkEq c rhs
                      let th = MkThm [] eq st
                      Right (MkTheory (tyops thy) ((n, ty) :: consts thy)
                                       (axioms thy) ((n, th) :: defs thy) st,
                             th)
    Just _ => Left "left-hand side is not a fresh name"

-- Carve out a new type in bijection with the subset picked out by `pred`,
-- given `|- pred witness`.
export
newBasicTypeDefinition : Theory -> String -> String -> String -> String -> Thm
                        -> Either String (Theory, Thm, Thm)
newBasicTypeDefinition thy fresh tyname absname repname th = do
  inTheory thy th
  when (isJust (constType thy absname) || isJust (constType thy repname))
    (Left "constant is already declared")
  when (isJust (typeArity thy tyname))
    (Left ("type constructor is already declared: " ++ tyname))
  when (absname == repname)
    (Left "abstraction and representation functions have the same name")
  when (not (null (thmHyps th)))
    (Left "witness theorem has hypotheses")
  case thmConcl th of
    Comb pred witness => do
      when (not (null (freeVars pred))) (Left "predicate is not closed")
      let tvs = termTypeVars pred
      rty <- typeOf witness
      when (not (all (\v => v `elem` tvs) (typeVars rty)))
        (Left "witness has type variables not present in the predicate")
      let st  = nextStamp fresh (thyStamp thy)
      let aty = TyApp tyname (map TyVar tvs)
      let thy2 = MkTheory ((tyname, length tvs) :: tyops thy)
                           ((repname, mkFun aty rty) :: (absname, mkFun rty aty) :: consts thy)
                           (axioms thy) (defs thy) st
      let absC = mkConst absname (mkFun rty aty)
      let repC = mkConst repname (mkFun aty rty)
      let a = mkVar "a" aty
      let r = mkVar "r" rty
      eq1 <- mkEq (Comb absC (Comb repC a)) a
      inner <- mkEq (Comb repC (Comb absC r)) r
      eq2 <- mkEq (Comb pred r) inner
      Right (thy2, MkThm [] eq1 st, MkThm [] eq2 st)
    _ => Left "witness theorem is not an application"
  where
    when : Bool -> Either String () -> Either String ()
    when True e  = e
    when False _ = Right ()

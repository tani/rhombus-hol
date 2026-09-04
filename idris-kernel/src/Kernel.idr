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
import Data.SortedSet
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
public export
record Stamp where
  constructor MkStamp
  stampId    : Nat
  stampGen   : Nat
  ancestors  : SortedSet Nat

export
descends : Stamp -> Stamp -> Bool
descends a b = contains (stampId a) (ancestors b)

freshStamp : Nat -> Stamp
freshStamp fresh = MkStamp fresh 0 (SortedSet.insert fresh SortedSet.empty)

nextStamp : Nat -> Stamp -> Stamp
nextStamp fresh prev =
  MkStamp fresh (S (stampGen prev)) (SortedSet.insert fresh (ancestors prev))

-- Two theorems may be combined only when their theories lie on one line of
-- extension.  The result belongs to the later of the two.
combineStamps : Stamp -> Stamp -> Either String Stamp
combineStamps a b =
  if descends a b then Right b
  else if descends b a then Right a
  else Left "theorems come from different theories"

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

public export
record Theory where
  constructor MkTheory
  tyops  : SortedMap String Nat
  consts : SortedMap String HType
  axioms : List Thm
  defs   : SortedMap String Thm
  thyStamp : Stamp

export
typeArity : Theory -> String -> Maybe Nat
typeArity thy n = SortedMap.lookup n (tyops thy)

export
constType : Theory -> String -> Maybe HType
constType thy n = SortedMap.lookup n (consts thy)

export
axiomsOf : Theory -> List Thm
axiomsOf = axioms

export
definitionOf : Theory -> String -> Maybe Thm
definitionOf thy n = SortedMap.lookup n (defs thy)

inTheory : Theory -> Thm -> Either String ()
inTheory thy th =
  if descends (thmStamp th) (thyStamp thy)
    then Right ()
    else Left "theorem was not proved in this theory or an ancestor of it"

-- `fresh` is a counter supplied by the caller.  The Rhombus kernel uses
-- uninterned symbols for this; Idris has no equivalent primitive available
-- purely, so extension threads a `Nat` counter instead.  Every extension
-- function below returns the counter alongside the theory.
export
initialTheory : Nat -> (Theory, Nat)
initialTheory fresh =
  ( MkTheory (fromList [("bool", 0), ("fun", 2)])
             (fromList [("eq", mkFun (TyVar "a") (mkFun (TyVar "a") boolTy))])
             []
             empty
             (freshStamp fresh)
  , S fresh)

extend : Theory -> Nat
       -> SortedMap String Nat -> SortedMap String HType
       -> List Thm -> SortedMap String Thm
       -> (Theory, Nat)
extend thy fresh tyops' consts' axioms' defs' =
  (MkTheory tyops' consts' axioms' defs' (nextStamp fresh (thyStamp thy)), S fresh)

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

-- Instantiate type variables.
export
instTypeR : Theory -> SortedMap String HType -> Thm -> Either String Thm
instTypeR thy tyin th = do
  inTheory thy th
  traverse_ (checkType thy) (values tyin)
  let hyps2 = rehashHyps (map (instType tyin) (thmHyps th))
  Right (MkThm hyps2 (instType tyin (thmConcl th)) (thyStamp thy))

-- -- theory extension -----------------------------------------------------

export
newType : Theory -> Nat -> String -> Nat -> Either String (Theory, Nat)
newType thy fresh n arity =
  case typeArity thy n of
    Just _  => Left ("type constructor is already declared: " ++ n)
    Nothing => Right (extend thy fresh (insert n arity (tyops thy)) (consts thy)
                              (axioms thy) (defs thy))

export
newConstant : Theory -> Nat -> String -> HType -> Either String (Theory, Nat)
newConstant thy fresh n ty =
  case constType thy n of
    Just _  => Left ("constant is already declared: " ++ n)
    Nothing => do
      checkType thy ty
      Right (extend thy fresh (tyops thy) (insert n ty (consts thy))
                    (axioms thy) (defs thy))

-- The escape hatch: every use shows up in `axiomsOf`.
export
newAxiom : Theory -> Nat -> Term -> Either String (Theory, Thm, Nat)
newAxiom thy fresh p = do
  checkProp thy p
  let st = nextStamp fresh (thyStamp thy)
  let th = MkThm [] p st
  Right (MkTheory (tyops thy) (consts thy) (th :: axioms thy) (defs thy) st, th, S fresh)

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
newBasicDefinition : Theory -> Nat -> Term -> Either String (Theory, Thm, Nat)
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
                      Right (MkTheory (tyops thy) (insert n ty (consts thy))
                                       (axioms thy) (insert n th (defs thy)) st,
                             th, S fresh)
    Just _ => Left "left-hand side is not a fresh name"

-- Carve out a new type in bijection with the subset picked out by `pred`,
-- given `|- pred witness`.
export
newBasicTypeDefinition : Theory -> Nat -> String -> String -> String -> Thm
                        -> Either String (Theory, Thm, Thm, Nat)
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
      let thy2 = MkTheory (insert tyname (length tvs) (tyops thy))
                           (insert repname (mkFun aty rty)
                             (insert absname (mkFun rty aty) (consts thy)))
                           (axioms thy) (defs thy) st
      let absC = mkConst absname (mkFun rty aty)
      let repC = mkConst repname (mkFun aty rty)
      let a = mkVar "a" aty
      let r = mkVar "r" rty
      eq1 <- mkEq (Comb absC (Comb repC a)) a
      inner <- mkEq (Comb repC (Comb absC r)) r
      eq2 <- mkEq (Comb pred r) inner
      Right (thy2, MkThm [] eq1 st, MkThm [] eq2 st, S fresh)
    _ => Left "witness theorem is not an application"
  where
    when : Bool -> Either String () -> Either String ()
    when True e  = e
    when False _ = Right ()

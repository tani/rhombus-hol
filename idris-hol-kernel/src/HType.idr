module HType
-- HOL types, ported from
-- rhombus-hol-lib/rhombus/hol/private/htype.rhm.
--
-- Two constructors, HOL Light style: type variables and applications of a
-- type constructor to arguments.  The function type is not special-cased --
-- it is `TyApp "fun" [dom, rng]` -- and constructor arities live in the
-- theory, not in the type.

import Data.List
import Data.Maybe
import Data.SortedMap
import public Name

%default total


-- `HType` and `List HType` are mutually structurally recursive, and Idris2's
-- termination checker only sees through that when the two functions are
-- declared together in one `mutual` block -- routing the list case through a
-- higher-order helper (as `Eq`'s default `/=`, or `Data.List`'s `==`, would)
-- hides the structural decrease and the checker rejects it as possibly
-- looping.  So types-and-terms equality below is hand-written, not derived.
mutual
  public export
  data HType : Type where
    TyVar : Name -> HType
    TyApp : Name -> List HType -> HType

  htypeEq : HType -> HType -> Bool
  htypeEq (TyVar a) (TyVar b) = a == b
  htypeEq (TyApp n1 as1) (TyApp n2 as2) = n1 == n2 && htypeListEq as1 as2
  htypeEq _ _ = False

  htypeListEq : List HType -> List HType -> Bool
  htypeListEq [] [] = True
  htypeListEq (x :: xs) (y :: ys) = htypeEq x y && htypeListEq xs ys
  htypeListEq _ _ = False

export
Eq HType where
  (==) = htypeEq

-- -- soundness proof: `Eq HType`'s `==` is sound -----------------------
--
-- Substitution lemmas need both directions of the comparison the kernel
-- actually performs: if `checkOpenTerm` decided two types are `==`, they
-- really are the *same* type (otherwise substituting a term of one type
-- for a `BVar` annotated with a merely-`==`-but-different type would be
-- silently unsound), and a type compares equal to itself.  Both are
-- structural inductions here, resting on `Name`'s own `nameEqSound` /
-- `nameEqRefl` -- see `Name.idr` for why the name type is inductive rather
-- than `String`, which is what makes that possible without any axiom.

-- `&&` returning `True` forces both operands to be `True`. Used all over
-- the substitution lemmas, since `checkOpenTerm`/`closedAt` combine their
-- sub-results with `&&`.
export
andTrueBoth : (x, y : Bool) -> x && y = True -> (x = True, y = True)
andTrueBoth True  y prf = (Refl, prf)
andTrueBoth False y prf = absurd prf

mutual
  export
  htypeEqSound : (a, b : HType) -> htypeEq a b = True -> a = b
  htypeEqSound (TyVar a)      (TyVar b)      prf = rewrite nameEqSound a b prf in Refl
  htypeEqSound (TyVar _)      (TyApp _ _)    prf = absurd prf
  htypeEqSound (TyApp _ _)    (TyVar _)      prf = absurd prf
  htypeEqSound (TyApp n1 as1) (TyApp n2 as2) prf =
    let (pn, pas) = andTrueBoth (n1 == n2) (htypeListEq as1 as2) prf
        nEq  = nameEqSound n1 n2 pn
        asEq = htypeListEqSound as1 as2 pas
    in rewrite nEq in rewrite asEq in Refl

  htypeListEqSound : (as, bs : List HType) -> htypeListEq as bs = True -> as = bs
  htypeListEqSound []        []        prf = Refl
  htypeListEqSound []        (_ :: _)  prf = absurd prf
  htypeListEqSound (_ :: _)  []        prf = absurd prf
  htypeListEqSound (x :: xs) (y :: ys) prf =
    let (px, pxs) = andTrueBoth (htypeEq x y) (htypeListEq xs ys) prf
        xEq  = htypeEqSound x y px
        xsEq = htypeListEqSound xs ys pxs
    in rewrite xEq in rewrite xsEq in Refl

-- The other direction: `==` on types is reflexive.  Needed wherever the
-- kernel compares a type against itself and the proof has to know the
-- comparison succeeds -- e.g. `typeMatch` re-encountering a type variable
-- it has already bound, which is what makes `eq`'s generic type match its
-- instance.
mutual
  export
  htypeEqRefl : (t : HType) -> htypeEq t t = True
  htypeEqRefl (TyVar n) = nameEqRefl n
  htypeEqRefl (TyApp n args) =
    rewrite nameEqRefl n in htypeListEqRefl args

  htypeListEqRefl : (ts : List HType) -> htypeListEq ts ts = True
  htypeListEqRefl [] = Refl
  htypeListEqRefl (t :: ts) =
    rewrite htypeEqRefl t in htypeListEqRefl ts

public export
boolTy : HType
boolTy = TyApp NBool []

public export
mkFun : HType -> HType -> HType
mkFun dom rng = TyApp NFun [dom, rng]

-- Name tested with `==` rather than matched as a literal, same as
-- `destFun` and for the same reason.
public export
isFun : HType -> Bool
isFun (TyApp n [_, _]) = n == NFun
isFun _                = False

-- Throws if `t` is not a function type; callers that are not sure should ask
-- `isFun` first.
--
-- The constructor name is tested with `==` rather than matched as a string
-- literal pattern.  Same behaviour, but a literal pattern leaves
-- `destFun (TyApp n [a, b])` stuck for an *abstract* `n` -- Idris's
-- evaluator does not carry "n is not \"fun\"" into the default branch --
-- and proofs that need to case on whether a type is a function type would
-- have nowhere to go.
public export
destFun : HType -> Either String (HType, HType)
destFun (TyApp n [dom, rng]) =
  if n == NFun then Right (dom, rng) else Left "not a function type"
destFun _ = Left "not a function type"

-- Type variables, in left-to-right order of first occurrence, without
-- duplicates.  Order matters: it is what makes generated axioms
-- deterministic.
addVar : Name -> List Name -> List Name
addVar n acc = if n `elem` acc then acc else acc ++ [n]

mutual
  -- Type variables, in left-to-right order of first occurrence, without
  -- duplicates.  Order matters: it is what makes generated axioms
  -- deterministic.
  export
  typeVars : HType -> List Name
  typeVars t = walkType t []

  walkType : HType -> List Name -> List Name
  walkType (TyVar n) acc = addVar n acc
  walkType (TyApp _ args) acc = walkTypeList args acc

  walkTypeList : List HType -> List Name -> List Name
  walkTypeList [] acc = acc
  walkTypeList (a :: as) acc = walkTypeList as (walkType a acc)

-- Association list rather than `SortedMap`, for the same two reasons
-- `typeMatch`'s accumulator is one: it crosses the FFI boundary cleanly,
-- and `Data.SortedMap`'s operations do not reduce during typechecking.
mutual
  public export
  typeSubst : List (Name, HType) -> HType -> HType
  typeSubst theta t =
    if null theta then t else typeSubst' theta t

  public export
  typeSubst' : List (Name, HType) -> HType -> HType
  typeSubst' theta (TyVar n)      = fromMaybe (TyVar n) (lookup n theta)
  typeSubst' theta (TyApp n args) = TyApp n (typeSubstList theta args)

  public export
  typeSubstList : List (Name, HType) -> List HType -> List HType
  typeSubstList _     []        = []
  typeSubstList theta (a :: as) = typeSubst' theta a :: typeSubstList theta as

-- One-way matching: extend `acc` so that `typeSubst result pat == t`.
-- `Nothing` when no such extension exists.
--
-- The accumulator is a plain association list rather than a `SortedMap`
-- for the same reason `Theory`'s tables are (see `Kernel.idr`), plus one
-- specific to proving things about it: `Data.SortedMap`'s operations are
-- `export`, not `public export`, so their bodies are invisible outside
-- that module and `lookup k empty` will not reduce during typechecking --
-- which blocks any proof that a match succeeds.  `Data.List.lookup` is
-- `public export` and reduces fine.  The accumulator is tiny (one entry
-- per type variable of the pattern), so a list is the right structure
-- anyway.
mutual
  public export
  typeMatch : HType -> HType -> List (Name, HType) -> Maybe (List (Name, HType))
  typeMatch (TyVar n) t acc =
    case lookup n acc of
      Nothing   => Just ((n, t) :: acc)
      Just prev => if prev == t then Just acc else Nothing
  typeMatch (TyApp n pargs) (TyApp n2 targs) acc =
    if n == n2 then typeMatchList pargs targs acc else Nothing
  typeMatch _ _ _ = Nothing

  public export
  typeMatchList : List HType -> List HType -> List (Name, HType)
                -> Maybe (List (Name, HType))
  typeMatchList [] [] a = Just a
  typeMatchList (p :: ps) (q :: qs) a = do
    a2 <- typeMatch p q a
    typeMatchList ps qs a2
  typeMatchList _ _ _ = Nothing

-- -- soundness proofs: matching survives instantiation ------------------
--
-- `INST_TYPE` rewrites the types inside a theorem.  The one thing that
-- could go wrong is a constant's use type ceasing to be an instance of its
-- declared generic type -- `check_open_term`'s `typeMatch` test.  It
-- cannot: substituting into an instance leaves it an instance, with the
-- bindings substituted the same way.  That is this section.

justInj : Just a = Just b -> a = b
justInj Refl = Refl

-- Substituting through a matcher's accumulator.
-- Stated with the worker `typeSubst'` rather than `typeSubst`, whose
-- `null theta` short-circuit would otherwise have to be case-split on at
-- every step; the two agree whenever `theta` is non-empty, which is the
-- only case that reaches here.
public export
substAcc : List (Name, HType) -> List (Name, HType) -> List (Name, HType)
substAcc theta [] = []
substAcc theta ((n, t) :: rest) = (n, typeSubst' theta t) :: substAcc theta rest

substAccLookupNothing : (theta, acc : List (Name, HType)) -> (n : Name) ->
                         lookup n acc = Nothing -> lookup n (substAcc theta acc) = Nothing
substAccLookupNothing theta [] n prf = Refl
substAccLookupNothing theta ((k, v) :: rest) n prf with (n == k)
  substAccLookupNothing theta ((k, v) :: rest) n prf | True = absurd prf
  substAccLookupNothing theta ((k, v) :: rest) n prf | False =
    substAccLookupNothing theta rest n prf

substAccLookupJust : (theta, acc : List (Name, HType)) -> (n : Name) -> (t : HType) ->
                      lookup n acc = Just t ->
                      lookup n (substAcc theta acc) = Just (typeSubst' theta t)
substAccLookupJust theta [] n t prf = absurd prf
substAccLookupJust theta ((k, v) :: rest) n t prf with (n == k)
  substAccLookupJust theta ((k, v) :: rest) n t prf | True =
    rewrite justInj prf in Refl
  substAccLookupJust theta ((k, v) :: rest) n t prf | False =
    substAccLookupJust theta rest n t prf

mutual
  export
  typeMatchSubst : (theta : List (Name, HType)) -> (p, t : HType) ->
                    (acc, m : List (Name, HType)) ->
                    typeMatch p t acc = Just m ->
                    typeMatch p (typeSubst' theta t) (substAcc theta acc)
                      = Just (substAcc theta m)
  typeMatchSubst theta (TyVar n) t acc m prf with (lookup n acc) proof pL
    typeMatchSubst theta (TyVar n) t acc m prf | Nothing =
      rewrite substAccLookupNothing theta acc n pL in
      rewrite sym (justInj prf) in Refl
    typeMatchSubst theta (TyVar n) t acc m prf | Just prev with (prev == t) proof pE
      typeMatchSubst theta (TyVar n) t acc m prf | Just prev | False = absurd prf
      typeMatchSubst theta (TyVar n) t acc m prf | Just prev | True =
        rewrite substAccLookupJust theta acc n prev pL in
        rewrite htypeEqSound prev t pE in
        rewrite htypeEqRefl (typeSubst' theta t) in
        rewrite sym (justInj prf) in Refl
  typeMatchSubst theta (TyApp n pargs) (TyVar _) acc m prf = absurd prf
  typeMatchSubst theta (TyApp n pargs) (TyApp n2 targs) acc m prf with (n == n2) proof pN
    typeMatchSubst theta (TyApp n pargs) (TyApp n2 targs) acc m prf | False = absurd prf
    typeMatchSubst theta (TyApp n pargs) (TyApp n2 targs) acc m prf | True =
      typeMatchListSubst theta pargs targs acc m prf

  typeMatchListSubst : (theta : List (Name, HType)) ->
                        (ps, ts : List HType) -> (acc, m : List (Name, HType)) ->
                        typeMatchList ps ts acc = Just m ->
                        typeMatchList ps (typeSubstList theta ts) (substAcc theta acc)
                          = Just (substAcc theta m)
  typeMatchListSubst theta [] [] acc m prf = rewrite sym (justInj prf) in Refl
  typeMatchListSubst theta [] (_ :: _) acc m prf = absurd prf
  typeMatchListSubst theta (_ :: _) [] acc m prf = absurd prf
  typeMatchListSubst theta (p :: ps) (t :: ts) acc m prf with (typeMatch p t acc) proof pM
    typeMatchListSubst theta (p :: ps) (t :: ts) acc m prf | Nothing = absurd prf
    typeMatchListSubst theta (p :: ps) (t :: ts) acc m prf | Just acc2 =
      rewrite typeMatchSubst theta p t acc acc2 pM in
      typeMatchListSubst theta ps ts acc2 m prf

export
typeSubstListLength : (theta : List (Name, HType)) -> (as : List HType) ->
                       length (typeSubstList theta as) = length as
typeSubstListLength theta [] = Refl
typeSubstListLength theta (a :: as) = cong S (typeSubstListLength theta as)

-- Anything `destFun` takes apart is a function type.
export
destFunIsFun : (t, a, b : HType) -> destFun t = Right (a, b) -> isFun t = True
destFunIsFun (TyVar _) a b prf = absurd prf
destFunIsFun (TyApp n []) a b prf = absurd prf
destFunIsFun (TyApp n [x]) a b prf = absurd prf
destFunIsFun (TyApp n (x :: y :: z :: rest)) a b prf = absurd prf
destFunIsFun (TyApp n [x, y]) a b prf with (n == NFun) proof pN
  destFunIsFun (TyApp n [x, y]) a b prf | False = absurd prf
  destFunIsFun (TyApp n [x, y]) a b prf | True = Refl

-- Substitution commutes with taking a function type apart, which is what
-- lets `typeOf` and `instType` commute on applications.
export
destFunSubst : (theta : List (Name, HType)) -> (t, a, b : HType) ->
                destFun t = Right (a, b) ->
                destFun (typeSubst' theta t) = Right (typeSubst' theta a, typeSubst' theta b)
destFunSubst theta (TyVar _) a b prf = absurd prf
destFunSubst theta (TyApp n []) a b prf = absurd prf
destFunSubst theta (TyApp n [x]) a b prf = absurd prf
destFunSubst theta (TyApp n (x :: y :: z :: rest)) a b prf = absurd prf
destFunSubst theta (TyApp n [x, y]) a b prf with (n == NFun) proof pN
  destFunSubst theta (TyApp n [x, y]) a b prf | False = absurd prf
  destFunSubst theta (TyApp n [x, y]) a b prf | True =
    rewrite sym (fst (pairInj (rightInj prf))) in
    rewrite sym (snd (pairInj (rightInj prf))) in Refl
    where
      rightInj : Right u = Right v -> u = v
      rightInj Refl = Refl
      pairInj : the (c, d) u = the (c, d) v -> (fst u = fst v, snd u = snd v)
      pairInj Refl = (Refl, Refl)

mutual
  export
  typeOccurs : Name -> HType -> Bool
  typeOccurs n (TyVar m)      = n == m
  typeOccurs n (TyApp _ args) = typeOccursList n args

  typeOccursList : Name -> List HType -> Bool
  typeOccursList _ []        = False
  typeOccursList n (a :: as) = typeOccurs n a || typeOccursList n as

-- A total order on types.  `TyVar` sorts before `TyApp`.
mutual
  export
  typeOrd : HType -> HType -> Ordering
  typeOrd (TyVar na) (TyVar nb) = compare na nb
  typeOrd (TyVar _) (TyApp _ _) = LT
  typeOrd (TyApp _ _) (TyVar _) = GT
  typeOrd (TyApp na aargs) (TyApp nb bargs) =
    case compare na nb of
      EQ => case compare (length aargs) (length bargs) of
              EQ => typeOrdList aargs bargs
              o  => o
      o  => o

  typeOrdList : List HType -> List HType -> Ordering
  typeOrdList [] [] = EQ
  typeOrdList (x :: xs) (y :: ys) =
    case typeOrd x y of
      EQ => typeOrdList xs ys
      o  => o
  typeOrdList _ _ = EQ

joinBy : String -> List String -> String
joinBy _ []          = ""
joinBy _ [x]         = x
joinBy sep (x :: xs) = x ++ sep ++ joinBy sep xs

mutual
  htypeShow : HType -> String
  htypeShow (TyVar n) = "'" ++ show n
  htypeShow (TyApp NFun [dom, rng]) =
    let d  = htypeShow dom
        ds = if isFun dom then "(" ++ d ++ ")" else d
     in ds ++ " -> " ++ htypeShow rng
  htypeShow (TyApp n []) = show n
  htypeShow (TyApp n args) = show n ++ "(" ++ joinBy ", " (htypeShowList args) ++ ")"

  htypeShowList : List HType -> List String
  htypeShowList []        = []
  htypeShowList (a :: as) = htypeShow a :: htypeShowList as

export
Show HType where
  show = htypeShow

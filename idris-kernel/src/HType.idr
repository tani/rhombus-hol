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

%default covering


-- `HType` and `List HType` are mutually structurally recursive, and Idris2's
-- termination checker only sees through that when the two functions are
-- declared together in one `mutual` block -- routing the list case through a
-- higher-order helper (as `Eq`'s default `/=`, or `Data.List`'s `==`, would)
-- hides the structural decrease and the checker rejects it as possibly
-- looping.  So types-and-terms equality below is hand-written, not derived.
mutual
  public export
  data HType : Type where
    TyVar : String -> HType
    TyApp : String -> List HType -> HType

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

export
boolTy : HType
boolTy = TyApp "bool" []

export
mkFun : HType -> HType -> HType
mkFun dom rng = TyApp "fun" [dom, rng]

export
isFun : HType -> Bool
isFun (TyApp "fun" [_, _]) = True
isFun _                    = False

-- Throws if `t` is not a function type; callers that are not sure should ask
-- `isFun` first.
export
destFun : HType -> Either String (HType, HType)
destFun (TyApp "fun" [dom, rng]) = Right (dom, rng)
destFun _                        = Left "not a function type"

-- Type variables, in left-to-right order of first occurrence, without
-- duplicates.  Order matters: it is what makes generated axioms
-- deterministic.
addVar : String -> List String -> List String
addVar n acc = if n `elem` acc then acc else acc ++ [n]

mutual
  -- Type variables, in left-to-right order of first occurrence, without
  -- duplicates.  Order matters: it is what makes generated axioms
  -- deterministic.
  export
  typeVars : HType -> List String
  typeVars t = walkType t []

  walkType : HType -> List String -> List String
  walkType (TyVar n) acc = addVar n acc
  walkType (TyApp _ args) acc = walkTypeList args acc

  walkTypeList : List HType -> List String -> List String
  walkTypeList [] acc = acc
  walkTypeList (a :: as) acc = walkTypeList as (walkType a acc)

mutual
  export
  typeSubst : SortedMap String HType -> HType -> HType
  typeSubst theta t =
    if null (SortedMap.toList theta) then t else typeSubst' theta t

  typeSubst' : SortedMap String HType -> HType -> HType
  typeSubst' theta (TyVar n)      = fromMaybe (TyVar n) (SortedMap.lookup n theta)
  typeSubst' theta (TyApp n args) = TyApp n (typeSubstList theta args)

  typeSubstList : SortedMap String HType -> List HType -> List HType
  typeSubstList _     []        = []
  typeSubstList theta (a :: as) = typeSubst' theta a :: typeSubstList theta as

-- One-way matching: extend `acc` so that `typeSubst result pat == t`.
-- `Nothing` when no such extension exists.
mutual
  export
  typeMatch : HType -> HType -> SortedMap String HType -> Maybe (SortedMap String HType)
  typeMatch (TyVar n) t acc =
    case SortedMap.lookup n acc of
      Nothing   => Just (insert n t acc)
      Just prev => if prev == t then Just acc else Nothing
  typeMatch (TyApp n pargs) (TyApp n2 targs) acc =
    if n == n2 then typeMatchList pargs targs acc else Nothing
  typeMatch _ _ _ = Nothing

  typeMatchList : List HType -> List HType -> SortedMap String HType
                -> Maybe (SortedMap String HType)
  typeMatchList [] [] a = Just a
  typeMatchList (p :: ps) (q :: qs) a = do
    a2 <- typeMatch p q a
    typeMatchList ps qs a2
  typeMatchList _ _ _ = Nothing

mutual
  export
  typeOccurs : String -> HType -> Bool
  typeOccurs n (TyVar m)      = n == m
  typeOccurs n (TyApp _ args) = typeOccursList n args

  typeOccursList : String -> List HType -> Bool
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
  htypeShow (TyVar n) = "'" ++ n
  htypeShow (TyApp "fun" [dom, rng]) =
    let d  = htypeShow dom
        ds = if isFun dom then "(" ++ d ++ ")" else d
     in ds ++ " -> " ++ htypeShow rng
  htypeShow (TyApp n []) = n
  htypeShow (TyApp n args) = n ++ "(" ++ joinBy ", " (htypeShowList args) ++ ")"

  htypeShowList : List HType -> List String
  htypeShowList []        = []
  htypeShowList (a :: as) = htypeShow a :: htypeShowList as

export
Show HType where
  show = htypeShow

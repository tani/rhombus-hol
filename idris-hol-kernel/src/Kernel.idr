module Kernel
-- The LCF kernel, ported from
-- rhombus-hol-lib/rhombus/hol/private/kernel.rhm.
--
-- `Stamp`, `Thm` and `Theory` are `export`, not `public export`, so their
-- constructors are private to this module: outside it they can only be
-- built by the ten rules and the extension principles, and only be read
-- through the accessors below.  That is the same boundary the Rhombus
-- kernel draws with `authentic` / `constructor ~none` / an unexported
-- `internal` constructor.  Everything this module proves is stated about
-- values reachable that way.
--
-- The guarantee is an *Idris-level* one and does not survive compilation:
-- the Racket backend represents these as bare tagged vectors, so a Racket
-- caller can still fabricate one.  A wiring that hands this kernel a
-- caller-built `Thm` therefore gets no benefit from the proofs below --
-- which is exactly why the intended use is to have this kernel construct
-- every theorem itself from a replayed derivation, rather than to accept
-- theorems across the FFI boundary.  See ../README.md and ../../PLAN.md.

import Data.List
import Data.Maybe
import Data.SortedMap
import HType
import Term

%default total


-- -- lineage --------------------------------------------------------------

-- Every theory node has a unique identity, and carries the set of identities
-- of all its ancestors (itself included).  A linear counter is not enough:
-- two sibling extensions of one base theory must stay incomparable, or a
-- theorem from one can be combined with a theorem from the other to prove
-- something false.  See the Rhombus kernel's comment for the concrete
-- example.
--
-- Identity is a caller-supplied opaque `Nat` token, not a counter Idris
-- mints itself: Idris has no pure "uninterned symbol" primitive, and a
-- kernel that minted its own identities would need either global mutable
-- state (ruled out -- see the Rhombus kernel's comment on why) or a counter
-- threaded through every caller. The Racket host already has exactly the
-- right primitive (`gensym`), used for this same purpose by the Rhombus
-- kernel today, so extension functions below take the fresh token as a
-- plain argument instead of returning one.  `ancestors` is a plain `List
-- Nat` rather than a `SortedSet`: it stays small (one entry per
-- extension in a lineage), and a `List` compiles to a bare Racket list with
-- no embedded interface-dictionary closures, which is what makes
-- constructing kernel values from the Racket side of the FFI boundary
-- tractable.
export
record Stamp where
  constructor MkStamp
  stampId    : Nat
  stampGen   : Nat
  ancestors  : List Nat

export
descends : Stamp -> Stamp -> Bool
descends a b = stampId a `elem` ancestors b

export
freshStamp : Nat -> Stamp
freshStamp fresh = MkStamp fresh 0 [fresh]

export
nextStamp : Nat -> Stamp -> Stamp
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

-- `nameEqRefl`/`nameEqSound` (the two axioms about `String`'s
-- primitive equality) live in `HType.idr`, next to the `HType` equality
-- soundness they ground.

-- `elem` here folds with `||` seeded at `True` once the head matches, and
-- `foldl` does not short-circuit -- it walks every remaining element
-- regardless of the accumulator -- so showing the fold "stays `True`" over
-- an arbitrary tail needs its own induction, not just unfolding `nameEqRefl`.
orTrueAbsorbs : (p : a -> Bool) -> (xs : List a) -> foldl (\acc, e => acc || p e) True xs = True
orTrueAbsorbs p [] = Refl
orTrueAbsorbs p (x :: xs) = orTrueAbsorbs p xs

export
elemSelf : (x : Nat) -> (xs : List Nat) -> elem x (x :: xs) = True
elemSelf x xs = rewrite natEqRefl x in orTrueAbsorbs _ xs

-- Every `Stamp` this kernel ever constructs contains its own identity in
-- its own ancestor set -- by construction, `freshStamp`/`nextStamp` always
-- cons the fresh id onto the front of `ancestors`. This is exactly what
-- makes `descends` reflexive for any stamp this kernel could actually
-- produce (an arbitrary hand-built `Stamp` need not satisfy it, but
-- nothing in `Kernel` builds one any other way).
export
descendsSelfFresh : (fresh : Nat) -> descends (freshStamp fresh) (freshStamp fresh) = True
descendsSelfFresh fresh = elemSelf fresh []

export
descendsSelfNext : (fresh : Nat) -> (prev : Stamp) ->
                    descends (nextStamp fresh prev) (nextStamp fresh prev) = True
descendsSelfNext fresh prev = elemSelf fresh (ancestors prev)

-- Stated in the folded-out form for the same reason as `orTrueAbsorbs`
-- above: `rewrite` will not normalise `elem` far enough to expose the
-- comparison, so the step lemma is proved about the fold and `elemCons`
-- then goes through by conversion alone.
orFalseCons : (p : a -> Bool) -> (y : a) -> (xs : List a) -> p y = False ->
               foldl (\acc, e => acc || p e) False xs = False ->
               foldl (\acc, e => acc || p e) False (y :: xs) = False
orFalseCons p y xs py miss = rewrite py in miss

-- `elem`'s step compares `x == e`, sought element on the *left*.
export
elemCons : (x, y : Nat) -> (xs : List Nat) ->
            x == y = False -> elem x xs = False -> elem x (y :: xs) = False
elemCons x y xs neq miss = orFalseCons (x ==) y xs neq miss

-- The property the ancestor *set* exists for, and the one thing the
-- section comment above asserts but nothing previously stated as a
-- theorem: two sibling extensions of one base theory are incomparable in
-- both directions. Without it a theorem proved in one sibling could be
-- fed to a rule checking membership in the other, which is exactly the
-- unsoundness the Rhombus kernel's comment describes. A plain generation
-- counter cannot support this -- both siblings would get the same number.
--
-- The freshness of the two tokens is a genuine precondition, not an
-- omission: Idris cannot mint identities (see the section comment), so
-- distinctness is what the caller must supply and what the Racket host's
-- `gensym` actually provides.
export
siblingsIncomparable :
  (f1, f2 : Nat) -> (prev : Stamp) ->
  f1 == f2 = False ->
  elem f1 (ancestors prev) = False ->
  elem f2 (ancestors prev) = False ->
  (descends (nextStamp f1 prev) (nextStamp f2 prev) = False,
   descends (nextStamp f2 prev) (nextStamp f1 prev) = False)
siblingsIncomparable f1 f2 prev neq miss1 miss2 =
  (elemCons f1 f2 (ancestors prev) neq miss1,
   elemCons f2 f1 (ancestors prev) (natEqSym f1 f2 neq) miss2)

-- The same, for two independently rooted theories: distinct roots never
-- descend from one another, so theorems cannot migrate between them.
export
rootsIncomparable :
  (f1, f2 : Nat) -> f1 == f2 = False ->
  (descends (freshStamp f1) (freshStamp f2) = False,
   descends (freshStamp f2) (freshStamp f1) = False)
rootsIncomparable f1 f2 neq =
  (elemCons f1 f2 [] neq Refl,
   elemCons f2 f1 [] (natEqSym f1 f2 neq) Refl)

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

export
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
export
record Theory where
  constructor MkTheory
  tyops  : List (Name, Nat)
  consts : List (Name, HType)
  axioms : List Thm
  defs   : List (Name, Thm)
  thyStamp : Stamp

export
typeArity : Theory -> Name -> Maybe Nat
typeArity thy n = lookup n (tyops thy)

export
constType : Theory -> Name -> Maybe HType
constType thy n = lookup n (consts thy)

export
axiomsOf : Theory -> List Thm
axiomsOf = axioms

-- `Theory`'s fields are private (see the record's comment), so clients that
-- need to ask a lineage question go through this rather than the field.
export
theoryStamp : Theory -> Stamp
theoryStamp = thyStamp

export
definitionOf : Theory -> Name -> Maybe Thm
definitionOf thy n = lookup n (defs thy)

inTheory : Theory -> Thm -> Either String ()
inTheory thy th =
  if descends (thmStamp th) (thyStamp thy)
    then Right ()
    else Left "theorem was not proved in this theory or an ancestor of it"

-- `fresh` is an opaque identity token supplied by the caller (see the
-- comment on `Stamp` above) -- one per theory-extending call, never reused.
export
initialTheory : Nat -> Theory
initialTheory fresh =
  MkTheory [(NBool, 0), (NFun, 2)]
           [(NEq, mkFun (TyVar NAlpha) (mkFun (TyVar NAlpha) boolTy))]
           []
           []
           (freshStamp fresh)

extend : Theory -> Nat
       -> List (Name, Nat) -> List (Name, HType)
       -> List Thm -> List (Name, Thm)
       -> Theory
extend thy fresh tyops' consts' axioms' defs' =
  MkTheory tyops' consts' axioms' defs' (nextStamp fresh (thyStamp thy))

-- -- well-formedness ----------------------------------------------------------

-- The argument walk is spelled out as `checkTypeList` rather than
-- `traverse_ (checkType thy)`: same behaviour (stop at the first `Left`),
-- but `traverse_` is built from `Foldable`/`Applicative` methods whose
-- bodies do not reduce during typechecking here, which would block every
-- proof that a particular type checks out.
mutual
  export
  checkType : Theory -> HType -> Either String ()
  checkType _   (TyVar _)    = Right ()
  checkType thy (TyApp n args) =
    case typeArity thy n of
      Nothing => Left ("undeclared type constructor: " ++ show n)
      Just ar =>
        if ar /= length args
          then Left "type constructor arity mismatch"
          else checkTypeList thy args

  export
  checkTypeList : Theory -> List HType -> Either String ()
  checkTypeList thy [] = Right ()
  checkTypeList thy (a :: as) =
    case checkType thy a of
      Left e   => Left e
      Right () => checkTypeList thy as

-- Exported (and used by `checkOpenTerm`'s `BVar` case below, rather than a
-- separate local copy) so the substitution lemma in `Term.idr` reasons
-- about the exact same function `checkOpenTerm` actually calls.
-- The empty-list clause comes first so `nthEnv k []` reduces to `Nothing`
-- for an *abstract* `k`: with the `Nat` clauses first, Idris's case tree
-- splits on the index before the list, and the proofs below (which hit
-- exactly that shape) would get stuck.  Behaviour is identical either way.
public export
nthEnv : Nat -> List HType -> Maybe HType
nthEnv _ [] = Nothing
nthEnv Z (x :: _) = Just x
nthEnv (S k) (_ :: xs) = nthEnv k xs

-- A constant's check is the one case that depends on neither the
-- environment nor anything else structural, so it is factored out: as a
-- clause body that is a single call not mentioning `env`, it reduces the
-- way `FVar`'s does.  Inline (as a `do` block in the clause), Idris's
-- unifier compares two `checkOpenTerm` applications argument-wise, fails on
-- the differing environments, and never unfolds far enough to notice
-- neither side uses it -- which blocks the weakening and substitution
-- lemmas below.
checkConstUse : Theory -> Name -> HType -> Either String ()
checkConstUse thy n ty = do
  checkType thy ty
  case constType thy n of
    Nothing => Left ("undeclared constant: " ++ show n)
    Just gty => case typeMatch gty ty [] of
                  Nothing => Left "constant used at a non-instance type"
                  Just _  => Right ()

-- Likewise factored out (see `checkConstUse`): taking the *result* of the
-- environment lookup rather than doing it inline keeps the `BVar` clause a
-- single call, which is what lets the proofs below unfold it.
checkBVarUse : Theory -> HType -> Maybe HType -> Either String ()
checkBVarUse thy ty Nothing = Left "term has an unbound de Bruijn index"
checkBVarUse thy ty (Just ety) =
  if ety == ty
    then checkType thy ty
    else Left "bound variable's type does not match its binder"

-- Same treatment for the application case, taking the four things that
-- vary -- the two sub-checks and the two operand types -- as arguments.
-- Beyond keeping the clause a single call, this puts exactly the
-- expressions the substitution lemma has to rewrite (`checkOpenTerm` of
-- each sub-term, `typeOf` of each sub-term) in argument position, where
-- `rewrite` can reach them without unfolding anything.
checkCombUse : Either String () -> Either String () ->
               Either String HType -> Either String HType -> Either String ()
checkCombUse fchk xchk ftyE xtyE = do
  fchk
  xchk
  fty <- ftyE
  if not (isFun fty)
    then Left "operator is not a function"
    else do
      (dom, _) <- destFun fty
      xty <- xtyE
      if dom == xty then Right () else Left "ill-typed application"

-- `env` holds the argument types of the enclosing binders, innermost first.
export
checkOpenTerm : Theory -> Term -> List HType -> Either String ()
checkOpenTerm thy (FVar _ ty) _ = checkType thy ty
checkOpenTerm thy (BVar i ty) env = checkBVarUse thy ty (nthEnv i env)
checkOpenTerm thy (Const n ty) _ = checkConstUse thy n ty
checkOpenTerm thy (Abs aty b) env = do
  checkType thy aty
  checkOpenTerm thy b (aty :: env)
checkOpenTerm thy (Comb f x) env =
  checkCombUse (checkOpenTerm thy f env) (checkOpenTerm thy x env) (typeOf f) (typeOf x)

export
checkTerm : Theory -> Term -> Either String ()
checkTerm thy t = checkOpenTerm thy t []

-- -- soundness proofs: type safety -----------------------------------------
--
-- The base safety property every derived-layer caller relies on `typeOf`
-- for: a term `checkOpenTerm`/`checkTerm` accepts always has a well-defined
-- type. Without this, a term the kernel considers well-formed could still
-- make `typeOf` fail later (e.g. inside `mkEq`, or a derived rule) --
-- exactly the "`typeOf` lies" failure mode the Rhombus kernel's own comment
-- on `BVar` warns about, for a different reason (a mismatched binder type,
-- which `checkOpenTerm`'s `env` threading already rules out). This proof
-- rules out the other half: that `typeOf` fails outright.
--
-- No separate lemma about `isFun`/`destFun` agreeing is needed: `Comb`'s
-- case of `checkOpenTerm` already binds `typeOf f`, checks `isFun`, and
-- binds `destFun fty` explicitly as part of its own definition, so every
-- fact `typeOf`'s `Comb` case needs is already sitting inside the
-- hypothesis `prf` -- the proof is unfolding `prf` layer by layer (one
-- `with` per bind `checkOpenTerm`/`typeOf` themselves perform), not a
-- separate induction. `Abs` is the one case that genuinely recurses: `typeOf
-- (Abs aty body)` needs `typeOf body` to succeed, which `checkOpenTerm`'s
-- `Abs` case does not bind directly (it only checks `body`'s
-- well-formedness), so that one call goes through the inductive hypothesis.
export
checkTermTypeOfSound : (thy : Theory) -> (t : Term) -> (env : List HType) ->
                        checkOpenTerm thy t env = Right () ->
                        (ty : HType ** typeOf t = Right ty)
checkTermTypeOfSound thy (FVar n ty) env prf = (ty ** Refl)
checkTermTypeOfSound thy (BVar i ty) env prf = (ty ** Refl)
checkTermTypeOfSound thy (Const n ty) env prf = (ty ** Refl)
checkTermTypeOfSound thy (Abs aty b) env prf with (checkType thy aty) proof pCT
  checkTermTypeOfSound thy (Abs aty b) env prf | Left e = absurd prf
  checkTermTypeOfSound thy (Abs aty b) env prf | Right () =
    let (bty ** bPrf) = checkTermTypeOfSound thy b (aty :: env) prf in
    (mkFun aty bty ** rewrite bPrf in Refl)
checkTermTypeOfSound thy (Comb f x) env prf
    with (checkOpenTerm thy f env) proof p1
  checkTermTypeOfSound thy (Comb f x) env prf | Left e = absurd prf
  checkTermTypeOfSound thy (Comb f x) env prf | Right ()
      with (checkOpenTerm thy x env) proof p2
    checkTermTypeOfSound thy (Comb f x) env prf | Right () | Left e = absurd prf
    checkTermTypeOfSound thy (Comb f x) env prf | Right () | Right ()
        with (typeOf f) proof p3
      checkTermTypeOfSound thy (Comb f x) env prf | Right () | Right () | Left e = absurd prf
      checkTermTypeOfSound thy (Comb f x) env prf | Right () | Right () | Right fty
          with (isFun fty) proof pIsFun
        checkTermTypeOfSound thy (Comb f x) env prf | Right () | Right () | Right fty | False =
          absurd prf
        checkTermTypeOfSound thy (Comb f x) env prf | Right () | Right () | Right fty | True
            with (destFun fty) proof p5
          checkTermTypeOfSound thy (Comb f x) env prf | Right () | Right () | Right fty | True | Left e =
            absurd prf
          checkTermTypeOfSound thy (Comb f x) env prf | Right () | Right () | Right fty | True | Right (dom, rng)
              with (typeOf x) proof p6
            checkTermTypeOfSound thy (Comb f x) env prf | Right () | Right () | Right fty | True | Right (dom, rng) | Left e =
              absurd prf
            checkTermTypeOfSound thy (Comb f x) env prf | Right () | Right () | Right fty | True | Right (dom, rng) | Right xty =
              (rng ** Refl)

-- -- soundness proof: substitution preserves typing (subject reduction) ---
--
-- This is the theorem `shiftPreservesType` was building toward: `BETA`'s
-- redex `Comb (Abs aty body) arg` reduces to `substBvar arg body`, and this
-- proves that reduction never changes the term's type -- the classic
-- "subject reduction for beta" property, generalized to an *arbitrary*
-- redex the way `kernel.rhm`'s own comment on `BETA` says this kernel's
-- locally-nameless representation allows (not just the trivial `(\v. b)
-- v`).
--
-- Unlike `shiftPreservesType`, this genuinely needs a well-formedness
-- hypothesis: a `BVar j`'s type annotation only reflects the substituted
-- term's real type once `checkOpenTerm`'s `env` has confirmed every
-- occurrence of that binder agrees on it. Extracting "agrees" as a
-- *propositional* equality from the `Bool` check `checkOpenTerm` actually
-- performs is exactly what `HType.htypeEqSound` (and `Name.natEqSound`,
-- for the de Bruijn index comparison) exist for.

justInjective : Just a = Just b -> a = b
justInjective Refl = Refl

rightInjective : Right a = Right b -> a = b
rightInjective Refl = Refl

-- The general substitution lemma: substituting a term of type `jty` for
-- the de Bruijn index `j` never changes the type of a well-formed term,
-- provided the replacement really does have type `jty`. `j`/`env` grow
-- together as the induction descends under binders (`Abs`'s case
-- increments both), which is what lets `jty` -- the type of the position
-- being substituted -- stay fixed throughout.
export
substAtTypeSound : (thy : Theory) -> (j : Nat) -> (env : List HType) -> (jty : HType) ->
                    (s, t : Term) ->
                    nthEnv j env = Just jty ->
                    checkOpenTerm thy t env = Right () ->
                    typeOf s = Right jty ->
                    typeOf (substAt j s t) = typeOf t
substAtTypeSound thy j env jty s (FVar n ty) njEq wf styOf = Refl
substAtTypeSound thy j env jty s (Const n ty) njEq wf styOf = Refl
substAtTypeSound thy j env jty s (BVar i ty) njEq wf styOf with (i == j) proof pij
  substAtTypeSound thy j env jty s (BVar i ty) njEq wf styOf | False = Refl
  substAtTypeSound thy j env jty s (BVar i ty) njEq wf styOf | True
      with (nthEnv i env) proof pNth
    substAtTypeSound thy j env jty s (BVar i ty) njEq wf styOf | True | Nothing =
      absurd wf
    substAtTypeSound thy j env jty s (BVar i ty) njEq wf styOf | True | Just ety
        with (ety == ty) proof pEtyTy
      substAtTypeSound thy j env jty s (BVar i ty) njEq wf styOf | True | Just ety | False =
        absurd wf
      substAtTypeSound thy j env jty s (BVar i ty) njEq wf styOf | True | Just ety | True =
        let iEqJ = natEqSound i j pij in
        let etyEqTy = htypeEqSound ety ty pEtyTy in
        let nthAtJ = rewrite sym iEqJ in pNth in
        let etyEqJty = justInjective (trans (sym nthAtJ) njEq) in
        let tyEqJty = trans (sym etyEqTy) etyEqJty in
        trans (shiftPreservesType (natToInteger j) 0 s)
              (trans styOf (cong Right (sym tyEqJty)))
substAtTypeSound thy j env jty s (Comb f x) njEq wf styOf
    with (checkOpenTerm thy f env) proof p1
  substAtTypeSound thy j env jty s (Comb f x) njEq wf styOf | Left e = absurd wf
  substAtTypeSound thy j env jty s (Comb f x) njEq wf styOf | Right () =
    cong (\ety => ety >>= (\fty => case destFun fty of
                                      Right (_, rng) => Right rng
                                      Left err => Left err))
         (substAtTypeSound thy j env jty s f njEq p1 styOf)
substAtTypeSound thy j env jty s (Abs aty b) njEq wf styOf
    with (checkType thy aty) proof pCT
  substAtTypeSound thy j env jty s (Abs aty b) njEq wf styOf | Left e = absurd wf
  substAtTypeSound thy j env jty s (Abs aty b) njEq wf styOf | Right () =
    cong (map (mkFun aty))
         (substAtTypeSound thy (S j) (aty :: env) jty s b njEq wf styOf)

-- Specializing the general lemma to `BETA`'s actual shape: substituting the
-- redex's argument for the one bound variable an `Abs` introduces.
export
substBvarPreservesType : (thy : Theory) -> (aty : HType) -> (body, arg : Term) -> (env : List HType) ->
                          checkOpenTerm thy body (aty :: env) = Right () ->
                          typeOf arg = Right aty ->
                          typeOf (substBvar arg body) = typeOf body
substBvarPreservesType thy aty body arg env wfBody argTy =
  trans (shiftPreservesType (-1) 0 (substAt 0 arg body))
        (substAtTypeSound thy 0 (aty :: env) aty arg body Refl wfBody argTy)

-- -- soundness proof: substitution preserves well-formedness --------------
--
-- `substBvarPreservesType` says beta reduction keeps the *type*.  This
-- section proves the stronger, and for `BETA` the decisive, claim: the
-- reduct is still a well-formed term of the same theory.  `BETA` checks
-- only its redex (`checkTerm thy t`) and never re-checks `substBvar arg
-- body`, so without this the rule would be taking on faith exactly what
-- `check_term` exists to establish.  Together with `substBvarClosed` (in
-- `Term.idr`) and `substBvarPreservesType`, it closes that gap.
--
-- The statement is fixed at the top-level environment (`checkTerm` passes
-- `[]`), which is how `BETA` always calls it.  That is what keeps `shift`'s
-- `Integer` index arithmetic out of the proof entirely: a term well-formed
-- in the empty environment is closed, and `shiftClosedId` makes every
-- `shift` in sight the identity.  The induction still descends under
-- binders, so it is stated over an arbitrary prefix `envH` of binders
-- entered so far, with the substituted binder pinned at the end
-- (`envH ++ [jty]`).

nthEnvAppend : (i : Nat) -> (env, env2 : List HType) -> (x : HType) ->
                nthEnv i env = Just x -> nthEnv i (env ++ env2) = Just x
nthEnvAppend _     []        env2 x prf = absurd prf
nthEnvAppend Z     (h :: hs) env2 x prf = prf
nthEnvAppend (S k) (h :: hs) env2 x prf = nthEnvAppend k hs env2 x prf

nthEnvAtEnd : (envH : List HType) -> (jty : HType) ->
               nthEnv (length envH) (envH ++ [jty]) = Just jty
nthEnvAtEnd []        jty = Refl
nthEnvAtEnd (h :: hs) jty = nthEnvAtEnd hs jty

-- Any index other than the substituted one that resolves in `envH ++ [jty]`
-- already resolved, to the same type, in `envH` alone.
nthEnvBelow : (i : Nat) -> (envH : List HType) -> (jty, ety : HType) ->
               nthEnv i (envH ++ [jty]) = Just ety -> i == length envH = False ->
               nthEnv i envH = Just ety
nthEnvBelow Z     []        jty ety prf neq = absurd neq
nthEnvBelow (S k) []        jty ety prf neq = absurd prf
nthEnvBelow Z     (h :: hs) jty ety prf neq = prf
nthEnvBelow (S k) (h :: hs) jty ety prf neq = nthEnvBelow k hs jty ety prf neq

nthEnvBound : (i : Nat) -> (env : List HType) -> (x : HType) ->
               nthEnv i env = Just x -> i < length env = True
nthEnvBound _     []        x prf = absurd prf
nthEnvBound Z     (h :: hs) x prf = Refl
nthEnvBound (S k) (h :: hs) x prf = nthEnvBound k hs x prf

-- Weakening: entering more binders never invalidates a term.  Only the
-- `BVar` case does any work, and it is exactly `nthEnvAppend`; every other
-- case either ignores the environment or is structural.
export
checkWeakenRight : (thy : Theory) -> (t : Term) -> (env, env2 : List HType) ->
                    checkOpenTerm thy t env = Right () ->
                    checkOpenTerm thy t (env ++ env2) = Right ()
checkWeakenRight thy (FVar n ty) env env2 prf = prf
checkWeakenRight thy (Const n ty) env env2 prf = prf
checkWeakenRight thy (BVar i ty) env env2 prf with (nthEnv i env) proof pN
  checkWeakenRight thy (BVar i ty) env env2 prf | Nothing = absurd prf
  checkWeakenRight thy (BVar i ty) env env2 prf | Just ety =
    rewrite nthEnvAppend i env env2 ety pN in prf
checkWeakenRight thy (Comb f x) env env2 prf
    with (checkOpenTerm thy f env) proof p1
  checkWeakenRight thy (Comb f x) env env2 prf | Left e = absurd prf
  checkWeakenRight thy (Comb f x) env env2 prf | Right ()
      with (checkOpenTerm thy x env) proof p2
    checkWeakenRight thy (Comb f x) env env2 prf | Right () | Left e = absurd prf
    checkWeakenRight thy (Comb f x) env env2 prf | Right () | Right () =
      rewrite checkWeakenRight thy f env env2 p1 in
      rewrite checkWeakenRight thy x env env2 p2 in
      prf
checkWeakenRight thy (Abs aty b) env env2 prf with (checkType thy aty) proof pCT
  checkWeakenRight thy (Abs aty b) env env2 prf | Left e = absurd prf
  checkWeakenRight thy (Abs aty b) env env2 prf | Right () =
    checkWeakenRight thy b (aty :: env) env2 prf

-- The well-formedness counterpart of `substAtTypeSound`.
export
substAtCheckSound : (thy : Theory) -> (envH : List HType) -> (jty : HType) ->
                     (s, t : Term) ->
                     checkOpenTerm thy t (envH ++ [jty]) = Right () ->
                     checkOpenTerm thy s [] = Right () ->
                     closedAt 0 s = True ->
                     typeOf s = Right jty ->
                     checkOpenTerm thy (shift (-1) (length envH) (substAt (length envH) s t)) envH
                       = Right ()
substAtCheckSound thy envH jty s (FVar n ty) prf sChk sClosed styOf = prf
substAtCheckSound thy envH jty s (Const n ty) prf sChk sClosed styOf = prf
substAtCheckSound thy envH jty s (BVar i ty) prf sChk sClosed styOf
    with (i == length envH) proof pij
  substAtCheckSound thy envH jty s (BVar i ty) prf sChk sClosed styOf | True =
    -- `s` is closed, so neither the shift `substAt` applies when it plants
    -- `s`, nor the outer gap-closing shift, touches it.
    rewrite shiftClosedId (natToInteger (length envH)) 0 s sClosed in
    rewrite shiftClosedId (-1) (length envH) s (closedAtFromZero (length envH) s sClosed) in
    checkWeakenRight thy s [] envH sChk
  -- A different index: it survives substitution, and since it resolves
  -- inside `envH` it is strictly below the cutoff, so the gap-closing shift
  -- is the identity on it too.
  substAtCheckSound thy envH jty s (BVar i ty) prf sChk sClosed styOf | False
      with (nthEnv i (envH ++ [jty])) proof pN
    substAtCheckSound thy envH jty s (BVar i ty) prf sChk sClosed styOf | False | Nothing =
      absurd prf
    substAtCheckSound thy envH jty s (BVar i ty) prf sChk sClosed styOf | False | Just ety =
      let below = nthEnvBelow i envH jty ety pN pij in
      rewrite nthEnvBound i envH ety below in
      rewrite below in prf
substAtCheckSound thy envH jty s (Comb f x) prf sChk sClosed styOf
    with (checkOpenTerm thy f (envH ++ [jty])) proof p1
  substAtCheckSound thy envH jty s (Comb f x) prf sChk sClosed styOf | Left e = absurd prf
  substAtCheckSound thy envH jty s (Comb f x) prf sChk sClosed styOf | Right ()
      with (checkOpenTerm thy x (envH ++ [jty])) proof p2
    substAtCheckSound thy envH jty s (Comb f x) prf sChk sClosed styOf | Right () | Left e =
      absurd prf
    substAtCheckSound thy envH jty s (Comb f x) prf sChk sClosed styOf | Right () | Right () =
      -- Both sub-terms stay well-formed (induction) and keep their types
      -- (`substAtTypeSound` + `shiftPreservesType`), so every check the
      -- `Comb` case performs lands exactly where it did before.
      rewrite substAtCheckSound thy envH jty s f p1 sChk sClosed styOf in
      rewrite substAtCheckSound thy envH jty s x p2 sChk sClosed styOf in
      rewrite trans (shiftPreservesType (-1) (length envH) (substAt (length envH) s f))
                    (substAtTypeSound thy (length envH) (envH ++ [jty]) jty s f
                                      (nthEnvAtEnd envH jty) p1 styOf) in
      rewrite trans (shiftPreservesType (-1) (length envH) (substAt (length envH) s x))
                    (substAtTypeSound thy (length envH) (envH ++ [jty]) jty s x
                                      (nthEnvAtEnd envH jty) p2 styOf) in
      prf
substAtCheckSound thy envH jty s (Abs aty b) prf sChk sClosed styOf
    with (checkType thy aty) proof pCT
  substAtCheckSound thy envH jty s (Abs aty b) prf sChk sClosed styOf | Left e = absurd prf
  substAtCheckSound thy envH jty s (Abs aty b) prf sChk sClosed styOf | Right () =
    substAtCheckSound thy (aty :: envH) jty s b prf sChk sClosed styOf

-- -- BETA's reduct is well-formed: putting it together ---------------------
--
-- The three preservation results above (`substBvarPreservesType`,
-- `substBvarClosed`, `substAtCheckSound`) are stated over the pieces of a
-- redex.  These lemmas take a checked redex apart into those pieces, so the
-- final theorem can be stated the way `BETA` actually meets it: one
-- `checkTerm` on the redex in, one `checkTerm` on the reduct out.

-- Anything well-formed in an environment has no index escaping it.
export
checkClosed : (thy : Theory) -> (t : Term) -> (env : List HType) ->
               checkOpenTerm thy t env = Right () -> closedAt (length env) t = True
checkClosed thy (FVar _ _) env prf = Refl
checkClosed thy (Const _ _) env prf = Refl
checkClosed thy (BVar i ty) env prf with (nthEnv i env) proof pN
  checkClosed thy (BVar i ty) env prf | Nothing = absurd prf
  checkClosed thy (BVar i ty) env prf | Just ety = nthEnvBound i env ety pN
checkClosed thy (Comb f x) env prf with (checkOpenTerm thy f env) proof p1
  checkClosed thy (Comb f x) env prf | Left e = absurd prf
  checkClosed thy (Comb f x) env prf | Right () with (checkOpenTerm thy x env) proof p2
    checkClosed thy (Comb f x) env prf | Right () | Left e = absurd prf
    checkClosed thy (Comb f x) env prf | Right () | Right () =
      rewrite checkClosed thy f env p1 in
      rewrite checkClosed thy x env p2 in Refl
checkClosed thy (Abs aty b) env prf with (checkType thy aty) proof pCT
  checkClosed thy (Abs aty b) env prf | Left e = absurd prf
  checkClosed thy (Abs aty b) env prf | Right () = checkClosed thy b (aty :: env) prf

absCheckBody : (thy : Theory) -> (aty : HType) -> (b : Term) -> (env : List HType) ->
                checkOpenTerm thy (Abs aty b) env = Right () ->
                checkOpenTerm thy b (aty :: env) = Right ()
absCheckBody thy aty b env prf with (checkType thy aty) proof pCT
  absCheckBody thy aty b env prf | Left e = absurd prf
  absCheckBody thy aty b env prf | Right () = prf

combCheckFun : (thy : Theory) -> (f, x : Term) -> (env : List HType) ->
                checkOpenTerm thy (Comb f x) env = Right () ->
                checkOpenTerm thy f env = Right ()
combCheckFun thy f x env prf with (checkOpenTerm thy f env) proof p1
  combCheckFun thy f x env prf | Left e = absurd prf
  combCheckFun thy f x env prf | Right () = Refl

combCheckArg : (thy : Theory) -> (f, x : Term) -> (env : List HType) ->
                checkOpenTerm thy (Comb f x) env = Right () ->
                checkOpenTerm thy x env = Right ()
combCheckArg thy f x env prf with (checkOpenTerm thy f env) proof p1
  combCheckArg thy f x env prf | Left e = absurd prf
  combCheckArg thy f x env prf | Right () with (checkOpenTerm thy x env) proof p2
    combCheckArg thy f x env prf | Right () | Left e = absurd prf
    combCheckArg thy f x env prf | Right () | Right () = Refl

-- A checked redex's argument really does have the binder's argument type:
-- the application check compared them, and `htypeEqSound` turns that
-- comparison into an equality the substitution lemmas can consume.
betaArgType : (thy : Theory) -> (aty : HType) -> (body, arg : Term) -> (env : List HType) ->
               checkOpenTerm thy (Comb (Abs aty body) arg) env = Right () ->
               typeOf arg = Right aty
betaArgType thy aty body arg env prf
    with (checkOpenTerm thy (Abs aty body) env) proof p1
  betaArgType thy aty body arg env prf | Left e = absurd prf
  betaArgType thy aty body arg env prf | Right ()
      with (checkOpenTerm thy arg env) proof p2
    betaArgType thy aty body arg env prf | Right () | Left e = absurd prf
    betaArgType thy aty body arg env prf | Right () | Right ()
        with (typeOf body) proof pB
      betaArgType thy aty body arg env prf | Right () | Right () | Left e = absurd prf
      betaArgType thy aty body arg env prf | Right () | Right () | Right bty
          with (typeOf arg) proof pA
        betaArgType thy aty body arg env prf | Right () | Right () | Right bty | Left e =
          absurd prf
        betaArgType thy aty body arg env prf | Right () | Right () | Right bty | Right xty
            with (aty == xty) proof pEq
          betaArgType thy aty body arg env prf | Right () | Right () | Right bty | Right xty | False =
            absurd prf
          betaArgType thy aty body arg env prf | Right () | Right () | Right bty | Right xty | True =
            cong Right (sym (htypeEqSound aty xty pEq))

-- The theorem `BETA` needs: reducing a well-formed redex yields a
-- well-formed term.  `BETA` checks only its redex and never re-checks the
-- reduct, so this is exactly the obligation the rule leaves implicit.
export
betaCheckSound : (thy : Theory) -> (aty : HType) -> (body, arg : Term) ->
                  checkTerm thy (Comb (Abs aty body) arg) = Right () ->
                  checkTerm thy (substBvar arg body) = Right ()
betaCheckSound thy aty body arg prf =
  let argChk    = combCheckArg thy (Abs aty body) arg [] prf
      bodyChk   = absCheckBody thy aty body [] (combCheckFun thy (Abs aty body) arg [] prf)
      argClosed = checkClosed thy arg [] argChk
      argTy     = betaArgType thy aty body arg [] prf
  in substAtCheckSound thy [] aty arg body bodyChk argChk argClosed argTy

-- `typeOf` of the redex is `typeOf body` once `body` has a type at all, so
-- `substBvarPreservesType`'s "same type as `body`" is the same statement as
-- "same type as the redex"; this just converts between the two forms.
betaTypeSoundAux : (aty : HType) -> (body, arg : Term) ->
                    typeOf (substBvar arg body) = typeOf body ->
                    typeOf (substBvar arg body) = typeOf (Comb (Abs aty body) arg)
betaTypeSoundAux aty body arg eq with (typeOf body) proof pB
  betaTypeSoundAux aty body arg eq | Left e = eq
  betaTypeSoundAux aty body arg eq | Right bty = eq

-- Subject reduction, stated the way `BETA` meets it: the reduct has the
-- same type as the redex it replaced.
export
betaTypeSound : (thy : Theory) -> (aty : HType) -> (body, arg : Term) ->
                 checkTerm thy (Comb (Abs aty body) arg) = Right () ->
                 typeOf (substBvar arg body) = typeOf (Comb (Abs aty body) arg)
betaTypeSound thy aty body arg prf =
  betaTypeSoundAux aty body arg
    (substBvarPreservesType thy aty body arg []
       (absCheckBody thy aty body [] (combCheckFun thy (Abs aty body) arg [] prf))
       (betaArgType thy aty body arg [] prf))

-- And the reduct has no dangling de Bruijn index.
export
betaClosedSound : (thy : Theory) -> (aty : HType) -> (body, arg : Term) ->
                   checkTerm thy (Comb (Abs aty body) arg) = Right () ->
                   isLocallyClosed (substBvar arg body) = True
betaClosedSound thy aty body arg prf =
  let argChk  = combCheckArg thy (Abs aty body) arg [] prf
      bodyChk = absCheckBody thy aty body [] (combCheckFun thy (Abs aty body) arg [] prf)
  in substBvarClosed body arg (checkClosed thy body [aty] bodyChk)
                              (checkClosed thy arg [] argChk)

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
    else Right (Comb (Comb (Const NEq (mkFun lty (mkFun lty boolTy))) l) r)

-- The constant's name is tested with `==` rather than matched as a string
-- literal, for the same reason `destFun` is: a literal pattern leaves
-- `destEq` stuck on an abstract name, and the rules' proofs need to
-- recover an equation's shape from `destEq` having succeeded.
public export
destEq : Term -> Maybe (Term, Term)
destEq (Comb (Comb (Const n _) l) r) = if n == NEq then Just (l, r) else Nothing
destEq _ = Nothing

export
isEq : Term -> Bool
isEq t = isJust (destEq t)

needEq : Thm -> Either String (Term, Term)
needEq th = case destEq (thmConcl th) of
              Nothing => Left "theorem is not an equation"
              Just pr => Right pr

-- -- soundness proofs: rule outputs are well-formed ------------------------
--
-- The rules build their conclusions with `mkEq` and hand the result
-- straight to `MkThm`, never re-checking it.  These lemmas discharge that:
-- an equation built from two checked terms of the same type is itself a
-- checked term.  It is the shared obligation behind `REFL`, `TRANS`,
-- `MK_COMB`, `EQ_MP` and `DEDUCT_ANTISYM_RULE`, all of which conclude with
-- an `mkEq`.
--
-- Unlike the substitution lemmas, this one needs to know the *theory* is
-- sane -- that `fun`, `bool` and `eq` mean what the kernel assumes.  A
-- hand-built `Theory` need not; `initialTheory` does (proved below), and
-- `newTypeMonotone`/`newConstantMonotone` are what carry that forward
-- through extension.

public export
eqGenericType : HType
eqGenericType = mkFun (TyVar NAlpha) (mkFun (TyVar NAlpha) boolTy)

public export
record WellFormedTheory (thy : Theory) where
  constructor MkWellFormedTheory
  funArity  : typeArity thy NFun = Just 2
  boolArity : typeArity thy NBool = Just 0
  eqDeclared : constType thy NEq = Just Kernel.eqGenericType

export
initialTheoryWellFormed : (fresh : Nat) -> WellFormedTheory (initialTheory fresh)
initialTheoryWellFormed fresh = MkWellFormedTheory Refl Refl Refl

export
checkTypeBool : (thy : Theory) -> WellFormedTheory thy -> checkType thy HType.boolTy = Right ()
checkTypeBool thy wf = rewrite boolArity wf in Refl

export
checkTypeFun : (thy : Theory) -> WellFormedTheory thy -> (a, b : HType) ->
                checkType thy a = Right () -> checkType thy b = Right () ->
                checkType thy (mkFun a b) = Right ()
checkTypeFun thy wf a b pa pb =
  rewrite funArity wf in rewrite pa in rewrite pb in Refl

-- The converse for the range: a function type only checks out if its range
-- does.  `typeOf`'s `Comb` case returns exactly that range.
checkTypeFunRange : (thy : Theory) -> (a, b : HType) ->
                     checkType thy (mkFun a b) = Right () -> checkType thy b = Right ()
checkTypeFunRange thy a b prf with (typeArity thy NFun) proof pFA
  checkTypeFunRange thy a b prf | Nothing = absurd prf
  checkTypeFunRange thy a b prf | Just ar with (ar /= 2) proof pAr
    checkTypeFunRange thy a b prf | Just ar | True = absurd prf
    checkTypeFunRange thy a b prf | Just ar | False with (checkType thy a) proof pA
      checkTypeFunRange thy a b prf | Just ar | False | Left e = absurd prf
      checkTypeFunRange thy a b prf | Just ar | False | Right () with (checkType thy b) proof pB
        checkTypeFunRange thy a b prf | Just ar | False | Right () | Left e = absurd prf
        checkTypeFunRange thy a b prf | Just ar | False | Right () | Right () = Refl

-- The same extraction, but starting from `destFun`'s result rather than a
-- syntactic `mkFun`: this is the shape `typeOf`'s `Comb` case produces.
checkTypeDestFunRange : (thy : Theory) -> (fty, dom, rng : HType) ->
                         destFun fty = Right (dom, rng) ->
                         checkType thy fty = Right () ->
                         checkType thy rng = Right ()
checkTypeDestFunRange thy (TyVar _) dom rng pD prf = absurd pD
checkTypeDestFunRange thy (TyApp n []) dom rng pD prf = absurd pD
checkTypeDestFunRange thy (TyApp n [a]) dom rng pD prf = absurd pD
checkTypeDestFunRange thy (TyApp n (a :: b :: c :: rest)) dom rng pD prf = absurd pD
checkTypeDestFunRange thy (TyApp n [a, b]) dom rng pD prf with (n == NFun) proof pN
  checkTypeDestFunRange thy (TyApp n [a, b]) dom rng pD prf | False = absurd pD
  checkTypeDestFunRange thy (TyApp n [a, b]) dom rng pD prf | True
      with (typeArity thy n) proof pFA
    checkTypeDestFunRange thy (TyApp n [a, b]) dom rng pD prf | True | Nothing = absurd prf
    checkTypeDestFunRange thy (TyApp n [a, b]) dom rng pD prf | True | Just ar
        with (ar /= 2) proof pAr
      checkTypeDestFunRange thy (TyApp n [a, b]) dom rng pD prf | True | Just ar | True =
        absurd prf
      checkTypeDestFunRange thy (TyApp n [a, b]) dom rng pD prf | True | Just ar | False
          with (checkType thy a) proof pA
        checkTypeDestFunRange thy (TyApp n [a, b]) dom rng pD prf | True | Just ar | False | Left e =
          absurd prf
        checkTypeDestFunRange thy (TyApp n [a, b]) dom rng pD prf | True | Just ar | False | Right ()
            with (checkType thy b) proof pB
          checkTypeDestFunRange thy (TyApp n [a, b]) dom rng pD prf | True | Just ar | False | Right () | Left e =
            absurd prf
          checkTypeDestFunRange thy (TyApp n [a, b]) dom rng pD prf | True | Just ar | False | Right () | Right () =
            rewrite sym (cong Builtin.snd (rightInjective pD)) in pB

-- A well-formed term's type is itself well-formed.  The environment never
-- enters: every case either reads a type annotation the check already
-- verified, or rebuilds one from sub-terms' types.
export
typeOfWellFormed : (thy : Theory) -> WellFormedTheory thy -> (t : Term) -> (env : List HType) ->
                    checkOpenTerm thy t env = Right () ->
                    (ty : HType) -> typeOf t = Right ty ->
                    checkType thy ty = Right ()
typeOfWellFormed thy wf (FVar n ty') env prf ty tyEq =
  rewrite sym (rightInjective tyEq) in prf
typeOfWellFormed thy wf (BVar i ty') env prf ty tyEq with (nthEnv i env) proof pN
  typeOfWellFormed thy wf (BVar i ty') env prf ty tyEq | Nothing = absurd prf
  typeOfWellFormed thy wf (BVar i ty') env prf ty tyEq | Just ety with (ety == ty') proof pEty
    typeOfWellFormed thy wf (BVar i ty') env prf ty tyEq | Just ety | False = absurd prf
    typeOfWellFormed thy wf (BVar i ty') env prf ty tyEq | Just ety | True =
      rewrite sym (rightInjective tyEq) in prf
typeOfWellFormed thy wf (Const n ty') env prf ty tyEq with (checkType thy ty') proof pCT
  typeOfWellFormed thy wf (Const n ty') env prf ty tyEq | Left e = absurd prf
  typeOfWellFormed thy wf (Const n ty') env prf ty tyEq | Right () =
    rewrite sym (rightInjective tyEq) in pCT
typeOfWellFormed thy wf (Abs aty b) env prf ty tyEq with (checkType thy aty) proof pCT
  typeOfWellFormed thy wf (Abs aty b) env prf ty tyEq | Left e = absurd prf
  typeOfWellFormed thy wf (Abs aty b) env prf ty tyEq | Right ()
      with (typeOf b) proof pB
    typeOfWellFormed thy wf (Abs aty b) env prf ty tyEq | Right () | Left e = absurd tyEq
    typeOfWellFormed thy wf (Abs aty b) env prf ty tyEq | Right () | Right bty =
      rewrite sym (rightInjective tyEq) in
      checkTypeFun thy wf aty bty pCT (typeOfWellFormed thy wf b (aty :: env) prf bty pB)
typeOfWellFormed thy wf (Comb f x) env prf ty tyEq
    with (checkOpenTerm thy f env) proof p1
  typeOfWellFormed thy wf (Comb f x) env prf ty tyEq | Left e = absurd prf
  typeOfWellFormed thy wf (Comb f x) env prf ty tyEq | Right ()
      with (typeOf f) proof pF
    typeOfWellFormed thy wf (Comb f x) env prf ty tyEq | Right () | Left e = absurd tyEq
    typeOfWellFormed thy wf (Comb f x) env prf ty tyEq | Right () | Right fty
        with (destFun fty) proof pD
      typeOfWellFormed thy wf (Comb f x) env prf ty tyEq | Right () | Right fty | Left e =
        absurd tyEq
      typeOfWellFormed thy wf (Comb f x) env prf ty tyEq | Right () | Right fty | Right (dom, rng) =
        -- `destFun` succeeding pins `fty` to `mkFun dom rng`, so the range
        -- `typeOf` returns is one of the arguments the function type's own
        -- check already walked.
        rewrite sym (rightInjective tyEq) in
        checkTypeDestFunRange thy fty dom rng pD
          (typeOfWellFormed thy wf f env p1 fty pF)

-- `eq` used at an instance of its generic type checks out, in any theory
-- that declares it the way `initialTheory` does.  This is where
-- `typeMatch` has to actually succeed, and so where `htypeEqRefl` earns
-- its keep: matching `'a -> 'a -> bool` against `ty -> ty -> bool` binds
-- `'a` to `ty` and then meets `'a` again, comparing `ty` with itself.
eqConstCheck : (thy : Theory) -> WellFormedTheory thy -> (ty : HType) ->
                checkType thy ty = Right () ->
                checkOpenTerm thy (Const NEq (mkFun ty (mkFun ty HType.boolTy))) [] = Right ()
eqConstCheck thy wf ty pTy =
  rewrite checkTypeFun thy wf ty (mkFun ty HType.boolTy) pTy
            (checkTypeFun thy wf ty HType.boolTy pTy (checkTypeBool thy wf)) in
  rewrite eqDeclared wf in
  rewrite htypeEqRefl ty in
  Refl

-- `eq` applied to its first operand: the half-built equation.
eqAppliedCheck : (thy : Theory) -> WellFormedTheory thy -> (l : Term) -> (ty : HType) ->
                  checkTerm thy l = Right () -> typeOf l = Right ty ->
                  checkOpenTerm thy
                    (Comb (Const NEq (mkFun ty (mkFun ty HType.boolTy))) l) [] = Right ()
eqAppliedCheck thy wf l ty cl tl =
  rewrite eqConstCheck thy wf ty (typeOfWellFormed thy wf l [] cl ty tl) in
  rewrite cl in
  rewrite tl in
  rewrite htypeEqRefl ty in
  Refl

-- The shared obligation behind every rule that concludes with an equation.
export
mkEqTermCheck : (thy : Theory) -> WellFormedTheory thy -> (l, r : Term) -> (ty : HType) ->
                 checkTerm thy l = Right () -> checkTerm thy r = Right () ->
                 typeOf l = Right ty -> typeOf r = Right ty ->
                 checkTerm thy
                   (Comb (Comb (Const NEq (mkFun ty (mkFun ty HType.boolTy))) l) r) = Right ()
mkEqTermCheck thy wf l r ty cl cr tl tr =
  rewrite eqAppliedCheck thy wf l ty cl tl in
  rewrite cr in
  rewrite tr in
  rewrite htypeEqRefl ty in
  Refl

-- ... and `mkEq` really does build that term.
export
mkEqShape : (l, r : Term) -> (ty : HType) ->
             typeOf l = Right ty -> typeOf r = Right ty ->
             mkEq l r = Right (Comb (Comb (Const NEq (mkFun ty (mkFun ty HType.boolTy))) l) r)
mkEqShape l r ty pl pr =
  rewrite pl in rewrite pr in rewrite htypeEqRefl ty in Refl

-- So: an equation built by `mkEq` from two checked terms of one type is a
-- checked term.  `REFL`'s conclusion is `mkEq t t`; `TRANS`, `MK_COMB`,
-- `EQ_MP` and `DEDUCT_ANTISYM_RULE` all conclude with an `mkEq` too.
export
mkEqCheckSound : (thy : Theory) -> WellFormedTheory thy -> (l, r : Term) -> (ty : HType) ->
                  checkTerm thy l = Right () -> checkTerm thy r = Right () ->
                  typeOf l = Right ty -> typeOf r = Right ty ->
                  (eq : Term) -> mkEq l r = Right eq ->
                  checkTerm thy eq = Right ()
mkEqCheckSound thy wf l r ty cl cr tl tr eq eqPrf =
  rewrite rightInjective (trans (sym eqPrf) (mkEqShape l r ty tl tr)) in
  mkEqTermCheck thy wf l r ty cl cr tl tr

-- `REFL`'s output is well-formed: its conclusion is `mkEq t t` for the `t`
-- it just checked.
export
reflConclSound : (thy : Theory) -> WellFormedTheory thy -> (t : Term) ->
                  checkTerm thy t = Right () ->
                  (eq : Term) -> mkEq t t = Right eq ->
                  checkTerm thy eq = Right ()
reflConclSound thy wf t ct eq eqPrf =
  let (ty ** tyPrf) = checkTermTypeOfSound thy t [] ct in
  mkEqCheckSound thy wf t t ty ct ct tyPrf tyPrf eq eqPrf

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
-- Top-level rather than a `where` inside `instR` so the proofs below can
-- reason about it; unchanged otherwise.
export
checkTheta : Theory -> List (Term, Term) -> Either String ()
checkTheta thy [] = Right ()
checkTheta thy ((rep, v) :: rest) = do
  case v of
    FVar _ _ => Right ()
    _        => Left "substitution target is not a free variable"
  checkTerm thy rep
  vty <- typeOf v
  rty <- typeOf rep
  if vty /= rty
    then Left "instantiation changes a variable's type"
    else checkTheta thy rest

export
instR : Theory -> List (Term, Term) -> Thm -> Either String Thm
instR thy theta th = do
  inTheory thy th
  checkTheta thy theta
  let hyps2 = rehashHyps (map (instFvar theta) (thmHyps th))
  Right (MkThm hyps2 (instFvar theta (thmConcl th)) (thyStamp thy))

-- Instantiate type variables.  `tyin` is a plain association list (see the
-- comment on `Theory` above for why).
export
instTypeR : Theory -> List (Name, HType) -> Thm -> Either String Thm
instTypeR thy tyin th = do
  inTheory thy th
  checkTypeList thy (map snd tyin)
  let hyps2 = rehashHyps (map (instType tyin) (thmHyps th))
  Right (MkThm hyps2 (instType tyin (thmConcl th)) (thyStamp thy))

-- -- soundness proofs: the rules produce well-formed theorems -------------
--
-- The payoff.  A `Thm` is well-formed when every hypothesis and its
-- conclusion are terms the theory accepts.  Nothing in the kernel ever
-- re-checks a theorem it built, so each rule owes exactly this, and these
-- theorems collect the debt for `REFL`, `ASSUME` and `BETA` -- the three
-- rules that build a conclusion out of a term they were handed rather than
-- out of an existing theorem's parts.

public export
data AllChecked : Theory -> List Term -> Type where
  AllCheckedNil  : AllChecked thy []
  AllCheckedCons : checkTerm thy t = Right () -> AllChecked thy ts ->
                   AllChecked thy (t :: ts)

public export
record WellFormedThm (thy : Theory) (th : Thm) where
  constructor MkWellFormedThm
  hypsChecked  : AllChecked thy (thmHyps th)
  conclChecked : checkTerm thy (thmConcl th) = Right ()

export
reflWellFormed : (thy : Theory) -> WellFormedTheory thy -> (t : Term) -> (th : Thm) ->
                  reflR thy t = Right th -> WellFormedThm thy th
reflWellFormed thy wf t th prf with (checkTerm thy t) proof ct
  reflWellFormed thy wf t th prf | Left e = absurd prf
  reflWellFormed thy wf t th prf | Right () with (mkEq t t) proof eqPrf
    reflWellFormed thy wf t th prf | Right () | Left e = absurd prf
    reflWellFormed thy wf t th prf | Right () | Right eq =
      rewrite sym (rightInjective prf) in
      MkWellFormedThm AllCheckedNil (reflConclSound thy wf t ct eq eqPrf)

export
assumeWellFormed : (thy : Theory) -> (p : Term) -> (th : Thm) ->
                    assumeR thy p = Right th -> WellFormedThm thy th
assumeWellFormed thy p th prf with (checkTerm thy p) proof cp
  assumeWellFormed thy p th prf | Left e = absurd prf
  assumeWellFormed thy p th prf | Right () with (isBool p) proof pB
    assumeWellFormed thy p th prf | Right () | Left e = absurd prf
    assumeWellFormed thy p th prf | Right () | Right ok with (ok)
      assumeWellFormed thy p th prf | Right () | Right ok | False = absurd prf
      assumeWellFormed thy p th prf | Right () | Right ok | True =
        rewrite sym (rightInjective prf) in
        MkWellFormedThm (AllCheckedCons cp AllCheckedNil) cp

-- `BETA` is where all of it comes together: its conclusion equates the
-- redex with the reduct, so it needs the reduct to be well-formed
-- (`betaCheckSound`) *and* to have the redex's type (`betaTypeSound`)
-- before `mkEqCheckSound` will build the equation.
export
betaWellFormed : (thy : Theory) -> WellFormedTheory thy ->
                  (aty : HType) -> (body, arg : Term) -> (th : Thm) ->
                  betaR thy (Comb (Abs aty body) arg) = Right th ->
                  WellFormedThm thy th
betaWellFormed thy wf aty body arg th prf
    with (checkTerm thy (Comb (Abs aty body) arg)) proof ct
  betaWellFormed thy wf aty body arg th prf | Left e = absurd prf
  betaWellFormed thy wf aty body arg th prf | Right ()
      with (mkEq (Comb (Abs aty body) arg) (substBvar arg body)) proof eqPrf
    betaWellFormed thy wf aty body arg th prf | Right () | Left e = absurd prf
    betaWellFormed thy wf aty body arg th prf | Right () | Right eq =
      let (ty ** tl) = checkTermTypeOfSound thy (Comb (Abs aty body) arg) [] ct in
      rewrite sym (rightInjective prf) in
      MkWellFormedThm AllCheckedNil
        (mkEqCheckSound thy wf (Comb (Abs aty body) arg) (substBvar arg body) ty
                        ct (betaCheckSound thy aty body arg ct)
                        tl (trans (betaTypeSound thy aty body arg ct) tl)
                        eq eqPrf)

-- -- soundness proofs: the equation-concluding rules -----------------------
--
-- `TRANS`, `MK_COMB`, `EQ_MP` and `DEDUCT_ANTISYM_RULE` all build their
-- conclusion out of parts of the theorems they were given, so their
-- obligation splits in two: the parts they pull out are still well-formed
-- (they come from a well-formed equation), and the hypothesis list they
-- assemble is still well-formed (`hypUnion`/`hypRemove` only ever move
-- existing hypotheses around).
--
-- The operand *types* come for free from `mkEq` itself: it refuses to
-- build an equation whose sides disagree, so a successful `mkEq` is
-- already a proof that they agree.  That is why no inversion of
-- `typeMatch` is needed here.

notFalseTrue : (b : Bool) -> not b = False -> b = True
notFalseTrue True  prf = Refl
notFalseTrue False prf = absurd prf

-- Inverting `typeMatch`: if `eq`'s generic type matched a concrete one at
-- all, that concrete one has to be `ty -> ty -> bool` for some `ty` -- the
-- pattern meets `'a` twice, so both sides of the equation are pinned to
-- the same type.  This is what recovers "an equation's two operands have
-- the same type" from nothing but the fact that the term type-checked.
typeMatchEqInv : (ety : HType) -> (m : List (Name, HType)) ->
                  typeMatch Kernel.eqGenericType ety [] = Just m ->
                  (ty : HType ** ety = mkFun ty (mkFun ty HType.boolTy))
typeMatchEqInv (TyVar _) m prf = absurd prf
typeMatchEqInv (TyApp n2 targs) m prf with (NFun == n2) proof pN2
  typeMatchEqInv (TyApp n2 targs) m prf | False = absurd prf
  typeMatchEqInv (TyApp n2 targs) m prf | True with (targs)
    typeMatchEqInv (TyApp n2 targs) m prf | True | [] = absurd prf
    typeMatchEqInv (TyApp n2 targs) m prf | True | [t1] = absurd prf
    typeMatchEqInv (TyApp n2 targs) m prf | True | (t1 :: t2 :: t3 :: rest)
        with (typeMatch (mkFun (TyVar NAlpha) HType.boolTy) t2 [(NAlpha, t1)])
      typeMatchEqInv (TyApp n2 targs) m prf | True | (t1 :: t2 :: t3 :: rest) | Nothing =
        absurd prf
      typeMatchEqInv (TyApp n2 targs) m prf | True | (t1 :: t2 :: t3 :: rest) | Just _ =
        absurd prf
    typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyVar _] = absurd prf
    typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3]
        with (NFun == n3) proof pN3
      typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | False = absurd prf
      typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True
          with (targs3)
        typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | [] =
          absurd prf
        typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | [t3]
            with (t1 == t3)
          typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | [t3] | False =
            absurd prf
          typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | [t3] | True =
            absurd prf
        typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | (t3 :: t4 :: t5 :: rest)
            with (t1 == t3)
          typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | (t3 :: t4 :: t5 :: rest) | False =
            absurd prf
          typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | (t3 :: t4 :: t5 :: rest) | True
              with (typeMatch HType.boolTy t4 [(NAlpha, t1)])
            typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | (t3 :: t4 :: t5 :: rest) | True | Nothing =
              absurd prf
            typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | (t3 :: t4 :: t5 :: rest) | True | Just _ =
              absurd prf
        typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | [t3, TyVar _]
            with (t1 == t3)
          typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | [t3, TyVar _] | False =
            absurd prf
          typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | [t3, TyVar _] | True =
            absurd prf
        typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | [t3, TyApp n4 targs4]
            with (t1 == t3) proof pT13
          typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | [t3, TyApp n4 targs4] | False =
            absurd prf
          typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | [t3, TyApp n4 targs4] | True
              with (NBool == n4) proof pN4
            typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | [t3, TyApp n4 targs4] | True | False =
              absurd prf
            typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | [t3, TyApp n4 targs4] | True | True
                with (targs4)
              typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | [t3, TyApp n4 targs4] | True | True | (_ :: _) =
                absurd prf
              typeMatchEqInv (TyApp n2 targs) m prf | True | [t1, TyApp n3 targs3] | True | [t3, TyApp n4 targs4] | True | True | [] =
                (t1 ** rewrite sym (nameEqSound NFun n2 pN2) in
                       rewrite sym (nameEqSound NFun n3 pN3) in
                       rewrite sym (nameEqSound NBool n4 pN4) in
                       rewrite sym (htypeEqSound t1 t3 pT13) in Refl)

export
mkEqTypes : (l, r : Term) -> (eq : Term) -> mkEq l r = Right eq ->
             (ty : HType ** (typeOf l = Right ty, typeOf r = Right ty))
mkEqTypes l r eq prf with (typeOf l) proof pl
  mkEqTypes l r eq prf | Left e = absurd prf
  mkEqTypes l r eq prf | Right lty with (typeOf r) proof pr
    mkEqTypes l r eq prf | Right lty | Left e = absurd prf
    mkEqTypes l r eq prf | Right lty | Right rty with (lty /= rty) proof pne
      mkEqTypes l r eq prf | Right lty | Right rty | True = absurd prf
      mkEqTypes l r eq prf | Right lty | Right rty | False =
        -- The `with` abstraction has already replaced `typeOf l`/`typeOf r`
        -- in the goal, so what is left is `Right lty = Right ty` and
        -- `Right rty = Right ty`; `mkEq`'s own check is what makes the two
        -- types the same.
        (lty ** (Refl,
                 cong Right (sym (htypeEqSound lty rty (notFalseTrue (lty == rty) pne)))))

-- Everything an application's check establishes, in one package: both
-- operand types, the operator's function type, and the fact that its
-- domain is the argument's type.  Written once and used at both levels of
-- an equation `Comb (Comb (Const NEq ety) l) r`.
export
combCheckTypes : (thy : Theory) -> (f, x : Term) -> (env : List HType) ->
                  checkOpenTerm thy (Comb f x) env = Right () ->
                  (fty : HType ** dom : HType ** rng : HType ** xty : HType **
                    (typeOf f = Right fty, destFun fty = Right (dom, rng),
                     typeOf x = Right xty, dom = xty))
combCheckTypes thy f x env prf with (checkOpenTerm thy f env) proof p1
  combCheckTypes thy f x env prf | Left e = absurd prf
  combCheckTypes thy f x env prf | Right () with (checkOpenTerm thy x env) proof p2
    combCheckTypes thy f x env prf | Right () | Left e = absurd prf
    combCheckTypes thy f x env prf | Right () | Right () with (typeOf f) proof pF
      combCheckTypes thy f x env prf | Right () | Right () | Left e = absurd prf
      combCheckTypes thy f x env prf | Right () | Right () | Right fty
          with (isFun fty) proof pIF
        combCheckTypes thy f x env prf | Right () | Right () | Right fty | False = absurd prf
        combCheckTypes thy f x env prf | Right () | Right () | Right fty | True
            with (destFun fty) proof pD
          combCheckTypes thy f x env prf | Right () | Right () | Right fty | True | Left e =
            absurd prf
          combCheckTypes thy f x env prf | Right () | Right () | Right fty | True | Right (dom, rng)
              with (typeOf x) proof pX
            combCheckTypes thy f x env prf | Right () | Right () | Right fty | True | Right (dom, rng) | Left e =
              absurd prf
            combCheckTypes thy f x env prf | Right () | Right () | Right fty | True | Right (dom, rng) | Right xty
                with (dom == xty) proof pDX
              combCheckTypes thy f x env prf | Right () | Right () | Right fty | True | Right (dom, rng) | Right xty | False =
                absurd prf
              combCheckTypes thy f x env prf | Right () | Right () | Right fty | True | Right (dom, rng) | Right xty | True =
                (fty ** dom ** rng ** xty ** (Refl, pD, Refl, htypeEqSound dom xty pDX))

-- Likewise for a constant: its use type matched the declared generic type.
export
constCheckMatch : (thy : Theory) -> (n : Name) -> (ty : HType) -> (env : List HType) ->
                   checkOpenTerm thy (Const n ty) env = Right () ->
                   (gty : HType ** m : List (Name, HType) **
                     (constType thy n = Just gty, typeMatch gty ty [] = Just m))
constCheckMatch thy n ty env prf with (checkType thy ty) proof pCT
  constCheckMatch thy n ty env prf | Left e = absurd prf
  constCheckMatch thy n ty env prf | Right () with (constType thy n) proof pC
    constCheckMatch thy n ty env prf | Right () | Nothing = absurd prf
    constCheckMatch thy n ty env prf | Right () | Just gty
        with (typeMatch gty ty []) proof pM
      constCheckMatch thy n ty env prf | Right () | Just gty | Nothing = absurd prf
      constCheckMatch thy n ty env prf | Right () | Just gty | Just m =
        (gty ** m ** (Refl, pM))

-- `destEq` succeeding pins the term's shape, so the two operands are the
-- function and argument of nested applications the check already walked.
destEqShape : (c : Term) -> (l, r : Term) -> destEq c = Just (l, r) ->
               (ety : HType ** c = Comb (Comb (Const NEq ety) l) r)
destEqShape (FVar _ _) l r prf = absurd prf
destEqShape (BVar _ _) l r prf = absurd prf
destEqShape (Const _ _) l r prf = absurd prf
destEqShape (Abs _ _) l r prf = absurd prf
destEqShape (Comb (FVar _ _) _) l r prf = absurd prf
destEqShape (Comb (BVar _ _) _) l r prf = absurd prf
destEqShape (Comb (Const _ _) _) l r prf = absurd prf
destEqShape (Comb (Abs _ _) _) l r prf = absurd prf
destEqShape (Comb (Comb (FVar _ _) _) _) l r prf = absurd prf
destEqShape (Comb (Comb (BVar _ _) _) _) l r prf = absurd prf
destEqShape (Comb (Comb (Comb _ _) _) _) l r prf = absurd prf
destEqShape (Comb (Comb (Abs _ _) _) _) l r prf = absurd prf
destEqShape (Comb (Comb (Const n ety) l') r') l r prf with (n == NEq) proof pN
  destEqShape (Comb (Comb (Const n ety) l') r') l r prf | False = absurd prf
  destEqShape (Comb (Comb (Const n ety) l') r') l r prf | True =
    (ety ** rewrite nameEqSound n NEq pN in
            rewrite fst (pairInjective (justInjective prf)) in
            rewrite snd (pairInjective (justInjective prf)) in Refl)
  where
    pairInjective : (x, y) = (u, v) -> (x = u, y = v)
    pairInjective Refl = (Refl, Refl)

-- Both operands of a well-formed equation are themselves well-formed.
export
eqOperandsChecked : (thy : Theory) -> (c, l, r : Term) ->
                     checkTerm thy c = Right () -> destEq c = Just (l, r) ->
                     (checkTerm thy l = Right (), checkTerm thy r = Right ())
eqOperandsChecked thy c l r cc dEq with (destEqShape c l r dEq)
  eqOperandsChecked thy c l r cc dEq | (ety ** shape) =
    let cc' = replace {p = \x => checkTerm thy x = Right ()} shape cc in
    (combCheckArg thy (Const NEq ety) l []
       (combCheckFun thy (Comb (Const NEq ety) l) r [] cc'),
     combCheckArg thy (Comb (Const NEq ety) l) r [] cc')

-- With `eq`'s use type known concretely, `destFun` reduces and both
-- operand types fall out of the two application checks.
eqTermTypesShaped : (thy : Theory) -> (ty : HType) -> (l, r : Term) ->
                     checkTerm thy
                       (Comb (Comb (Const NEq (mkFun ty (mkFun ty HType.boolTy))) l) r)
                         = Right () ->
                     (typeOf l = Right ty, typeOf r = Right ty)
eqTermTypesShaped thy ty l r cc =
  let innerChk = combCheckFun thy (Comb (Const NEq (mkFun ty (mkFun ty HType.boolTy))) l) r [] cc
      (fty2 ** dom2 ** rng2 ** lty ** (tC, dC, tL, domEqL)) =
        combCheckTypes thy (Const NEq (mkFun ty (mkFun ty HType.boolTy))) l [] innerChk
      domTy = fst (pairInj (rightInjective
                     (replace {p = \z => destFun z = Right (dom2, rng2)}
                              (sym (rightInjective tC)) dC)))
      (ity ** dom ** rng ** rty ** (tI, dI, tR, domEqR)) =
        combCheckTypes thy (Comb (Const NEq (mkFun ty (mkFun ty HType.boolTy))) l) r [] cc
      domTy2 = fst (pairInj (rightInjective
                      (replace {p = \z => destFun z = Right (dom, rng)}
                               (sym (rightInjective tI)) dI)))
   in (replace {p = \z => typeOf l = Right z} (trans (sym domEqL) (sym domTy)) tL,
       replace {p = \z => typeOf r = Right z} (trans (sym domEqR) (sym domTy2)) tR)
  where
    pairInj : the (a, b) x = the (a, b) y -> (fst x = fst y, snd x = snd y)
    pairInj Refl = (Refl, Refl)

-- Recovering "an equation's two operands have the same type" from nothing
-- but the fact that the equation type-checked.  This is the piece
-- `MK_COMB` needs and the other equation rules do not: it concludes with
-- an equation between *applications it builds*, so it has to know the two
-- theorems it was given really do equate same-typed terms.
export
eqOperandTypes : (thy : Theory) -> WellFormedTheory thy -> (c, l, r : Term) ->
                  checkTerm thy c = Right () -> destEq c = Just (l, r) ->
                  (ty : HType ** (typeOf l = Right ty, typeOf r = Right ty))
eqOperandTypes thy wf c l r cc dEq with (destEqShape c l r dEq)
  eqOperandTypes thy wf c l r cc dEq | (ety ** shape) =
    let cc' = replace {p = \x => checkTerm thy x = Right ()} shape cc
        constChk = combCheckFun thy (Const NEq ety) l []
                     (combCheckFun thy (Comb (Const NEq ety) l) r [] cc')
        (gty ** m ** (cT, mT)) = constCheckMatch thy NEq ety [] constChk
        mT2 = replace {p = \g => typeMatch g ety [] = Just m}
                      (justInjective (trans (sym cT) (eqDeclared wf))) mT
        (ty ** etyShape) = typeMatchEqInv ety m mT2
        cc2 = replace {p = \e => checkTerm thy (Comb (Comb (Const NEq e) l) r) = Right ()}
                      etyShape cc'
    in (ty ** eqTermTypesShaped thy ty l r cc2)

-- Hypothesis-list bookkeeping preserves well-formedness: every rule that
-- merges or drops hypotheses only ever moves existing ones around.
export
hypInsertChecked : (thy : Theory) -> (t : Term) -> (hs : List Term) ->
                    checkTerm thy t = Right () -> AllChecked thy hs ->
                    AllChecked thy (hypInsert t hs)
hypInsertChecked thy t [] ct acc = AllCheckedCons ct AllCheckedNil
hypInsertChecked thy t (h :: hs) ct (AllCheckedCons ch cs) with (termOrd t h)
  hypInsertChecked thy t (h :: hs) ct (AllCheckedCons ch cs) | EQ = AllCheckedCons ch cs
  hypInsertChecked thy t (h :: hs) ct (AllCheckedCons ch cs) | LT =
    AllCheckedCons ct (AllCheckedCons ch cs)
  hypInsertChecked thy t (h :: hs) ct (AllCheckedCons ch cs) | GT =
    AllCheckedCons ch (hypInsertChecked thy t hs ct cs)

foldlHypInsertChecked : (thy : Theory) -> (as, acc : List Term) ->
                         AllChecked thy as -> AllChecked thy acc ->
                         AllChecked thy (foldl (flip Kernel.hypInsert) acc as)
foldlHypInsertChecked thy [] acc _ pacc = pacc
foldlHypInsertChecked thy (a :: as) acc (AllCheckedCons ca cas) pacc =
  foldlHypInsertChecked thy as (hypInsert a acc) cas (hypInsertChecked thy a acc ca pacc)

export
hypUnionChecked : (thy : Theory) -> (as, bs : List Term) ->
                   AllChecked thy as -> AllChecked thy bs ->
                   AllChecked thy (hypUnion as bs)
hypUnionChecked thy [] bs pas pbs = pbs
hypUnionChecked thy (a :: as) [] pas pbs = pas
hypUnionChecked thy (a :: as) (b :: bs) pas pbs =
  foldlHypInsertChecked thy (a :: as) (b :: bs) pas pbs

export
hypRemoveChecked : (thy : Theory) -> (t : Term) -> (hs : List Term) ->
                    AllChecked thy hs -> AllChecked thy (hypRemove t hs)
hypRemoveChecked thy t [] pas = AllCheckedNil
hypRemoveChecked thy t (h :: hs) (AllCheckedCons ch cs) with (h /= t)
  hypRemoveChecked thy t (h :: hs) (AllCheckedCons ch cs) | True =
    AllCheckedCons ch (hypRemoveChecked thy t hs cs)
  hypRemoveChecked thy t (h :: hs) (AllCheckedCons ch cs) | False =
    hypRemoveChecked thy t hs cs

-- `MK_COMB` is the one of the four whose conclusion equates *applications*
-- it builds rather than terms it was handed, so it needs the application
-- to be assembled from the checks the rule itself performs.
combCheckBuild : (thy : Theory) -> (f, x : Term) -> (fty, dom, rng, xty : HType) ->
                  checkTerm thy f = Right () -> checkTerm thy x = Right () ->
                  typeOf f = Right fty -> typeOf x = Right xty ->
                  isFun fty = True -> destFun fty = Right (dom, rng) -> dom = xty ->
                  checkTerm thy (Comb f x) = Right ()
combCheckBuild thy f x fty dom rng xty cf cx tf tx pIsFun pD pDom =
  rewrite cf in rewrite cx in rewrite tf in rewrite pIsFun in
  rewrite pD in rewrite tx in rewrite pDom in
  rewrite htypeEqRefl xty in Refl

export
transWellFormed : (thy : Theory) -> WellFormedTheory thy -> (a, b : Thm) ->
                   WellFormedThm thy a -> WellFormedThm thy b ->
                   (th : Thm) -> transR a b = Right th -> WellFormedThm thy th
transWellFormed thy wf a b wa wb th prf
    with (combineStamps (thmStamp a) (thmStamp b)) proof pSt
  transWellFormed thy wf a b wa wb th prf | Left e = absurd prf
  transWellFormed thy wf a b wa wb th prf | Right st
      with (destEq (thmConcl a)) proof pA
    transWellFormed thy wf a b wa wb th prf | Right st | Nothing = absurd prf
    transWellFormed thy wf a b wa wb th prf | Right st | Just (l, m1)
        with (destEq (thmConcl b)) proof pB
      transWellFormed thy wf a b wa wb th prf | Right st | Just (l, m1) | Nothing = absurd prf
      transWellFormed thy wf a b wa wb th prf | Right st | Just (l, m1) | Just (m2, r)
          with (m1 /= m2) proof pM
        transWellFormed thy wf a b wa wb th prf | Right st | Just (l, m1) | Just (m2, r) | True =
          absurd prf
        transWellFormed thy wf a b wa wb th prf | Right st | Just (l, m1) | Just (m2, r) | False
            with (mkEq l r) proof pEq
          transWellFormed thy wf a b wa wb th prf | Right st | Just (l, m1) | Just (m2, r) | False | Left e =
            absurd prf
          transWellFormed thy wf a b wa wb th prf | Right st | Just (l, m1) | Just (m2, r) | False | Right eq =
            let (ty ** (tl, tr)) = mkEqTypes l r eq pEq
                (cl, _) = eqOperandsChecked thy (thmConcl a) l m1 (conclChecked wa) pA
                (_, cr) = eqOperandsChecked thy (thmConcl b) m2 r (conclChecked wb) pB in
            rewrite sym (rightInjective prf) in
            MkWellFormedThm
              (hypUnionChecked thy (thmHyps a) (thmHyps b) (hypsChecked wa) (hypsChecked wb))
              (mkEqCheckSound thy wf l r ty cl cr tl tr eq pEq)

export
eqMpWellFormed : (thy : Theory) -> (eqth, th' : Thm) ->
                  WellFormedThm thy eqth -> WellFormedThm thy th' ->
                  (th : Thm) -> eqMpR eqth th' = Right th -> WellFormedThm thy th
eqMpWellFormed thy eqth th' we wt th prf
    with (combineStamps (thmStamp eqth) (thmStamp th')) proof pSt
  eqMpWellFormed thy eqth th' we wt th prf | Left e = absurd prf
  eqMpWellFormed thy eqth th' we wt th prf | Right st
      with (destEq (thmConcl eqth)) proof pE
    eqMpWellFormed thy eqth th' we wt th prf | Right st | Nothing = absurd prf
    eqMpWellFormed thy eqth th' we wt th prf | Right st | Just (p, q)
        with (p /= thmConcl th') proof pM
      eqMpWellFormed thy eqth th' we wt th prf | Right st | Just (p, q) | True = absurd prf
      eqMpWellFormed thy eqth th' we wt th prf | Right st | Just (p, q) | False =
        -- The conclusion is the equation's right-hand side, which the
        -- equation's own well-formedness already covers.
        rewrite sym (rightInjective prf) in
        MkWellFormedThm
          (hypUnionChecked thy (thmHyps eqth) (thmHyps th') (hypsChecked we) (hypsChecked wt))
          (snd (eqOperandsChecked thy (thmConcl eqth) p q (conclChecked we) pE))

export
deductAntisymWellFormed : (thy : Theory) -> WellFormedTheory thy -> (a, b : Thm) ->
                           WellFormedThm thy a -> WellFormedThm thy b ->
                           (th : Thm) -> deductAntisymRule a b = Right th ->
                           WellFormedThm thy th
deductAntisymWellFormed thy wf a b wa wb th prf
    with (combineStamps (thmStamp a) (thmStamp b)) proof pSt
  deductAntisymWellFormed thy wf a b wa wb th prf | Left e = absurd prf
  deductAntisymWellFormed thy wf a b wa wb th prf | Right st
      with (mkEq (thmConcl a) (thmConcl b)) proof pEq
    deductAntisymWellFormed thy wf a b wa wb th prf | Right st | Left e = absurd prf
    deductAntisymWellFormed thy wf a b wa wb th prf | Right st | Right eq =
      -- Both operands are the inputs' own conclusions, so their
      -- well-formedness is the hypothesis; only the hypothesis lists move.
      let (ty ** (tl, tr)) = mkEqTypes (thmConcl a) (thmConcl b) eq pEq in
      rewrite sym (rightInjective prf) in
      MkWellFormedThm
        (hypUnionChecked thy (hypRemove (thmConcl b) (thmHyps a))
                             (hypRemove (thmConcl a) (thmHyps b))
                             (hypRemoveChecked thy (thmConcl b) (thmHyps a) (hypsChecked wa))
                             (hypRemoveChecked thy (thmConcl a) (thmHyps b) (hypsChecked wb)))
        (mkEqCheckSound thy wf (thmConcl a) (thmConcl b) ty
                        (conclChecked wa) (conclChecked wb) tl tr eq pEq)

export
mkCombWellFormed : (thy : Theory) -> WellFormedTheory thy -> (fth, xth : Thm) ->
                    WellFormedThm thy fth -> WellFormedThm thy xth ->
                    (th : Thm) -> mkCombR fth xth = Right th -> WellFormedThm thy th
mkCombWellFormed thy wf fth xth wff wx th prf
    with (combineStamps (thmStamp fth) (thmStamp xth)) proof pSt
  mkCombWellFormed thy wf fth xth wff wx th prf | Left e = absurd prf
  mkCombWellFormed thy wf fth xth wff wx th prf | Right st
      with (destEq (thmConcl fth)) proof pF
    mkCombWellFormed thy wf fth xth wff wx th prf | Right st | Nothing = absurd prf
    mkCombWellFormed thy wf fth xth wff wx th prf | Right st | Just (f, g)
        with (destEq (thmConcl xth)) proof pX
      mkCombWellFormed thy wf fth xth wff wx th prf | Right st | Just (f, g) | Nothing =
        absurd prf
      mkCombWellFormed thy wf fth xth wff wx th prf | Right st | Just (f, g) | Just (x, y)
          with (typeOf f) proof pTF
        mkCombWellFormed thy wf fth xth wff wx th prf | Right st | Just (f, g) | Just (x, y) | Left e =
          absurd prf
        mkCombWellFormed thy wf fth xth wff wx th prf | Right st | Just (f, g) | Just (x, y) | Right fty
            with (isFun fty) proof pIF
          mkCombWellFormed thy wf fth xth wff wx th prf | Right st | Just (f, g) | Just (x, y) | Right fty | False =
            absurd prf
          mkCombWellFormed thy wf fth xth wff wx th prf | Right st | Just (f, g) | Just (x, y) | Right fty | True
              with (destFun fty) proof pD
            mkCombWellFormed thy wf fth xth wff wx th prf | Right st | Just (f, g) | Just (x, y) | Right fty | True | Left e =
              absurd prf
            mkCombWellFormed thy wf fth xth wff wx th prf | Right st | Just (f, g) | Just (x, y) | Right fty | True | Right (dom, rng)
                with (typeOf x) proof pTX
              mkCombWellFormed thy wf fth xth wff wx th prf | Right st | Just (f, g) | Just (x, y) | Right fty | True | Right (dom, rng) | Left e =
                absurd prf
              mkCombWellFormed thy wf fth xth wff wx th prf | Right st | Just (f, g) | Just (x, y) | Right fty | True | Right (dom, rng) | Right xty
                  with (dom /= xty) proof pDX
                mkCombWellFormed thy wf fth xth wff wx th prf | Right st | Just (f, g) | Just (x, y) | Right fty | True | Right (dom, rng) | Right xty | True =
                  absurd prf
                mkCombWellFormed thy wf fth xth wff wx th prf | Right st | Just (f, g) | Just (x, y) | Right fty | True | Right (dom, rng) | Right xty | False
                    with (mkEq (Comb f x) (Comb g y)) proof pEq
                  mkCombWellFormed thy wf fth xth wff wx th prf | Right st | Just (f, g) | Just (x, y) | Right fty | True | Right (dom, rng) | Right xty | False | Left e =
                    absurd prf
                  mkCombWellFormed thy wf fth xth wff wx th prf | Right st | Just (f, g) | Just (x, y) | Right fty | True | Right (dom, rng) | Right xty | False | Right eq =
                    let (ty ** (tl, tr)) = mkEqTypes (Comb f x) (Comb g y) eq pEq
                        (cf, cg) = eqOperandsChecked thy (thmConcl fth) f g (conclChecked wff) pF
                        (cx, cy) = eqOperandsChecked thy (thmConcl xth) x y (conclChecked wx) pX
                        -- the two sides of each input equation share a type,
                        -- so `g`/`y` fit together exactly as `f`/`x` do
                        (tf ** (tF, tG)) =
                          eqOperandTypes thy wf (thmConcl fth) f g (conclChecked wff) pF
                        (tx ** (tX, tY)) =
                          eqOperandTypes thy wf (thmConcl xth) x y (conclChecked wx) pX
                        ftyEq = rightInjective (trans (sym tF) pTF)
                        xtyEq = rightInjective (trans (sym tX) pTX)
                        domEq = htypeEqSound dom xty (notFalseTrue (dom == xty) pDX)
                        cfx = combCheckBuild thy f x fty dom rng xty cf cx pTF pTX pIF pD domEq
                        cgy = combCheckBuild thy g y fty dom rng xty cg cy
                                (replace {p = \z => typeOf g = Right z} ftyEq tG)
                                (replace {p = \z => typeOf y = Right z} xtyEq tY)
                                pIF pD domEq in
                    rewrite sym (rightInjective prf) in
                    MkWellFormedThm
                      (hypUnionChecked thy (thmHyps fth) (thmHyps xth)
                                       (hypsChecked wff) (hypsChecked wx))
                      (mkEqCheckSound thy wf (Comb f x) (Comb g y) ty cfx cgy tl tr eq pEq)

-- -- soundness proofs: ABS -------------------------------------------------
--
-- `ABS` closes a free variable, which is substitution run backwards:
-- instead of replacing a `BVar` by a term, it replaces an `FVar` by a
-- `BVar` and pushes the variable's type onto the environment.  The lemma
-- has the same shape as `substAtCheckSound`, with the binder appended to
-- the environment rather than consumed from it.

fvarTypeInj : FVar a b = FVar c d -> b = d
fvarTypeInj Refl = Refl

export
abstractAtCheck : (thy : Theory) -> (n : Name) -> (vty : HType) ->
                   (t : Term) -> (env : List HType) ->
                   checkOpenTerm thy t env = Right () ->
                   checkType thy vty = Right () ->
                   checkOpenTerm thy (abstractAt (length env) (FVar n vty) t) (env ++ [vty])
                     = Right ()
abstractAtCheck thy n vty (FVar n' ty') env prf cvty with (FVar n' ty' == FVar n vty) proof pEq
  abstractAtCheck thy n vty (FVar n' ty') env prf cvty | False = prf
  abstractAtCheck thy n vty (FVar n' ty') env prf cvty | True =
    -- it *is* the variable being abstracted, so it becomes the new binder's
    -- index, and its type is the binder's type
    let tyEq = fvarTypeInj (termEqSound (FVar n' ty') (FVar n vty) pEq) in
    rewrite nthEnvAtEnd env vty in
    rewrite tyEq in
    rewrite htypeEqRefl vty in
    cvty
abstractAtCheck thy n vty (Const n' ty') env prf cvty = prf
abstractAtCheck thy n vty (BVar i ty') env prf cvty with (nthEnv i env) proof pN
  abstractAtCheck thy n vty (BVar i ty') env prf cvty | Nothing = absurd prf
  abstractAtCheck thy n vty (BVar i ty') env prf cvty | Just ety =
    rewrite nthEnvAppend i env [vty] ety pN in prf
abstractAtCheck thy n vty (Comb f x) env prf cvty
    with (checkOpenTerm thy f env) proof p1
  abstractAtCheck thy n vty (Comb f x) env prf cvty | Left e = absurd prf
  abstractAtCheck thy n vty (Comb f x) env prf cvty | Right ()
      with (checkOpenTerm thy x env) proof p2
    abstractAtCheck thy n vty (Comb f x) env prf cvty | Right () | Left e = absurd prf
    abstractAtCheck thy n vty (Comb f x) env prf cvty | Right () | Right () =
      rewrite abstractAtCheck thy n vty f env p1 cvty in
      rewrite abstractAtCheck thy n vty x env p2 cvty in
      rewrite abstractPreservesType (length env) (FVar n vty) f in
      rewrite abstractPreservesType (length env) (FVar n vty) x in
      prf
abstractAtCheck thy n vty (Abs aty b) env prf cvty with (checkType thy aty) proof pCT
  abstractAtCheck thy n vty (Abs aty b) env prf cvty | Left e = absurd prf
  abstractAtCheck thy n vty (Abs aty b) env prf cvty | Right () =
    abstractAtCheck thy n vty b (aty :: env) prf cvty

export
absWellFormed : (thy : Theory) -> WellFormedTheory thy -> (n : Name) -> (vty : HType) ->
                 (th' : Thm) -> WellFormedThm thy th' -> (th : Thm) ->
                 absR thy (FVar n vty) th' = Right th -> WellFormedThm thy th
absWellFormed thy wf n vty th' wt th prf with (inTheory thy th') proof pIn
  absWellFormed thy wf n vty th' wt th prf | Left e = absurd prf
  absWellFormed thy wf n vty th' wt th prf | Right () with (checkType thy vty) proof pCV
    absWellFormed thy wf n vty th' wt th prf | Right () | Left e = absurd prf
    absWellFormed thy wf n vty th' wt th prf | Right () | Right ()
        with (any (vfreeIn (FVar n vty)) (thmHyps th')) proof pFree
      absWellFormed thy wf n vty th' wt th prf | Right () | Right () | True = absurd prf
      absWellFormed thy wf n vty th' wt th prf | Right () | Right () | False
          with (destEq (thmConcl th')) proof pE
        absWellFormed thy wf n vty th' wt th prf | Right () | Right () | False | Nothing =
          absurd prf
        absWellFormed thy wf n vty th' wt th prf | Right () | Right () | False | Just (l, r)
            with (mkEq (Abs vty (abstractFvar (FVar n vty) l))
                       (Abs vty (abstractFvar (FVar n vty) r))) proof pEq
          absWellFormed thy wf n vty th' wt th prf | Right () | Right () | False | Just (l, r) | Left e =
            absurd prf
          absWellFormed thy wf n vty th' wt th prf | Right () | Right () | False | Just (l, r) | Right eq =
            let (cl, cr) = eqOperandsChecked thy (thmConcl th') l r (conclChecked wt) pE
                (ty ** (tl, tr)) =
                  mkEqTypes (Abs vty (abstractFvar (FVar n vty) l))
                            (Abs vty (abstractFvar (FVar n vty) r)) eq pEq
                cla = rewrite pCV in abstractAtCheck thy n vty l [] cl pCV
                cra = rewrite pCV in abstractAtCheck thy n vty r [] cr pCV in
            rewrite sym (rightInjective prf) in
            MkWellFormedThm (hypsChecked wt)
              (mkEqCheckSound thy wf (Abs vty (abstractFvar (FVar n vty) l))
                              (Abs vty (abstractFvar (FVar n vty) r)) ty cla cra tl tr eq pEq)

-- -- soundness proofs: INST -------------------------------------------------
--
-- Instantiating free variables is substitution again, this time driven by
-- a list rather than a de Bruijn index.  The same trick as `BETA` keeps
-- `shift` out of it: `checkTheta` checks each replacement in the *empty*
-- environment, so every replacement is closed, and `instFvarLookup`'s
-- `shift depth 0` is the identity on it.

public export
data ThetaOk : Theory -> List (Term, Term) -> Type where
  ThetaOkNil  : ThetaOk thy []
  ThetaOkCons : checkTerm thy rep = Right () -> typeOf rep = typeOf x ->
                ThetaOk thy rest -> ThetaOk thy ((rep, x) :: rest)

-- `checkTheta` establishes exactly that.
export
checkThetaOk : (thy : Theory) -> (theta : List (Term, Term)) ->
                checkTheta thy theta = Right () -> ThetaOk thy theta
checkThetaOk thy [] prf = ThetaOkNil
checkThetaOk thy ((rep, FVar n vt) :: rest) prf with (checkTerm thy rep) proof pC
  checkThetaOk thy ((rep, FVar n vt) :: rest) prf | Left e = absurd prf
  checkThetaOk thy ((rep, FVar n vt) :: rest) prf | Right () with (typeOf rep) proof pR
    checkThetaOk thy ((rep, FVar n vt) :: rest) prf | Right () | Left e = absurd prf
    checkThetaOk thy ((rep, FVar n vt) :: rest) prf | Right () | Right rty
        with (vt /= rty) proof pNe
      checkThetaOk thy ((rep, FVar n vt) :: rest) prf | Right () | Right rty | True =
        absurd prf
      checkThetaOk thy ((rep, FVar n vt) :: rest) prf | Right () | Right rty | False =
        ThetaOkCons pC
          (trans pR (cong Right (sym (htypeEqSound vt rty (notFalseTrue (vt == rty) pNe)))))
          (checkThetaOk thy rest prf)
checkThetaOk thy ((rep, BVar _ _) :: rest) prf = absurd prf
checkThetaOk thy ((rep, Const _ _) :: rest) prf = absurd prf
checkThetaOk thy ((rep, Comb _ _) :: rest) prf = absurd prf
checkThetaOk thy ((rep, Abs _ _) :: rest) prf = absurd prf

-- A replacement the lookup finds is well-formed and has the type of the
-- variable it replaces.
instFvarLookupSound : (thy : Theory) -> (theta : List (Term, Term)) -> (v, u : Term) ->
                       (depth : Nat) -> (env : List HType) ->
                       ThetaOk thy theta -> instFvarLookup theta v depth = Just u ->
                       (checkOpenTerm thy u env = Right (), typeOf u = typeOf v)
instFvarLookupSound thy [] v u depth env ok prf = absurd prf
instFvarLookupSound thy ((rep, x) :: rest) v u depth env (ThetaOkCons cr tr oks) prf
    with (x == v) proof pXV
  instFvarLookupSound thy ((rep, x) :: rest) v u depth env (ThetaOkCons cr tr oks) prf | False =
    instFvarLookupSound thy rest v u depth env oks prf
  instFvarLookupSound thy ((rep, x) :: rest) v u depth env (ThetaOkCons cr tr oks) prf | True
      with (depth == 0)
    instFvarLookupSound thy ((rep, x) :: rest) v u depth env (ThetaOkCons cr tr oks) prf | True | True =
      rewrite sym (justInjective prf) in
      (checkWeakenRight thy rep [] env cr,
       replace {p = \z => typeOf rep = typeOf z} (termEqSound x v pXV) tr)
    instFvarLookupSound thy ((rep, x) :: rest) v u depth env (ThetaOkCons cr tr oks) prf | True | False =
      -- the shifted copy: `rep` is closed, so the shift is the identity
      rewrite sym (justInjective prf) in
      rewrite shiftClosedId (natToInteger depth) 0 rep (checkClosed thy rep [] cr) in
      (checkWeakenRight thy rep [] env cr,
       replace {p = \z => typeOf rep = typeOf z} (termEqSound x v pXV) tr)

instFvarGoType : (thy : Theory) -> (theta : List (Term, Term)) -> (t : Term) -> (depth : Nat) ->
                  ThetaOk thy theta -> typeOf (instFvarGo theta t depth) = typeOf t
instFvarGoType thy theta (FVar n ty) depth ok with (instFvarLookup theta (FVar n ty) depth) proof pL
  instFvarGoType thy theta (FVar n ty) depth ok | Nothing = Refl
  instFvarGoType thy theta (FVar n ty) depth ok | Just u =
    snd (instFvarLookupSound thy theta (FVar n ty) u depth [] ok pL)
instFvarGoType thy theta (BVar _ _) depth ok = Refl
instFvarGoType thy theta (Const _ _) depth ok = Refl
instFvarGoType thy theta (Comb f x) depth ok =
  cong (\ety => ety >>= (\fty => case destFun fty of
                                    Right (_, rng) => Right rng
                                    Left err => Left err))
       (instFvarGoType thy theta f depth ok)
instFvarGoType thy theta (Abs aty b) depth ok =
  rewrite instFvarGoType thy theta b (S depth) ok in Refl

export
instFvarGoCheck : (thy : Theory) -> (theta : List (Term, Term)) -> (t : Term) ->
                   (env : List HType) -> ThetaOk thy theta ->
                   checkOpenTerm thy t env = Right () ->
                   checkOpenTerm thy (instFvarGo theta t (length env)) env = Right ()
instFvarGoCheck thy theta (FVar n ty) env ok prf
    with (instFvarLookup theta (FVar n ty) (length env)) proof pL
  instFvarGoCheck thy theta (FVar n ty) env ok prf | Nothing = prf
  instFvarGoCheck thy theta (FVar n ty) env ok prf | Just u =
    fst (instFvarLookupSound thy theta (FVar n ty) u (length env) env ok pL)
instFvarGoCheck thy theta (Const n ty) env ok prf = prf
instFvarGoCheck thy theta (BVar i ty) env ok prf = prf
instFvarGoCheck thy theta (Comb f x) env ok prf
    with (checkOpenTerm thy f env) proof p1
  instFvarGoCheck thy theta (Comb f x) env ok prf | Left e = absurd prf
  instFvarGoCheck thy theta (Comb f x) env ok prf | Right ()
      with (checkOpenTerm thy x env) proof p2
    instFvarGoCheck thy theta (Comb f x) env ok prf | Right () | Left e = absurd prf
    instFvarGoCheck thy theta (Comb f x) env ok prf | Right () | Right () =
      rewrite instFvarGoCheck thy theta f env ok p1 in
      rewrite instFvarGoCheck thy theta x env ok p2 in
      rewrite instFvarGoType thy theta f (length env) ok in
      rewrite instFvarGoType thy theta x (length env) ok in
      prf
instFvarGoCheck thy theta (Abs aty b) env ok prf with (checkType thy aty) proof pCT
  instFvarGoCheck thy theta (Abs aty b) env ok prf | Left e = absurd prf
  instFvarGoCheck thy theta (Abs aty b) env ok prf | Right () =
    instFvarGoCheck thy theta b (aty :: env) ok prf

export
instFvarCheck : (thy : Theory) -> (theta : List (Term, Term)) -> (t : Term) ->
                 ThetaOk thy theta -> checkTerm thy t = Right () ->
                 checkTerm thy (instFvar theta t) = Right ()
instFvarCheck thy [] t ok prf = prf
instFvarCheck thy (p :: ps) t ok prf = instFvarGoCheck thy (p :: ps) t [] ok prf

-- Instantiating every hypothesis keeps the list well-formed, and so does
-- rebuilding its canonical form afterwards.
mapInstChecked : (thy : Theory) -> (theta : List (Term, Term)) -> (hs : List Term) ->
                  ThetaOk thy theta -> AllChecked thy hs ->
                  AllChecked thy (map (instFvar theta) hs)
mapInstChecked thy theta [] ok AllCheckedNil = AllCheckedNil
mapInstChecked thy theta (h :: hs) ok (AllCheckedCons ch cs) =
  AllCheckedCons (instFvarCheck thy theta h ok ch) (mapInstChecked thy theta hs ok cs)

export
rehashChecked : (thy : Theory) -> (hs : List Term) ->
                 AllChecked thy hs -> AllChecked thy (rehashHyps hs)
rehashChecked thy hs ph = foldlHypInsertChecked thy hs [] ph AllCheckedNil

export
instWellFormed : (thy : Theory) -> (theta : List (Term, Term)) -> (th' : Thm) ->
                  WellFormedThm thy th' -> (th : Thm) ->
                  instR thy theta th' = Right th -> WellFormedThm thy th
instWellFormed thy theta th' wt th prf with (inTheory thy th') proof pIn
  instWellFormed thy theta th' wt th prf | Left e = absurd prf
  instWellFormed thy theta th' wt th prf | Right () with (checkTheta thy theta) proof pCT
    instWellFormed thy theta th' wt th prf | Right () | Left e = absurd prf
    instWellFormed thy theta th' wt th prf | Right () | Right () =
      let ok = checkThetaOk thy theta pCT in
      rewrite sym (rightInjective prf) in
      MkWellFormedThm
        (rehashChecked thy (map (instFvar theta) (thmHyps th'))
                       (mapInstChecked thy theta (thmHyps th') ok (hypsChecked wt)))
        (instFvarCheck thy theta (thmConcl th') ok (conclChecked wt))

-- -- soundness proofs: INST_TYPE --------------------------------------------
--
-- Type instantiation rewrites the types *inside* a theorem, including the
-- binder types, so the environment a sub-term is checked against moves with
-- it -- hence the `map (typeSubst' tyin) env` in the statement below.  The
-- delicate case is `Const`: its check asks whether the use type is an
-- instance of the declared generic type, and instantiating must not break
-- that.  It does not, by `typeMatchSubst` (in `HType.idr`).

public export
data TyThetaOk : Theory -> List (Name, HType) -> Type where
  TyThetaOkNil  : TyThetaOk thy []
  TyThetaOkCons : checkType thy t = Right () -> TyThetaOk thy rest ->
                  TyThetaOk thy ((n, t) :: rest)

export
checkTypeListTyThetaOk : (thy : Theory) -> (tyin : List (Name, HType)) ->
                          checkTypeList thy (map Builtin.snd tyin) = Right () -> TyThetaOk thy tyin
checkTypeListTyThetaOk thy [] prf = TyThetaOkNil
checkTypeListTyThetaOk thy ((n, t) :: rest) prf with (checkType thy t) proof pC
  checkTypeListTyThetaOk thy ((n, t) :: rest) prf | Left e = absurd prf
  checkTypeListTyThetaOk thy ((n, t) :: rest) prf | Right () =
    TyThetaOkCons pC (checkTypeListTyThetaOk thy rest prf)

tyThetaLookup : (thy : Theory) -> (tyin : List (Name, HType)) -> (n : Name) -> (t : HType) ->
                 TyThetaOk thy tyin -> lookup n tyin = Just t -> checkType thy t = Right ()
tyThetaLookup thy [] n t ok prf = absurd prf
tyThetaLookup thy ((k, v) :: rest) n t (TyThetaOkCons cv oks) prf with (n == k)
  tyThetaLookup thy ((k, v) :: rest) n t (TyThetaOkCons cv oks) prf | True =
    rewrite sym (justInjective prf) in cv
  tyThetaLookup thy ((k, v) :: rest) n t (TyThetaOkCons cv oks) prf | False =
    tyThetaLookup thy rest n t oks prf

mutual
  export
  checkTypeSubst : (thy : Theory) -> (tyin : List (Name, HType)) -> (ty : HType) ->
                    TyThetaOk thy tyin -> checkType thy ty = Right () ->
                    checkType thy (typeSubst' tyin ty) = Right ()
  checkTypeSubst thy tyin (TyVar n) ok prf with (lookup n tyin) proof pL
    checkTypeSubst thy tyin (TyVar n) ok prf | Nothing = Refl
    checkTypeSubst thy tyin (TyVar n) ok prf | Just t = tyThetaLookup thy tyin n t ok pL
  checkTypeSubst thy tyin (TyApp n args) ok prf with (typeArity thy n) proof pA
    checkTypeSubst thy tyin (TyApp n args) ok prf | Nothing = absurd prf
    checkTypeSubst thy tyin (TyApp n args) ok prf | Just ar with (ar /= length args) proof pAr
      checkTypeSubst thy tyin (TyApp n args) ok prf | Just ar | True = absurd prf
      checkTypeSubst thy tyin (TyApp n args) ok prf | Just ar | False =
        rewrite typeSubstListLength tyin args in
        rewrite pAr in
        checkTypeListSubst thy tyin args ok prf

  checkTypeListSubst : (thy : Theory) -> (tyin : List (Name, HType)) -> (as : List HType) ->
                        TyThetaOk thy tyin -> checkTypeList thy as = Right () ->
                        checkTypeList thy (typeSubstList tyin as) = Right ()
  checkTypeListSubst thy tyin [] ok prf = Refl
  checkTypeListSubst thy tyin (a :: as) ok prf with (checkType thy a) proof pA
    checkTypeListSubst thy tyin (a :: as) ok prf | Left e = absurd prf
    checkTypeListSubst thy tyin (a :: as) ok prf | Right () =
      rewrite checkTypeSubst thy tyin a ok pA in
      checkTypeListSubst thy tyin as ok prf

export
typeOfInstType : (tyin : List (Name, HType)) -> (t : Term) -> (ty : HType) ->
                  typeOf t = Right ty ->
                  typeOf (instTypeGo tyin t) = Right (typeSubst' tyin ty)
typeOfInstType tyin (FVar n ty') ty prf = rewrite sym (rightInjective prf) in Refl
typeOfInstType tyin (BVar i ty') ty prf = rewrite sym (rightInjective prf) in Refl
typeOfInstType tyin (Const n ty') ty prf = rewrite sym (rightInjective prf) in Refl
typeOfInstType tyin (Abs aty b) ty prf with (typeOf b) proof pB
  typeOfInstType tyin (Abs aty b) ty prf | Left e = absurd prf
  typeOfInstType tyin (Abs aty b) ty prf | Right bty =
    rewrite typeOfInstType tyin b bty pB in
    rewrite sym (rightInjective prf) in Refl
typeOfInstType tyin (Comb f x) ty prf with (typeOf f) proof pF
  typeOfInstType tyin (Comb f x) ty prf | Left e = absurd prf
  typeOfInstType tyin (Comb f x) ty prf | Right fty with (destFun fty) proof pD
    typeOfInstType tyin (Comb f x) ty prf | Right fty | Left e = absurd prf
    typeOfInstType tyin (Comb f x) ty prf | Right fty | Right (dom, rng) =
      rewrite typeOfInstType tyin f fty pF in
      rewrite destFunSubst tyin fty dom rng pD in
      rewrite sym (rightInjective prf) in Refl

nthEnvMapSubst : (tyin : List (Name, HType)) -> (i : Nat) -> (env : List HType) ->
                  (ety : HType) -> nthEnv i env = Just ety ->
                  nthEnv i (map (typeSubst' tyin) env) = Just (typeSubst' tyin ety)
nthEnvMapSubst tyin _ [] ety prf = absurd prf
nthEnvMapSubst tyin Z (h :: hs) ety prf = rewrite sym (justInjective prf) in Refl
nthEnvMapSubst tyin (S k) (h :: hs) ety prf = nthEnvMapSubst tyin k hs ety prf

export
instTypeGoCheck : (thy : Theory) -> (tyin : List (Name, HType)) -> (t : Term) ->
                   (env : List HType) -> TyThetaOk thy tyin ->
                   checkOpenTerm thy t env = Right () ->
                   checkOpenTerm thy (instTypeGo tyin t) (map (typeSubst' tyin) env) = Right ()
instTypeGoCheck thy tyin (FVar n ty) env ok prf = checkTypeSubst thy tyin ty ok prf
instTypeGoCheck thy tyin (BVar i ty) env ok prf with (nthEnv i env) proof pN
  instTypeGoCheck thy tyin (BVar i ty) env ok prf | Nothing = absurd prf
  instTypeGoCheck thy tyin (BVar i ty) env ok prf | Just ety with (ety == ty) proof pE
    instTypeGoCheck thy tyin (BVar i ty) env ok prf | Just ety | False = absurd prf
    instTypeGoCheck thy tyin (BVar i ty) env ok prf | Just ety | True =
      rewrite nthEnvMapSubst tyin i env ety pN in
      rewrite htypeEqSound ety ty pE in
      rewrite htypeEqRefl (typeSubst' tyin ty) in
      checkTypeSubst thy tyin ty ok prf
instTypeGoCheck thy tyin (Const n ty) env ok prf with (checkType thy ty) proof pCT
  instTypeGoCheck thy tyin (Const n ty) env ok prf | Left e = absurd prf
  instTypeGoCheck thy tyin (Const n ty) env ok prf | Right ()
      with (constType thy n) proof pC
    instTypeGoCheck thy tyin (Const n ty) env ok prf | Right () | Nothing = absurd prf
    instTypeGoCheck thy tyin (Const n ty) env ok prf | Right () | Just gty
        with (typeMatch gty ty []) proof pM
      instTypeGoCheck thy tyin (Const n ty) env ok prf | Right () | Just gty | Nothing =
        absurd prf
      instTypeGoCheck thy tyin (Const n ty) env ok prf | Right () | Just gty | Just m =
        -- the instantiated use type is still an instance of the declared
        -- generic type -- `typeMatchSubst`, with the empty accumulator
        -- substituted (which is itself empty)
        rewrite checkTypeSubst thy tyin ty ok pCT in
        rewrite typeMatchSubst tyin gty ty [] m pM in
        Refl
instTypeGoCheck thy tyin (Comb f x) env ok prf with (checkOpenTerm thy f env) proof p1
  instTypeGoCheck thy tyin (Comb f x) env ok prf | Left e = absurd prf
  instTypeGoCheck thy tyin (Comb f x) env ok prf | Right ()
      with (checkOpenTerm thy x env) proof p2
    instTypeGoCheck thy tyin (Comb f x) env ok prf | Right () | Left e = absurd prf
    instTypeGoCheck thy tyin (Comb f x) env ok prf | Right () | Right ()
        with (typeOf f) proof pF
      instTypeGoCheck thy tyin (Comb f x) env ok prf | Right () | Right () | Left e =
        absurd prf
      instTypeGoCheck thy tyin (Comb f x) env ok prf | Right () | Right () | Right fty
          with (isFun fty) proof pIF
        instTypeGoCheck thy tyin (Comb f x) env ok prf | Right () | Right () | Right fty | False =
          absurd prf
        instTypeGoCheck thy tyin (Comb f x) env ok prf | Right () | Right () | Right fty | True
            with (destFun fty) proof pD
          instTypeGoCheck thy tyin (Comb f x) env ok prf | Right () | Right () | Right fty | True | Left e =
            absurd prf
          instTypeGoCheck thy tyin (Comb f x) env ok prf | Right () | Right () | Right fty | True | Right (dom, rng)
              with (typeOf x) proof pX
            instTypeGoCheck thy tyin (Comb f x) env ok prf | Right () | Right () | Right fty | True | Right (dom, rng) | Left e =
              absurd prf
            instTypeGoCheck thy tyin (Comb f x) env ok prf | Right () | Right () | Right fty | True | Right (dom, rng) | Right xty
                with (dom == xty) proof pDX
              instTypeGoCheck thy tyin (Comb f x) env ok prf | Right () | Right () | Right fty | True | Right (dom, rng) | Right xty | False =
                absurd prf
              instTypeGoCheck thy tyin (Comb f x) env ok prf | Right () | Right () | Right fty | True | Right (dom, rng) | Right xty | True =
                rewrite instTypeGoCheck thy tyin f env ok p1 in
                rewrite instTypeGoCheck thy tyin x env ok p2 in
                rewrite typeOfInstType tyin f fty pF in
                rewrite destFunIsFun (typeSubst' tyin fty)
                                     (typeSubst' tyin dom) (typeSubst' tyin rng)
                                     (destFunSubst tyin fty dom rng pD) in
                rewrite destFunSubst tyin fty dom rng pD in
                rewrite typeOfInstType tyin x xty pX in
                rewrite htypeEqSound dom xty pDX in
                rewrite htypeEqRefl (typeSubst' tyin xty) in
                Refl
instTypeGoCheck thy tyin (Abs aty b) env ok prf with (checkType thy aty) proof pCT
  instTypeGoCheck thy tyin (Abs aty b) env ok prf | Left e = absurd prf
  instTypeGoCheck thy tyin (Abs aty b) env ok prf | Right () =
    rewrite checkTypeSubst thy tyin aty ok pCT in
    instTypeGoCheck thy tyin b (aty :: env) ok prf

export
instTypeCheck : (thy : Theory) -> (tyin : List (Name, HType)) -> (t : Term) ->
                 TyThetaOk thy tyin -> checkTerm thy t = Right () ->
                 checkTerm thy (instType tyin t) = Right ()
instTypeCheck thy [] t ok prf = prf
instTypeCheck thy (p :: ps) t ok prf = instTypeGoCheck thy (p :: ps) t [] ok prf

mapInstTypeChecked : (thy : Theory) -> (tyin : List (Name, HType)) -> (hs : List Term) ->
                      TyThetaOk thy tyin -> AllChecked thy hs ->
                      AllChecked thy (map (instType tyin) hs)
mapInstTypeChecked thy tyin [] ok AllCheckedNil = AllCheckedNil
mapInstTypeChecked thy tyin (h :: hs) ok (AllCheckedCons ch cs) =
  AllCheckedCons (instTypeCheck thy tyin h ok ch) (mapInstTypeChecked thy tyin hs ok cs)

export
instTypeWellFormed : (thy : Theory) -> (tyin : List (Name, HType)) -> (th' : Thm) ->
                      WellFormedThm thy th' -> (th : Thm) ->
                      instTypeR thy tyin th' = Right th -> WellFormedThm thy th
instTypeWellFormed thy tyin th' wt th prf with (inTheory thy th') proof pIn
  instTypeWellFormed thy tyin th' wt th prf | Left e = absurd prf
  instTypeWellFormed thy tyin th' wt th prf | Right ()
      with (checkTypeList thy (map snd tyin)) proof pCT
    instTypeWellFormed thy tyin th' wt th prf | Right () | Left e = absurd prf
    instTypeWellFormed thy tyin th' wt th prf | Right () | Right () =
      let ok = checkTypeListTyThetaOk thy tyin pCT in
      rewrite sym (rightInjective prf) in
      MkWellFormedThm
        (rehashChecked thy (map (instType tyin) (thmHyps th'))
                       (mapInstTypeChecked thy tyin (thmHyps th') ok (hypsChecked wt)))
        (instTypeCheck thy tyin (thmConcl th') ok (conclChecked wt))

-- -- theory extension -----------------------------------------------------

export
newType : Theory -> Nat -> Name -> Nat -> Either String Theory
newType thy fresh n arity =
  case typeArity thy n of
    Just _  => Left ("type constructor is already declared: " ++ show n)
    Nothing => Right (extend thy fresh ((n, arity) :: tyops thy) (consts thy)
                              (axioms thy) (defs thy))

export
newConstant : Theory -> Nat -> Name -> HType -> Either String Theory
newConstant thy fresh n ty =
  case constType thy n of
    Just _  => Left ("constant is already declared: " ++ show n)
    Nothing => do
      checkType thy ty
      Right (extend thy fresh (tyops thy) ((n, ty) :: consts thy)
                    (axioms thy) (defs thy))

-- -- soundness proof: theory extension is monotonic ------------------------
--
-- Declaring a new type constructor never un-declares an existing one. This
-- is what makes `in_theory`/`descends` meaningful at all: a theorem proved
-- against an ancestor theory is only safe to reuse in an extension because
-- the extension is guaranteed to still recognize everything the ancestor
-- did. Without this, `in_theory` would be checking a lineage relationship
-- that doesn't actually guarantee semantic compatibility.
export
newTypeMonotone : (thy : Theory) -> (fresh : Nat) -> (n : Name) -> (arity : Nat) -> (thy2 : Theory) ->
                  newType thy fresh n arity = Right thy2 ->
                  (n2 : Name) -> (a2 : Nat) -> typeArity thy n2 = Just a2 ->
                  typeArity thy2 n2 = Just a2
newTypeMonotone thy fresh n arity thy2 nt n2 a2 prevDecl
    with (typeArity thy n) proof pTA
  newTypeMonotone thy fresh n arity thy2 nt n2 a2 prevDecl | Just _ = absurd nt
  newTypeMonotone thy fresh n arity thy2 nt n2 a2 prevDecl | Nothing
      with (n2 == n) proof pEq
    newTypeMonotone thy fresh n arity thy2 nt n2 a2 prevDecl | Nothing | True =
      -- n2 == n, so typeArity thy n2 = typeArity thy n = Nothing (pTA) --
      -- contradicting the hypothesis that thy already declares n2.
      let n2EqN = nameEqSound n2 n pEq in
      let prevDecl' = the (typeArity thy n = Just a2) (rewrite sym n2EqN in prevDecl) in
      absurd (trans (sym prevDecl') pTA)
    newTypeMonotone thy fresh n arity thy2 nt n2 a2 prevDecl | Nothing | False =
      let thy2Eq = rightInjective nt in
      rewrite sym thy2Eq in
      rewrite pEq in
      prevDecl

export
newConstantMonotone : (thy : Theory) -> (fresh : Nat) -> (n : Name) -> (ty : HType) -> (thy2 : Theory) ->
                       newConstant thy fresh n ty = Right thy2 ->
                       (n2 : Name) -> (a2 : HType) -> constType thy n2 = Just a2 ->
                       constType thy2 n2 = Just a2
newConstantMonotone thy fresh n ty thy2 nt n2 a2 prevDecl
    with (constType thy n) proof pCT
  newConstantMonotone thy fresh n ty thy2 nt n2 a2 prevDecl | Just _ = absurd nt
  newConstantMonotone thy fresh n ty thy2 nt n2 a2 prevDecl | Nothing
      with (checkType thy ty) proof pChk
    newConstantMonotone thy fresh n ty thy2 nt n2 a2 prevDecl | Nothing | Left e = absurd nt
    newConstantMonotone thy fresh n ty thy2 nt n2 a2 prevDecl | Nothing | Right ()
        with (n2 == n) proof pEq
      newConstantMonotone thy fresh n ty thy2 nt n2 a2 prevDecl | Nothing | Right () | True =
        let n2EqN = nameEqSound n2 n pEq in
        let prevDecl' = the (constType thy n = Just a2) (rewrite sym n2EqN in prevDecl) in
        absurd (trans (sym prevDecl') pCT)
      newConstantMonotone thy fresh n ty thy2 nt n2 a2 prevDecl | Nothing | Right () | False =
        let thy2Eq = rightInjective nt in
        rewrite sym thy2Eq in
        rewrite pEq in
        prevDecl

-- The escape hatch: every use shows up in `axiomsOf`.
export
newAxiom : Theory -> Nat -> Term -> Either String (Theory, Thm)
newAxiom thy fresh p = do
  checkProp thy p
  let st = nextStamp fresh (thyStamp thy)
  let th = MkThm [] p st
  Right (MkTheory (tyops thy) (consts thy) (th :: axioms thy) (defs thy) st, th)

termTypeVars : Term -> List Name
termTypeVars t = walk t []
  where
    add : HType -> List Name -> List Name
    add ty acc = foldl (\a, v => if v `elem` a then a else a ++ [v]) acc (typeVars ty)
    walk : Term -> List Name -> List Name
    walk (FVar _ ty) acc  = add ty acc
    walk (BVar _ ty) acc  = add ty acc
    walk (Const _ ty) acc = add ty acc
    walk (Comb f x) acc   = walk x (walk f acc)
    walk (Abs aty b) acc  = walk b (add aty acc)

-- A conservative definition: `c = rhs` where `c` is undeclared, `rhs` is
-- closed, and `rhs` has no type variables beyond those of its own type.
export
newBasicDefinition : Theory -> Nat -> Term -> Either String (Theory, Thm)
newBasicDefinition thy fresh tm =
  case destEq tm of
    Nothing => Left "definition is not an equation"
    Just (FVar n ty, rhs) => do
      case constType thy n of
        Just _  => Left ("constant is already declared: " ++ show n)
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
newBasicTypeDefinition : Theory -> Nat -> Name -> Name -> Name -> Thm
                        -> Either String (Theory, Thm, Thm)
newBasicTypeDefinition thy fresh tyname absname repname th = do
  inTheory thy th
  when (isJust (constType thy absname) || isJust (constType thy repname))
    (Left "constant is already declared")
  when (isJust (typeArity thy tyname))
    (Left ("type constructor is already declared: " ++ show tyname))
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
      -- The two names `kernel.rhm` writes here, `names.rhm`'s `v_alpha`
      -- and `v_rep`.  Which names they are does not matter logically --
      -- `pred` is checked closed, and a free variable in a conclusion is
      -- instantiable -- but they must be *the same* names, or the two
      -- kernels produce different theorems.
      let a = mkVar NAlpha aty
      let r = mkVar NRepVar rty
      eq1 <- mkEq (Comb absC (Comb repC a)) a
      inner <- mkEq (Comb repC (Comb absC r)) r
      eq2 <- mkEq (Comb pred r) inner
      Right (thy2, MkThm [] eq1 st, MkThm [] eq2 st)
    _ => Left "witness theorem is not an application"
  where
    when : Bool -> Either String () -> Either String ()
    when True e  = e
    when False _ = Right ()

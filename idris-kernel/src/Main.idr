module Main
-- Smoke test for the Idris2 kernel prototype, run through the Racket
-- backend:
--
--   idris2 --cg racket -o kernel src/Main.idr
--   racket build/exec/kernel
--
-- Exercises every one of the ten primitive rules plus theory extension, not
-- just the first few: idris2's codegen only emits functions reachable from
-- `main`, so a rule this file never calls is silently *absent* from the
-- generated Racket, not merely untested -- `rhombus-hol-lib/.../kernel.rhm`
-- calling it via `ik.#{Kernel-whatever}` would then fail at Rhombus
-- compile/require time with "no such imported identifier", far from here.
-- Keep every `export`ed `Kernel` function reachable from `main`.

import Data.Maybe
import HType
import Term
import Kernel

%default covering

-- Idris2's own `putStrLn` routes through `libidris2_support.so` on the
-- Racket backend (`idris2_putStr`, an FFI call into the runtime support
-- library idris2 ships). `kernel.rhm` never calls anything in `Main` --
-- only bare `Kernel-*` functions -- so that whole FFI/shared-library load
-- is dead weight from the integration's point of view, paid once per
-- `raco test` subprocess for no reason. Calling straight into Racket's own
-- `display`, bypassing idris2's runtime support library entirely, drops
-- `idris_kernel_gen.rkt`'s only foreign-library dependency (confirmed by
-- `grep ffi-lib` on the generated file coming up empty).
%foreign "scheme,racket:display"
prim__display : String -> PrimIO ()

myPutStrLn : String -> IO ()
myPutStrLn s = primIO (prim__display (s ++ "\n"))

report : Show a => String -> Either String a -> IO ()
report label (Right v) = myPutStrLn (label ++ ": ok -> " ++ show v)
report label (Left err) = myPutStrLn (label ++ ": FAILED -> " ++ err)

reportPair : (Show a, Show b) => String -> Either String (a, b) -> IO ()
reportPair label = report label

main : IO ()
main = do
  let thy0 = initialTheory "thy0"
  let x = mkVar "x" boolTy
  report "REFL x" (reflR thy0 x)

  case newConstant thy0 "thy1" "p" boolTy of
    Left err => myPutStrLn ("newConstant: FAILED -> " ++ err)
    Right thy1 => do
      let p = mkConst "p" boolTy
      let (Right th_p) = reflR thy1 p
        | Left err => myPutStrLn ("REFL p: FAILED -> " ++ err)
      report "TRANS (p=p) (p=p)" (transR th_p th_p)

      let idAbs = mkAbs x x
      case idAbs of
        Left err => myPutStrLn ("mkAbs: FAILED -> " ++ err)
        Right idT => do
          case mkComb idT x of
            Left err => myPutStrLn ("mkComb: FAILED -> " ++ err)
            Right redex => report "BETA (\\x.x) x" (betaR thy1 redex)

      report "ASSUME p" (assumeR thy1 p)
      let (Right th_assume_p) = assumeR thy1 p
        | Left err => myPutStrLn ("ASSUME p: FAILED -> " ++ err)
      report "MK_COMB (p=p) (p=p)" (mkCombR th_p th_p)
      let (Right p_eq_p) = mkEq p p
        | Left err => myPutStrLn ("mkEq: FAILED -> " ++ err)
      case reflR thy1 p_eq_p of
        Left err => myPutStrLn ("REFL (p=p): FAILED -> " ++ err)
        Right th_refl_eq => report "EQ_MP (REFL (p=p)) (p=p)" (eqMpR th_refl_eq th_p)
      report "DEDUCT_ANTISYM_RULE (p=p) (p=p)" (deductAntisymRule th_p th_p)
      case absR thy1 x th_p of
        Left err => myPutStrLn ("ABS: FAILED -> " ++ err)
        Right th_abs => myPutStrLn ("ABS x (p=p): ok -> " ++ show th_abs)
      report "INST [] (p=p)" (instR thy1 [] th_p)
      report "INST_TYPE [] (p=p)" (instTypeR thy1 [] th_p)

      myPutStrLn ("checkType bool: " ++ show (checkType thy1 boolTy))
      myPutStrLn ("checkTerm p: " ++ show (checkTerm thy1 p))
      myPutStrLn ("isBool p: " ++ show (isBool p))
      myPutStrLn ("typeArity bool: " ++ show (typeArity thy1 "bool"))
      myPutStrLn ("constType p: " ++ show (constType thy1 "p"))
      myPutStrLn ("isEq (p=p): " ++ show (isEq p_eq_p))
      myPutStrLn ("destEq (p=p): " ++ show (isJust (destEq p_eq_p)))
      myPutStrLn ("hypsOf (ASSUME p): " ++ show (hypsOf th_assume_p))
      myPutStrLn ("conclOf (ASSUME p): " ++ show (conclOf th_assume_p))
      myPutStrLn ("descends: " ++ show (descends (stampOf th_p) (thyStamp thy1)))
      myPutStrLn ("axiomsOf thy1: " ++ show (length (axiomsOf thy1)))
      myPutStrLn ("definitionOf thy1 p: " ++ show (isJust (definitionOf thy1 "p")))

      -- `th_p : |- p = p` is `Comb (Comb (Const "eq" ...) p) p`, which
      -- already parses as `Comb pred witness` with `pred = Comb eq p` and
      -- `witness = p` -- no separate proof needed to exercise this rule.
      case newBasicTypeDefinition thy1 "thy1b" "unit_ty2" "absu" "repu" th_p of
        Left err => myPutStrLn ("newBasicTypeDefinition: FAILED -> " ++ err)
        Right (_, th_abs_rep, th_pred) =>
          myPutStrLn ("newBasicTypeDefinition: ok -> " ++ show th_abs_rep ++ " / " ++ show th_pred)

  case newType thy0 "thy2" "unit_ty" 0 of
    Left err => myPutStrLn ("newType: FAILED -> " ++ err)
    Right thy2 =>
      case newAxiom thy2 "thy3" (mkConst "p" boolTy) of
        Left err => myPutStrLn ("newAxiom: FAILED -> " ++ err)
        Right (thy3, _) =>
          case newConstant thy3 "thy4" "q" boolTy of
            Left err => myPutStrLn ("newConstant q: FAILED -> " ++ err)
            Right thy4 =>
              case mkEq (mkVar "c" boolTy) (mkConst "q" boolTy) of
                Left err => myPutStrLn ("mkEq c=q: FAILED -> " ++ err)
                Right defTm =>
                  case newBasicDefinition thy4 "thy5" defTm of
                    Left err => myPutStrLn ("newBasicDefinition: FAILED -> " ++ err)
                    Right (thy5, defTh) => myPutStrLn ("newBasicDefinition: ok -> " ++ show defTh)

  myPutStrLn "idris-kernel smoke test done"

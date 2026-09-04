module Main
-- Smoke test for the Idris2 kernel prototype, run through the Racket
-- backend:
--
--   idris2 --cg racket -o kernel src/Main.idr
--   racket build/exec/kernel
--
-- Exercises `initial_theory`, `REFL`, `ABS`+`BETA`, and one theory
-- extension, mirroring the first few checks in
-- rhombus-hol/rhombus/hol/tests/kernel.rhm.

import HType
import Term
import Kernel

%default covering

report : Show a => String -> Either String a -> IO ()
report label (Right v) = putStrLn (label ++ ": ok -> " ++ show v)
report label (Left err) = putStrLn (label ++ ": FAILED -> " ++ err)

main : IO ()
main = do
  let (thy0, fresh0) = initialTheory 0
  let x = mkVar "x" boolTy
  report "REFL x" (reflR thy0 x)

  let idAbs = mkAbs x x
  case idAbs of
    Left err => putStrLn ("mkAbs: FAILED -> " ++ err)
    Right idT => do
      case mkComb idT x of
        Left err => putStrLn ("mkComb: FAILED -> " ++ err)
        Right redex => report "BETA (\\x.x) x" (betaR thy0 redex)

  case newConstant thy0 fresh0 "p" boolTy of
    Left err => putStrLn ("newConstant: FAILED -> " ++ err)
    Right (thy1, fresh1) =>
      report "REFL p (after new_constant)" (reflR thy1 (mkConst "p" boolTy))

  putStrLn "idris-kernel smoke test done"

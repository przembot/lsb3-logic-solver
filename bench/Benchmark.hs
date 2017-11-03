module Main where

import Criterion.Main
import Lib


tautFormulas :: [Logic]
tautFormulas = [
    BinForm Impl (C (BinForm Impl (Var 'a') (Var 'b')))
                 (BinForm Impl (C (Var 'a')) (C (Var 'b')))
  , BinForm Impl (C (Var 'a')) (Not (C (Not (Var 'a'))))
  , BinForm Equiv (C (BinForm And (Var 'a') (Var 'b')))
                  (BinForm And (C (Var 'a')) (C (Var 'b')))
  , BinForm Impl (BinForm Or (C (Var 'a')) (C (Var 'b')))
                 (C (BinForm Or (Var 'a') (Var 'b')))
  , BinForm Equiv (C (Var 'a')) (C (Not (Not (Var 'a'))))
  , Not (C (BinForm And (Var 'a') (Not (Var 'a'))))
  , BinForm Impl (C (BinForm And (Var 'a') (Not (Var 'a'))))
                 (C (Var 'b'))
  ]

hugeTaut :: Logic
hugeTaut = foldl1 (BinForm And) tautFormulas

atrans, btrans :: String
atrans = "pqrstu"
btrans = reverse atrans

vars :: [(Char,Char)]
vars = zip atrans btrans

replaceVars :: (Char -> Logic) -> Logic -> Logic
replaceVars f (Var a) = f a
replaceVars f (BinForm op a b) = BinForm op (replaceVars f a) (replaceVars f b)
replaceVars f (Not a) = Not (replaceVars f a)
replaceVars f (C a) = C (replaceVars f a)
replaceVars _ x = x

hugeTautManyVars :: Logic
hugeTautManyVars = foldl1 (BinForm And) . zipWith (\(a,b) form ->
  replaceVars (\c -> if c == 'a' then Var a else Var b) form) vars $ tautFormulas


genTestCase :: Logic -> [Benchmark]
genTestCase expr =
  [ bench "LSB3T naiveSolverSat" $ whnf runNaiveSatT expr
  , bench "LSB3T naiveSolverTaut" $ whnf runNaiveTautT expr
  , bench "LSB3P naiveSolverSat" $ whnf runNaiveSatP expr
  , bench "LSB3P naiveSolverTaut" $ whnf runNaiveTautP expr
  , bench "LSB3T DPLLSolverSat" $ whnf runSatTDPLL expr
  , bench "LSB3T DPLLSolverTaut" $ whnf runTautTDPLL expr
  , bench "LSB3P DPLLSolverSat" $ whnf runSatPDPLL expr
  , bench "LSB3P DPLLSolverTaut" $ whnf runTautPDPLL expr
  ]

main :: IO ()
main =
  defaultMain
    [ bgroup "sample" (genTestCase hugeTaut)
    , bgroup "6vars" (genTestCase hugeTautManyVars)
    ]

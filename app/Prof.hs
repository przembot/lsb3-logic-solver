{-# LANGUAGE BangPatterns #-}
module Main where

import Lib
import Data.Text.IO as T (readFile)
-- import Criterion.Main

main :: IO ()
main = do
  {-
  (Right !x) <- parseLogic <$> T.readFile "bench/bigsample"
  defaultMain
    [ bench "naive" $ whnf (uniRunSat Naive LSB3P) x
    , bench "DPLL" $ whnf (uniRunSat DPLL LSB3P) x
    ]
    -}
  (Right !x) <- parseLogic <$> T.readFile "bench/bigsample"
  print $ uniRunSat DPLL LSB3P x

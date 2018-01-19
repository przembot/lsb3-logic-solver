{-# LANGUAGE BangPatterns #-}
module Main where

import Lib
import Data.Text.IO as T (readFile)

main :: IO ()
main = do
  (Right !x) <- parseLogic <$> T.readFile "bench/ex10"
  print $ uniRunSat LSB3P DPLL x

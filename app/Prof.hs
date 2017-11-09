module Main where

import Lib
import Data.Text.IO as T (readFile)

main :: IO ()
main = do
  (Right x) <- parseLogic <$> T.readFile "bench/bigsample"
  print $ uniRunSat DPLL LSB3T x

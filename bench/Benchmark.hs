{-# LANGUAGE BangPatterns #-}
module Main where

import Lib
import Data.Text.IO as T (readFile)
import Criterion.Main

toMaybe :: Either e a -> Maybe a
toMaybe (Right x) = Just x
toMaybe _ = Nothing

singleGroup :: SolverType -> [(Int, Logic)] -> [Benchmark]
singleGroup st = map
  (\(num, form) -> bench ("przyklad "++show num) $ nf (toMaybe . uniRunSat LSB3P st) form)

files :: [(Int, FilePath)]
files = take 10 . map (\num -> (num, "bench/ex"++show num)) $ [1..]

loadFormula :: Either a Logic -> Logic
loadFormula (Right !x) = x

main :: IO ()
main = do
  !examples <- map (fmap $ loadFormula . parseLogic) <$> mapM (traverse T.readFile) files
  defaultMain
    [ bgroup "dpll" $ singleGroup DPLL examples
    , bgroup "naive" $ singleGroup Naive (take 5 $ examples)
    ]

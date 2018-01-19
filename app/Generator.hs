{-# LANGUAGE LambdaCase #-}
module Main where

import Lib
import System.Timeout (timeout)
import System.TimeIt (timeItT)
import Data.Maybe (isNothing)


-- | Maksymalny czas wykonywania
-- | dla szukania spelnialnosci
-- | dla algorytmu naiwnego.
-- | Wyrażony w mikrosekundach.
maxTimeLong, maxTimeShort :: Int
maxTimeLong = 30 * (10^(6 :: Int))
maxTimeShort = 2 * (10^(6 :: Int))

inRange :: Double -> Bool
inRange x = x <= 2.0

-- | Czy weryfikacja podanego przykladu
-- | testowego konczy sie w okreslonym czasie
longExamplePred :: Logic -> IO Bool
longExamplePred form =
  isNothing <$> timeout maxTimeLong (timeItT . return $! uniRunSat LSB3P Naive form)

shortExamplePred :: Logic -> IO Bool
shortExamplePred form =
  (\case
    Just (time, _) -> inRange time
    _ -> False
  )
  <$> timeout maxTimeShort (timeItT . return $! uniRunSat LSB3P Naive form)

saveSample :: Int -> Logic -> IO ()
saveSample num form =
  writeFile ("bench/ex"++show num) (show form)


-- | Funkcja generujaca i zapisujaca poprawny przyklad
sampleGen :: (Logic -> IO Bool) -> Int -> IO ()
sampleGen check num = do
  x <- generateBigSample
  filterResult <- check x
  if filterResult
     then putStrLn "sample generated" >> saveSample num x
     else sampleGen check num


-- | Generowane są dwa rozne rodzaje przypadkow testowych, po 5
-- | pierwszy - formuly, ktore dla algorytmu naiwnego
-- | wykonuja sie krocej niz sekunde
-- | drugi - formuly, ktore dla algorytmu naiwnego wykonuja sie ponad 20 sekund
main :: IO ()
main = do
  mapM_ (sampleGen shortExamplePred) . take 5 $ [1..]
  mapM_ (sampleGen longExamplePred) . take 5 $ [6..]

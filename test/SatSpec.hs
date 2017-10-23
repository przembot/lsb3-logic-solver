module SatSpec (spec) where

import Test.Hspec
import Lib


-- | Formuly bedace tautologiami LSB3_t
tautFormulas :: [Logic]
tautFormulas = [
    Not $ C (BinForm And (Var 'a') (Not (Var 'a')))
  , BinForm Impl (C (BinForm Impl (Var 'a') (Var 'b')))
                 (BinForm Impl (C (Var 'a')) (C (Var 'b')))
  , Not (C (BinForm And (Var 'a') (Not (Var 'a'))))
  , BinForm Impl (C (BinForm And (Var 'a') (Not (Var 'a'))))
                 (C (Var 'b'))
  , BinForm Equiv (C (Var 'a')) (C (Not (Not (Var 'a'))))
  ]

-- | Formuly spelnialne w LSB3_t
satFormulas :: [Logic]
satFormulas = [
  BinForm Impl (Not (C (Not (Var 'p')))) (C (Var 'p'))
  ]

-- | Formuly niespelnialne w LSB3_t
-- czyli negacje tautologii z LSB3_t
unsatFormulas :: [Logic]
unsatFormulas = map Not tautFormulas

-- Liczby naturalne
nats :: [Int]
nats = 1 : map (+1) nats

shouldSat, shouldNotSat, shouldSatTaut :: (Logic -> Bool) -- ^ solver
                                       -> Spec
shouldSat sat = mapM_ (\(f, num) ->
                  it ("should sat "++(show num)) $ sat f `shouldBe` True
                      ) $ zip (tautFormulas++satFormulas) nats

shouldNotSat sat = mapM_ (\(f, num) ->
                  it ("should unsat "++(show num)) $ sat f `shouldBe` False
                      ) $ zip unsatFormulas nats

shouldSatTaut sat = mapM_ (\(f, num) ->
                    it ("should sat (taut) "++(show num)) $ sat f `shouldBe` True
                       ) $ zip tautFormulas nats

spec :: Spec
spec = do
  describe "funkcja sat powinna spelniac" $
    shouldSat runSatDPLL
  describe "funkcja sat nie powinna spelniac" $
    shouldNotSat runSatDPLL
  describe "funkcja sat (taut) powinna spelniac" $
    shouldSatTaut runTautDPLL

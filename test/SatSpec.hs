module SatSpec (spec) where

import Test.Hspec
import Data.Either (isRight)

import Logic
import SAT

-- | Formuly bedace tautologiami LSB3_x
-- | przepisane w referatu
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

-- | Formuly bedace tautologiami w LSB3_T
tautTFormulas :: [Logic]
tautTFormulas = [
    C $ (BinForm Impl (Var 'q') (BinForm Impl (Var 'p') (Var 'q')))
  , C $ BinForm Impl (BinForm Impl (Var 'p') (Var 'q'))
                     (BinForm Impl (BinForm Impl (Var 'q') (Var 'r'))
                                   (BinForm Impl (Var 'p') (Var 'r')))
    ]

-- | Formuly bedace tautologiami w LSB3_P
tautPFormulas :: [Logic]
tautPFormulas = []

-- | Formuly spelnialne w LSB3_x
satFormulas :: [Logic]
satFormulas = [
  BinForm Impl (Not (C (Not (Var 'p')))) (C (Var 'p'))
  ]


-- | Formuly niespelnialne w LSB3_x
-- czyli negacje tautologii z LSB3_x
unsatFormulas :: [Logic]
unsatFormulas = map Not tautFormulas

-- Liczby naturalne
nats :: [Int]
nats = 1 : map (+1) nats

shouldSat, shouldNotSat :: (Logic -> SatResult) -- ^ solver
                        -> Spec
shouldSat sat = mapM_ (\(f, num) ->
  it ("should sat "++(show num)) $ isRight (sat f) `shouldBe` True
  ) $ zip (tautFormulas++satFormulas) nats

shouldNotSat sat = mapM_ (\(f, num) ->
  it ("should unsat "++(show num)) $ isRight (sat f) `shouldBe` False
  ) $ zip unsatFormulas nats

shouldSatTaut :: [Logic] -> (Logic -> TautResult) -> Spec
shouldSatTaut set sat = mapM_ (\(f, num) ->
  it ("should sat (taut) "++(show num)) $ isRight (sat f) `shouldBe` True
  ) $ zip set nats

shouldSatNoTaut :: [Logic] -> (Logic -> TautResult) -> Spec
shouldSatNoTaut forms sat = mapM_ (\(f, num) ->
  it ("should sat (no taut) "++(show num)) $ isRight (sat f) `shouldBe` False
  ) $ zip forms nats

spec :: Spec
spec = do
  describe "funkcja sat powinna spelniac" $ do
    describe "lsb3_p" $
      shouldSat runSatPDPLL
    describe "lsb3_t" $
      shouldSat runSatTDPLL
  describe "funkcja sat nie powinna spelniac" $ do
    describe "lsb3_p" $
      shouldNotSat runSatPDPLL
    describe "lsb3_t" $
      shouldNotSat runSatTDPLL
  describe "funkcja sat (taut) powinna spelniac" $ do
    describe "lsb3_p" $
      shouldSatTaut tautFormulas runTautPDPLL
    describe "lsb3_t" $
      shouldSatTaut (tautFormulas ++ tautTFormulas) runTautTDPLL
  describe "funkcja sat (taut) nie powinna spelniac" $ do
    describe "lsb3_p" $
      shouldSatNoTaut tautTFormulas runTautPDPLL

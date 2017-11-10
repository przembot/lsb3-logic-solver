module SatSpec (spec) where

import Test.Hspec
import Test.QuickCheck
import Data.Either (isRight)
import Data.Maybe (isJust)
import Data.List (foldl1')
import Data.Char (isLower)

import Logic
import SAT
import CNF

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
    C (BinForm Impl (Var 'q') (BinForm Impl (Var 'p') (Var 'q')))
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


-- | Wrapper na wyrazenie logiczne bedace
-- | w formacie CNF
newtype CNFLogic = CNFLogic { unCL :: Logic }
  deriving Show


instance Arbitrary CNFLogic where
  arbitrary = CNFLogic . cnfToLogic <$> sized cnf


singleelem :: Gen (Negable Atom)
singleelem = elements [Pure, NotE] <*> oneof [VarE <$> var]
  where
    var = suchThat arbitrary isLower

clause :: Int -> Int -> Gen Clause
clause n m = vectorOf n (elements [Pure, NotE] <*> vectorOf m singleelem)

cnf :: Int -> Gen CNF
cnf n = vectorOf x (clause 3 3)
  where
    x = ceiling ((fromIntegral n)/9 :: Float)
    -- x = ceiling (fromIntegral n ** (1/3) :: Float)


cnfToLogic :: CNF -> Logic
cnfToLogic = foldl1' (BinForm And)
           . map clauseToLogic
    where
      clauseToLogic = foldl1' (BinForm Or)
                    . map funcToLogic
      funcToLogic (Pure l) = C $ foldl1' (BinForm Or) (map natomToLogic l)
      funcToLogic (NotE l) = Not $ C $ foldl1' (BinForm Or) (map natomToLogic l)
      natomToLogic (Pure x) = atomToLogic x
      natomToLogic (NotE x) = Not $ atomToLogic x
      atomToLogic (Lit x) = Const x
      atomToLogic (VarE x) = Var x

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


prop_naive_dpll :: CNFLogic -> Property
prop_naive_dpll (CNFLogic expr) =
  (isRight (uniRunSat Naive LSB3T expr) ===
    isRight (uniRunSat DPLL LSB3T expr))



spec :: Spec
spec = do
  describe "funkcja sat powinna spelniac" $ do
    describe "lsb3_p" $
      shouldSat (uniRunSat DPLL LSB3P)
    describe "lsb3_t" $
      shouldSat (uniRunSat DPLL LSB3T)
  describe "funkcja sat nie powinna spelniac" $ do
    describe "lsb3_p" $
      shouldNotSat (uniRunSat DPLL LSB3P)
    describe "lsb3_t" $
      shouldNotSat (uniRunSat DPLL LSB3T)
  describe "funkcja sat (taut) powinna spelniac" $ do
    describe "lsb3_p" $
      shouldSatTaut tautFormulas (uniRunTaut DPLL LSB3P)
    describe "lsb3_t" $
      shouldSatTaut (tautFormulas ++ tautTFormulas) (uniRunTaut DPLL LSB3T)
  describe "funkcja sat (taut) nie powinna spelniac" $ do
    describe "lsb3_p" $
      shouldSatNoTaut tautTFormulas (uniRunTaut DPLL LSB3P)

  describe "dla dowolnego wyrazenia" $ do
    it "naiwny i heurystyczny znajduja rozwiazanie dla tego samego przypadku" $
      mapSize (const 50) $ property prop_naive_dpll

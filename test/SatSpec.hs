module SatSpec (spec) where

import Test.Hspec
import Test.QuickCheck
import Data.Either (isRight)
import Data.List (foldl1')
import Data.Char (isLower)

import Logic
import SAT
import NF

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
  -- De Morgan
  , BinForm Equiv (C (Not (BinForm Or (Var 'a') (Var 'b'))))
                  (C (BinForm And (Not (Var 'a')) (Not (Var 'b'))))
  , BinForm Equiv (C (Not (BinForm And (Var 'a') (Var 'b'))))
                  (C (BinForm Or (Not (Var 'a')) (Not (Var 'b'))))
  ]

-- | Formuly bedace tautologiami w LSB3_T
tautTFormulas :: [Logic]
tautTFormulas =
  [ C (BinForm Impl (Var 'q') (BinForm Impl (Var 'p') (Var 'q')))
  , C $ BinForm Impl (BinForm Impl (Var 'p') (Var 'q'))
                     (BinForm Impl (BinForm Impl (Var 'q') (Var 'r'))
                                   (BinForm Impl (Var 'p') (Var 'r')))
  ]

-- | Formuly bedace tautologiami w LSB3_P
tautPFormulas :: [Logic]
tautPFormulas =
  [ BinForm Equiv (C (BinForm Or (Var 'a') (Var 'b')))
                  (BinForm Or (C (Var 'a')) (C (Var 'b')))
  ]

-- | Formuly spelnialne w LSB3_x
satFormulas :: [Logic]
satFormulas = [
  BinForm Impl (Not (C (Not (Var 'p')))) (C (Var 'p'))
  ]

satTFormulas :: [Logic]
satTFormulas = [
  BinForm And (Not (C (Var 'a'))) (C (BinForm Or (Var 'a') (Const Neither)))
  ]

-- | Formuly niespelnialne w LSB3_x
-- czyli negacje tautologii z LSB3_x
unsatFormulas :: [Logic]
unsatFormulas = map Not tautFormulas

-- | Wrapper na wyrazenie logiczne bedace
-- | w formacie NF
newtype NFLogic = NFLogic { unCL :: Logic }
  deriving Show


instance Arbitrary NFLogic where
  arbitrary = NFLogic . cnfToLogic <$> sized cnf


singleelem :: Gen (Negable Atom)
singleelem = elements [Pure, NotE] <*> oneof [VarE <$> var, Lit <$> val]
  where
    var = suchThat arbitrary isLower
    val = elements [TrueV, Neither, FalseV]

clause :: Int -> Int -> Gen Clause
clause n m = vectorOf n (elements [Pure, NotE] <*> vectorOf m singleelem)

cnf :: Int -> Gen NF
cnf n = vectorOf x (clause 3 3)
  where
    x = ceiling (fromIntegral n/9 :: Float)
    -- x = ceiling (fromIntegral n ** (1/3) :: Float)


cnfToLogic :: NF -> Logic
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

-- Liczby naturalne
nats :: [Int]
nats = 1 : map (+1) nats

-- | Sprawdza, czy formula jest spelnialna
-- | uzywajac danych podstawien.
-- | Jezeli nie ma ktorejs ze zmiennych,
-- | sprawdza kazda mozliwosc
verifySubs :: LogicType -> Logic -> Interpretation -> Bool
verifySubs lt expr subs =
  let
    expr' = foldl (flip ($)) expr (map (uncurry substitudeNaiveVar) subs)
  in
    case findUnassignedVar expr' of
      Just var -> verifySubs lt expr' [(var, TrueV)]
               && verifySubs lt expr' [(var, Neither)]
               && verifySubs lt expr' [(var, FalseV)]
      Nothing ->
          case evalLogic lt expr' of
            Just val -> val == TrueV
            _ -> False

shouldSat, shouldNotSat :: LogicType
                        -> (LogicType -> Logic -> SatResult) -- ^ solver
                        -> Spec
shouldSat lt sat = mapM_ (\(f, num) ->
  it ("should sat "++ show num) $ (verifySubs lt f <$> sat lt f) `shouldBe` Right True
  ) $ zip (tautFormulas++satFormulas) nats

shouldNotSat lt sat = mapM_ (\(f, num) ->
  it ("should unsat "++ show num) $ sat lt f `shouldBe` Left NoInterpretationFound
  ) $ zip unsatFormulas nats

shouldSatExtra :: [Logic] -> (Logic -> SatResult)
               -> Spec
shouldSatExtra extra sat = mapM_ (\(f, num) ->
  it ("should sat "++ show num) $ isRight (sat f) `shouldBe` True
  ) $ zip (tautFormulas++satFormulas++extra) nats

shouldSatTaut :: [Logic] -> (Logic -> TautResult) -> Spec
shouldSatTaut set sat = mapM_ (\(f, num) ->
  it ("should sat (taut) "++ show num) $ isRight (sat f) `shouldBe` True
  ) $ zip set nats

shouldSatNoTaut :: [Logic] -> (Logic -> TautResult) -> Spec
shouldSatNoTaut forms sat = mapM_ (\(f, num) ->
  it ("should sat (no taut) "++ show num) $ isRight (sat f) `shouldBe` False
  ) $ zip forms nats


prop_naive_dpll :: LogicType -> NFLogic -> Property
prop_naive_dpll lt (NFLogic expr) =
  (verifySubs lt expr <$> (uniRunSat Naive lt expr)) ===
    (verifySubs lt expr <$> (uniRunSat DPLL lt expr))


-- | Dla zadanego typu solvera sprawdza,
-- | czy podstawowe aksjomaty i inne formuly
-- | sa spelnialne badz sa tautologiami
solverSpec :: SolverType -> Spec
solverSpec st =
  describe ("dla solvera typu " ++ show st) $ do
    describe "funkcja sat powinna spelniac" $ do
      describe "lsb3_p" $
        shouldSat LSB3P (uniRunSat st)
      describe "lsb3_t" $
        shouldSatExtra satTFormulas (uniRunSat st LSB3T)
    describe "funkcja sat nie powinna spelniac" $ do
      describe "lsb3_p" $
        shouldNotSat LSB3P (uniRunSat st)
      describe "lsb3_t" $
        shouldNotSat LSB3T (uniRunSat st)
    describe "funkcja sat (taut) powinna spelniac" $ do
      describe "lsb3_p" $
        shouldSatTaut (tautFormulas ++ tautPFormulas) (uniRunTaut st LSB3P)
      describe "lsb3_t" $
        shouldSatTaut (tautFormulas ++ tautTFormulas) (uniRunTaut st LSB3T)
    describe "funkcja sat (taut) nie powinna spelniac" $
      describe "lsb3_p" $
        shouldSatNoTaut tautTFormulas (uniRunTaut st LSB3P)


spec :: Spec
spec = do
  solverSpec Naive
  solverSpec DPLL
  describe "dla dowolnego wyrazenia" $ do
    it "naiwny i heurystyczny znajduja rozwiazanie dla tego samego przypadku: LSB3T" $
      mapSize (const 11) $ property $ prop_naive_dpll LSB3T
    it "naiwny i heurystyczny znajduja rozwiazanie dla tego samego przypadku: LSB3P" $
      mapSize (const 11) $ property $ prop_naive_dpll LSB3P

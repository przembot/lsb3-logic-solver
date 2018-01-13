{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module SatSpec (spec) where

import Test.Hspec
import Test.QuickCheck
import Data.Either (isRight)
import Data.Char (isLower)
import Data.Bifunctor (bimap)

import Logic
import SAT
import CNF


-- | Formuly bedace tautologiami LSB3
-- | przepisane z referatu
tautFormulas :: [Logic]
tautFormulas =
  [ BinForm Impl (C (BinForm Impl (Var 'a') (Var 'b')))
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

-- | Formuly bedace tautologiami tylko w LSB3_T
tautTFormulas :: [Logic]
tautTFormulas =
  [ C (BinForm Impl (Var 'q') (BinForm Impl (Var 'p') (Var 'q')))
  , C $ BinForm Impl (BinForm Impl (Var 'p') (Var 'q'))
                     (BinForm Impl (BinForm Impl (Var 'q') (Var 'r'))
                                   (BinForm Impl (Var 'p') (Var 'r')))
  ]

-- | Formuly bedace tautologiami tylko w LSB3_P
tautPFormulas :: [Logic]
tautPFormulas =
  [ BinForm Equiv (C (BinForm Or (Var 'a') (Var 'b')))
                  (BinForm Or (C (Var 'a')) (C (Var 'b')))
  -- dystrybucja wewnatrz funktora
  , BinForm Equiv (C (BinForm Or (Var 'a') (BinForm And (Var 'b') (Var 'c'))))
                  (C (BinForm And (BinForm Or (Var 'a') (Var 'b'))
                                  (BinForm Or (Var 'a') (Var 'c'))))
  ]

-- | Formuly spelnialne w LSB3
satFormulas :: [Logic]
satFormulas =
  [ BinForm Impl (Not (C (Not (Var 'p')))) (C (Var 'p'))
  -- dystrybucja wewnatrz funktora
  , BinForm Equiv (C (BinForm Or (Var 'a') (BinForm And (Var 'b') (Var 'c'))))
                  (C (BinForm And (BinForm Or (Var 'a') (Var 'b'))
                                  (BinForm Or (Var 'a') (Var 'c'))))
  ]

-- | Formuly spelnialne tylko w LSB3_T
satTFormulas :: [Logic]
satTFormulas =
  [ BinForm And (Not (C (Var 'a'))) (C (BinForm Or (Var 'a') (Const Neither)))
  , BinForm Or (Not (C (BinForm Or (Const TrueV) (Not (Var 'a')))))
               (C (BinForm Or (Not (Const Neither)) (Not (Var 'b'))))
  ]

-- | Formuly niespelnialne w LSB3
-- czyli negacje tautologii z LSB3
unsatFormulas :: [Logic]
unsatFormulas = map Not tautFormulas

-- | Wrapper na wyrazenie logiczne bedace
-- | w formacie CNF
newtype CNFLogic = CNFLogic { unCL :: Logic }
  deriving Show


instance Arbitrary CNFLogic where
  arbitrary = CNFLogic . cnfToLogic <$> sized cnf


singleelem :: Gen Elem
singleelem = elements [Pure . Pure, Pure . NotE, NotE . Pure, NotE . NotE] <*> oneof [VarE <$> var, Lit <$> val]
  where
    var = suchThat arbitrary isLower
    val = elements [TrueV, Neither, FalseV]

clause :: Int -> Gen Clause
clause n = vectorOf n singleelem


-- | Generator formuly logicznej bedacej juz
-- | w postaci normalnej
cnf :: Int -> Gen CNF
cnf n = vectorOf x (clause 3)
  where
    x = ceiling (fromIntegral n/3 :: Float)


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

-- | Pomocnicze funkcje generujace
-- | przypadki testowe z list formul
shouldSat, shouldNotSat :: LogicType
                        -> (LogicType -> Logic -> SatResult) -- ^ solver
                        -> Spec
shouldSat lt sat =
  mapM_ (\(f, num) ->
    it ("should sat "++ show num) $
      (verifySubs lt f <$> sat lt f) `shouldBe` Right True)
  $ zip (tautFormulas++satFormulas) nats

shouldNotSat lt sat =
  mapM_ (\(f, num) ->
    it ("should unsat "++ show num) $
      sat lt f `shouldBe` Left NoInterpretationFound)
  $ zip unsatFormulas nats

shouldSatExtra :: [Logic] -> (Logic -> SatResult)
               -> Spec
shouldSatExtra extra sat =
  mapM_ (\(f, num) ->
    it ("should sat "++ show num) $
      isRight (sat f) `shouldBe` True)
  $ zip (tautFormulas++satFormulas++extra) nats

shouldSatTaut :: [Logic] -> (Logic -> TautResult) -> Spec
shouldSatTaut set sat =
  mapM_ (\(f, num) ->
    it ("should sat (taut) "++ show num) $
      isRight (sat f) `shouldBe` True)
  $ zip set nats

shouldSatNoTaut :: [Logic] -> (Logic -> TautResult) -> Spec
shouldSatNoTaut forms sat =
  mapM_ (\(f, num) ->
    it ("should sat (no taut) "++ show num) $
      isRight (sat f) `shouldBe` False)
  $ zip forms nats


-- | Dla dowolnego wyrazenia, jezeli solver
-- | naiwny zwroci rozwiazanie, to heurystyczny tez
-- | zwroci poprawne. Jezeli podana formula
-- | nie jest spelnialna, to oba solvery tez
-- | to wykaza.
prop_naive_dpll_sat :: LogicType -> CNFLogic -> Property
prop_naive_dpll_sat lt (CNFLogic expr) = commonSat lt expr

-- | Podobnie jak wyzej, z tym ze formula jest dowolna
prop_all_naive_dpll_sat :: LogicType -> Logic -> Property
prop_all_naive_dpll_sat = commonSat

commonSat :: LogicType -> Logic -> Property
commonSat lt expr =
  (verifySubs lt expr <$> uniRunSat lt Naive expr) ===
    (verifySubs lt expr <$> uniRunSat lt DPLL expr)


-- | Dla dowolnego wyrazenia, jezeli jest ono tautologia,
-- | to oba solvery to wykaza, jezeli nie jest,
-- | to oba solvery podadza poprawny dowod.
prop_naive_dpll_taut :: LogicType -> CNFLogic -> Property
prop_naive_dpll_taut lt (CNFLogic expr) = commonTaut lt expr

-- | Podobnie jak wyzej, z tym ze formula jest dowolna
prop_all_naive_dpll_taut :: LogicType -> Logic -> Property
prop_all_naive_dpll_taut = commonTaut

commonTaut :: LogicType -> Logic -> Property
commonTaut lt expr =
  f (uniRunTaut lt Naive expr) === f (uniRunTaut lt DPLL expr)
    where
      f = bimap (\case
            TautologyFail proof ->
              if not (verifySubs lt expr proof)
                 then False
                 else error $
                   "dowod nietautologicznosci jest bledny " ++ show proof
            e -> error (show e)
          ) id

-- | Dla dowolnej formuly,
-- | jezeli okaze sie spelnialna,
-- | to dowod dla niej jest poprawny
prop_lsb3t_sat :: Logic -> Property
prop_lsb3t_sat = commonT

commonT :: Logic -> Property
commonT expr =
  let
    a = uniRunSat LSB3T Naive expr
  in
    isRight a ==> ((verifySubs LSB3T expr <$> a) === Right True)



-- | Dla zadanego typu solvera sprawdza,
-- | czy podstawowe aksjomaty i inne formuly
-- | sa spelnialne badz sa tautologiami
solverSpec :: SolverType -> Spec
solverSpec st =
  describe ("dla solvera typu " ++ show st) $ do
    describe "funkcja sat powinna spelniac" $ do
      describe "lsb3_p" $
        shouldSat LSB3P (flip uniRunSat st)
      describe "lsb3_t" $
        shouldSatExtra satTFormulas (uniRunSat LSB3T st)
    describe "funkcja sat nie powinna spelniac" $ do
      describe "lsb3_p" $
        shouldNotSat LSB3P (flip uniRunSat st)
      describe "lsb3_t" $
        shouldNotSat LSB3T (flip uniRunSat st)
    describe "funkcja sat (taut) powinna spelniac" $ do
      describe "lsb3_p" $
        shouldSatTaut (tautFormulas ++ tautPFormulas) (uniRunTaut LSB3P st)
      describe "lsb3_t" $
        shouldSatTaut (tautFormulas ++ tautTFormulas) (uniRunTaut LSB3T st)
    describe "funkcja sat (taut) nie powinna spelniac" $ do
      describe "lsb3_p" $
        shouldSatNoTaut tautTFormulas (uniRunTaut LSB3P st)
      describe "lsb3_t" $
        shouldSatNoTaut tautPFormulas (uniRunTaut LSB3T st)


propertySpec :: Testable prop => String
             -> (LogicType -> prop)
             -> (LogicType -> prop)
             -> Spec
propertySpec info satp tautp =
  describe ("dla dowolnej formuly" ++ info) $ do
    describe "sat" $
      it "naiwny i heurystyczny znajduja rozwiazanie dla tego samego przypadku: LSB3P" $
        mapSize (const 12) . property $ satp LSB3P
    describe "taut" $
      it "naiwny i heurystyczny znajduja rozwiazanie dla tego samego przypadku: LSB3P" $
        mapSize (const 12) . property $ tautp LSB3P

spec :: Spec
spec = do
  solverSpec Naive
  solverSpec DPLL
  propertySpec " w postaci normalnej" prop_naive_dpll_sat prop_naive_dpll_taut
  propertySpec "" prop_all_naive_dpll_sat prop_all_naive_dpll_taut
  describe "dla dowolnej formuly" $
    it "jezeli solver sat znajdzie rozwiazanie, to jest ono poprawne" $
      mapSize (const 12) . property $ prop_lsb3t_sat

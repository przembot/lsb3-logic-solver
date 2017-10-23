module Thesis where

import Data.HashMap.Strict as HM
import Data.Set as S
import Data.List.Split (chunksOf)
import Data.List (find)

type VarMap = HashMap Char TriVal
type VarMapBool = HashMap Char Bool

data Variables = Variables {
    outsideLogic :: VarMapBool
  , insideLogic :: VarMap
  }

boolToTri :: Bool -> TriVal
boolToTri True = TrueV
boolToTri False = FalseV

data TriVal =
    TrueV
  | Neither
  | FalseV
  deriving (Show, Eq)


class TriValValue a where
  true, false, neither :: a
  foldTriVal :: a -> a -> a -> a -> a


instance TriValValue TriVal where
  true = TrueV
  neither = Neither
  false = FalseV
  foldTriVal x e1 e2 e3 =
    case x of
      TrueV -> e1
      Neither -> e2
      _ -> e3

data BinaryOp =
    And
  | Or
  | Implication
  | Equal
  deriving (Show, Eq)


data Logic =
    Const TriVal
  | Var Char
  | Not Logic
  | BinForm BinaryOp Logic Logic
  | Cp Logic
  | Ct Logic
  deriving (Show, Eq)


-- | Sprawdza m. in. czy nie ma zagniezdzonego Ci w sobie
verifyTree :: Logic -> Bool
verifyTree = const True

-- | Podstawia wszystkie zmienne wystepujace w formule.
-- Jesli nie istenieje dane podstawienie - zwracane jest Nothing
mapVars :: (Char -> Maybe TriVal) -- ^ wartosciowanie v()
        -> (Char -> Maybe TriVal) -- ^ wartosciowanie v(Ci())
        -> Logic -> Maybe Logic
mapVars f _ (Var c) = Const <$> f c
mapVars _ _ a@(Const _) = Just a
mapVars f fc (Not l) = Not <$> mapVars f fc l
mapVars f fc (BinForm op l r) =
  BinForm op <$> (mapVars f fc l) <*> (mapVars f fc r)
mapVars _ fc (Cp l) = Cp <$> mapVars fc fc l
mapVars _ fc (Ct l) = Ct <$> mapVars fc fc l

{-
foldLogicM :: (TriVal -> Logic)
           -> (Char -> Logic)
           -> Logic
           -> Logic
           -}

substitute :: Variables -> Logic -> Maybe Logic
substitute (Variables o i) =
  mapVars (\a -> HM.lookup a (fmap boolToTri o))
          (\a -> HM.lookup a i)

notI, notO :: TriVal -> TriVal
notI TrueV = FalseV
notI Neither = Neither
notI FalseV = TrueV

notO TrueV = FalseV
notO FalseV = TrueV
notO _ = TrueV

andP, andT, andO :: TriVal -> TriVal -> TriVal
andP TrueV TrueV = TrueV
andP FalseV _ = FalseV
andP _ FalseV = FalseV
andP _ _ = Neither

andT TrueV TrueV = TrueV
andT TrueV Neither = Neither
andT Neither TrueV  = Neither
andT _ _ = FalseV

andO TrueV TrueV = TrueV
andO _ _ = FalseV

orP, orT, orO :: TriVal -> TriVal -> TriVal
orP TrueV _ = TrueV
orP _ TrueV = TrueV
orP FalseV FalseV = FalseV
orP _ _ = Neither

orT FalseV FalseV = FalseV
orT FalseV Neither = Neither
orT Neither FalseV = Neither
orT _ _ = TrueV

orO TrueV _ = TrueV
orO _ TrueV = TrueV
orO _ _ = FalseV

implP, implT, implO :: TriVal -> TriVal -> TriVal
implP a b = orP (notI a) b
implT a b = orT (notI a) b
implO a b = orO (notO a) b

eqP, eqT, eqO :: TriVal -> TriVal -> TriVal
eqP a b = andP (implP a b) (implP b a)
eqT a b = andT (implT a b) (implT b a)
eqO a b = andO (implO a b) (implO b a)

evalCp, evalCt :: Logic -> Maybe TriVal
evalCp (Const a) = Just a
evalCp (Var _) = Nothing
evalCp (Not l) = notI <$> evalCp l
evalCp (BinForm And l r) = andP <$> evalCp l <*> evalCp r
evalCp (BinForm Or l r) = orP <$> evalCp l <*> evalCp r
evalCp (BinForm Implication l r) = implP <$> evalCp l <*> evalCp r
evalCp (BinForm Equal l r) = eqP <$> evalCp l <*> evalCp r
evalCp _ = Nothing -- zagniezdzenie Ci jest zabronione

evalCt (Const a) = Just a
evalCt (Var _) = Nothing
evalCt (Not l) = notI <$> evalCt l
evalCt (BinForm And l r) = andT <$> evalCt l <*> evalCt r
evalCt (BinForm Or l r) = orT <$> evalCt l <*> evalCt r
evalCt (BinForm Implication l r) = implT <$> evalCt l <*> evalCt r
evalCt (BinForm Equal l r) = eqT <$> evalCt l <*> evalCt r
evalCt _ = Nothing -- zagniezdzenie Ci jest zabronione


evalLogic :: Logic -> Maybe TriVal
evalLogic (Const a) = Just a
evalLogic (Var _) = Nothing
evalLogic (Not l) = notO <$> evalLogic l
evalLogic (BinForm And l r) = andO <$> evalLogic l <*> evalLogic r
evalLogic (BinForm Or l r) = orO <$> evalLogic l <*> evalLogic r
evalLogic (BinForm Implication l r) = implO <$> evalLogic l <*> evalLogic r
evalLogic (BinForm Equal l r) = eqO <$> evalLogic l <*> evalLogic r
evalLogic (Cp l) = evalCp l
evalLogic (Ct l) = evalCt l


sample, sample2 :: Logic
sample = Cp $ BinForm Or (Const FalseV) $ BinForm And (Const Neither) (Const Neither)
sample2 = BinForm And (Var 'q') $ Cp $ BinForm Or (Var 'p') $ BinForm And (Const Neither) (Const Neither)


type FreeVars = (Set Char, Set Char)

sumVars :: FreeVars
        -> FreeVars
        -> FreeVars
sumVars (a, b) (c, d) = (S.union a c, S.union b d)

-- | Znajduje wszystkie uzywane zmienne v() i v(Ci())
findVars :: Logic -> FreeVars
findVars = go False (S.empty, S.empty)
  where
    go :: Bool -> FreeVars -> Logic -> FreeVars
    go _ vars (Const _) = vars
    go b (p, q) (Var v) = if b then (p, S.insert v q) else (S.insert v p, q)
    go b vars (Not l) = go b vars l
    go b vars (BinForm _ l r) = sumVars (go b vars l) (go b vars r)
    go _ vars (Cp l) = go True vars l
    go _ vars (Ct l) = go True vars l


type InvalidVals = ([(Char, Bool)], [(Char, TriVal)])

isNotTrue :: Logic -> Variables -> Maybe Bool
isNotTrue logic vars = (/= TrueV) <$> ((substitute vars logic) >>= evalLogic)

allVars :: FreeVars -> [Variables]
allVars (a, b) = Variables <$> al <*> bl
  where
    al = HM.fromList <$> chunksOf (S.size a)
      ((,) <$> S.toList a <*> [False, True])

    bl = HM.fromList <$> chunksOf (S.size b)
      ((,) <$> S.toList b <*> [FalseV, Neither, TrueV])


-- | Czy podana formula jest tautologia
-- Left w przypadku niepoprawnej formuly
verifyNaive :: Logic -> Either InvalidVals ()
verifyNaive for =
  case (find (\(b, _) -> b == Just True) . fmap (\a -> (isNotTrue for a, a)) . allVars . findVars) for of
    (Just (_, (Variables o i))) -> Left (HM.toList o, HM.toList i)
    _ -> Right ()

main :: IO ()
main = do
  putStrLn "hello world"

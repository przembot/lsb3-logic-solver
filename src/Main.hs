module Main where

import Data.HashMap.Strict as HM

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

data BaseLogic =
    ConstI TriVal
  | VarI Char
  | NotI BaseLogic
  | BinFormI BinaryOp BaseLogic BaseLogic
  deriving (Show, Eq)

data Logic =
    Const TriVal
  | Var Char
  | Not Logic
  | BinForm BinaryOp Logic Logic
  | Cp BaseLogic
  | Ct BaseLogic
  deriving (Show, Eq)


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
mapVars _ fc (Cp l) = Cp <$> mapVarsC fc l
mapVars _ fc (Ct l) = Ct <$> mapVarsC fc l


mapVarsC :: (Char -> Maybe TriVal) -> BaseLogic -> Maybe BaseLogic
mapVarsC _ a@(ConstI _) = Just a
mapVarsC f (VarI c) = ConstI <$> f c
mapVarsC f (NotI l) = NotI <$> mapVarsC f l
mapVarsC f (BinFormI op l r) = BinFormI op <$> mapVarsC f l <*> mapVarsC f r

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

notI :: TriVal -> TriVal
notI TrueV = FalseV
notI Neither = Neither
notI FalseV = TrueV

andP :: TriVal -> TriVal -> TriVal
andP TrueV TrueV = TrueV
andP FalseV _ = FalseV
andP _ FalseV = FalseV
andP _ _ = Neither

orP :: TriVal -> TriVal -> TriVal
orP TrueV _ = TrueV
orP _ TrueV = TrueV
orP FalseV FalseV = FalseV
orP _ _ = Neither

implP :: TriVal -> TriVal -> TriVal
implP a b = orP (notI a) b

eqP :: TriVal -> TriVal -> TriVal
eqP a b = andP (implP a b) (implP b a)

evalCp, evalCt :: BaseLogic -> Maybe TriVal
evalCp (ConstI a) = Just a
evalCp (VarI _) = Nothing
evalCp (NotI l) = notI <$> evalCp l
evalCp (BinFormI And l r) = andP <$> evalCp l <*> evalCp r
evalCp (BinFormI Or l r) = orP <$> evalCp l <*> evalCp r
evalCp (BinFormI Implication l r) = implP <$> evalCp l <*> evalCp r
evalCp (BinFormI Equal l r) = eqP <$> evalCp l <*> evalCp r
evalCt = undefined

evalLogic :: Logic -> Maybe TriVal
evalLogic (Const a) = Just a
evalLogic (Var _) = Nothing
evalLogic (Cp l) = evalCp l
evalLogic (Ct l) = evalCt l

main :: IO ()
main = do
  putStrLn "hello world"

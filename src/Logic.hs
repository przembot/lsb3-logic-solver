{-|
   Ponizszy modul przedstawia reprezentacje formuly
   logicznej logiki LSB3 wraz z pomocniczymi funkcjami
   do manipulacji nad formula.
-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Logic (
    TriVal (..)
  , BinaryOp (..)
  , Logic (..)
  , LogicType (..)
  , notO
  , notI
  , applyLogic
  , evalLogic
  , findUnassignedVar
  , substitudeNaiveVar
  , generateBigSample
  ) where

import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)

import Data.Char (isLower)
import Control.Applicative ((<|>))


-- | Wartosci wystepujace w logike LSB3
data TriVal =
    TrueV -- ^ oznaczenie 1
  | Neither -- ^ oznaczenie 1/2
  | FalseV -- ^ oznaczenie 0
  deriving (Eq, Generic, NFData)


-- | Mozliwe warianty logiki
data LogicType = LSB3T
               | LSB3P
               deriving Eq


instance Show TriVal where
  show TrueV = "1"
  show Neither = "1/2"
  show FalseV = "0"

-- | Operacje dwuargumentowe na logice
data BinaryOp =
    And
  | Or
  | Impl
  | Equiv
  deriving Eq

instance Show BinaryOp where
  show And = "*"
  show Or = "+"
  show Impl = "->"
  show Equiv = "<->"

-- | Funkcja wyliczajaca negacje zewnetrzna
notO :: TriVal -> TriVal
notO TrueV = FalseV
notO _ = TrueV

-- | Funkcja wyliczajaca negacje wewnatrz funktora przekonaniowego
notI :: TriVal -> TriVal
notI TrueV = FalseV
notI FalseV = TrueV
notI x = x


-- | Reprezentacja wyrazenia
data Logic =
    Const TriVal
  | Var Char
  | Not Logic
  | BinForm BinaryOp Logic Logic
  | C Logic
  deriving Eq

instance Show Logic where
  show (Const val) = show val
  show (Var c) = [c]
  show (Not x) = "~" ++ show x
  show (BinForm op p q) = unwords ["(", show p, show op, show q, ")"]
  show (C x) = unwords ["C(", show x, ")"]

instance Arbitrary TriVal where
  arbitrary = elements [TrueV, Neither, FalseV]

instance Arbitrary BinaryOp where
  arbitrary = elements [And, Or, Impl, Equiv]

instance Arbitrary Logic where
  arbitrary = sized genLogic


genLogic :: Int -> Gen Logic
genLogic = logic' . (`div` 2)


-- | Generator logiki LSB3
logic' :: Int -> Gen Logic
logic' 0 = C <$> sampleLogic' 0
logic' n = oneof [ Not <$> logic' (n-1), C <$> sampleLogic' n
                 , BinForm <$> elements [Or, And] <*> subtree <*> subtree ]
                     where
                       subtree = logic' (n `div` 2)


-- | Generator logiki pozbawionej funktora C
sampleLogic' :: Int -> Gen Logic
sampleLogic' 0 = oneof [ Var <$> suchThat arbitrary isLower
                       , Not . Var <$> suchThat arbitrary isLower]
sampleLogic' n = oneof [ Not <$> sampleLogic' (n-1)
                       , BinForm <$> elements [Or, And] <*> subtree <*> subtree ]
                           where
                             subtree = sampleLogic' (n `div` 2)


-- | Generuje losowa formule logiczna
-- skladajaca sie z co najwyzej 32 zmiennych zdaniowych
generateBigSample :: IO Logic
generateBigSample = generate . resize 32 $ arbitrary

-- | Znajduje zmienna zdaniowa w formule
findUnassignedVar :: Logic -> Maybe Char
findUnassignedVar (Var x) = Just x
findUnassignedVar (Const _) = Nothing
findUnassignedVar (Not x) = findUnassignedVar x
findUnassignedVar (BinForm _ x y) = findUnassignedVar x <|> findUnassignedVar y
findUnassignedVar (C x) = findUnassignedVar x

-- | Podstawia wartosc za dana zmienna w formule
substitudeNaiveVar :: Char -> TriVal -> Logic -> Logic
substitudeNaiveVar var val (Var x) =
  if x == var then Const val
              else Var x
substitudeNaiveVar var val expr = applyLogic (substitudeNaiveVar var val) expr


-- | Wprowadz dane przeksztalcenie w calej formule
applyLogic :: (Logic -> Logic) -- ^ funkcja realizujaca przeksztalcenie
           -> Logic -> Logic
applyLogic f (BinForm op a b) = BinForm op (f a) (f b)
applyLogic f (C x) = C (f x)
applyLogic f (Not x) = Not (f x)
applyLogic _ x = x

-- | Oblicza wartosc formuly logicznej.
-- Jezeli formula nie da sie wyliczyc (np. jest w niej nieprzypisana zmienna)
-- to zwracane jest Nothing.
evalLogic :: LogicType -> Logic -> Maybe TriVal
evalLogic _ (Const x) = Just x
evalLogic _ (Var _) = Nothing
evalLogic lt (Not x) = notO <$> evalLogic lt x
evalLogic lt (BinForm op x y) = evalOp op <$> evalLogic lt x <*> evalLogic lt y
evalLogic lt (C x) = evalLogicI lt x

-- | Oblicze wartosc formuly logicznej
-- bedacej w funktorze przekonaniowym
evalLogicI :: LogicType -> Logic -> Maybe TriVal
evalLogicI _ (Const x) = Just x
evalLogicI _ (Var _) = Nothing
evalLogicI lt (Not x) = notI <$> evalLogicI lt x
evalLogicI lt (BinForm op x y) = evalOpI lt op <$> evalLogicI lt x <*> evalLogicI lt y
evalLogicI lt (C x) = evalLogicI lt x


-- | Obliczenie wartosci formuly dla spojnikow druargumentowych
-- logiki zewnetrznej
evalOp :: BinaryOp -> TriVal -> TriVal -> TriVal
evalOp Or TrueV _ = TrueV
evalOp Or _ TrueV = TrueV
evalOp Or _ _ = FalseV
evalOp And TrueV TrueV = TrueV
evalOp And _ _ = FalseV
evalOp Impl a b = evalOp Or (notO a) b
evalOp Equiv a b = evalOp And (evalOp Impl a b) (evalOp Impl b a)

-- | Obliczenie wartosci formuly dla spojnikow druargumentowych
-- | logiki wewnetrznej
evalOpI :: LogicType -> BinaryOp -> TriVal -> TriVal -> TriVal
evalOpI LSB3T = evalOpIT
evalOpI LSB3P = evalOpIP

evalOpIT, evalOpIP :: BinaryOp -> TriVal -> TriVal -> TriVal
evalOpIP Or TrueV _ = TrueV
evalOpIP Or _ TrueV = TrueV
evalOpIP Or FalseV FalseV = FalseV
evalOpIP Or _ _ = Neither
evalOpIP And TrueV TrueV = TrueV
evalOpIP And FalseV _ = FalseV
evalOpIP And _ FalseV = FalseV
evalOpIP And _ _ = Neither
evalOpIP Impl a b = evalOpIP Or (notI a) b
evalOpIP Equiv a b = evalOpIP And (evalOpIP Impl a b) (evalOpIP Impl b a)

evalOpIT Or FalseV x = x
evalOpIT Or x FalseV = x
evalOpIT Or _ _ = TrueV
evalOpIT And TrueV x = x
evalOpIT And x TrueV = x
evalOpIT And _ _ = FalseV
evalOpIT Impl a b = evalOpIT Or (notI a) b
evalOpIT Equiv a b = evalOpIT And (evalOpIT Impl a b) (evalOpIT Impl b a)

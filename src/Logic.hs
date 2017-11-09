{-
   Implementacja logiki LSB3
-}
module Logic (
    TriVal (..)
  , BinaryOp (..)
  , Logic (..)
  , notO
  , notI
  ) where

import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen

import Data.Char (isLower)


-- | Wartosci wystepujace w logike LSB3
data TriVal =
    TrueV
  | Neither
  | FalseV
  deriving Eq

instance Show TriVal where
  show TrueV = "T"
  show Neither = "N"
  show FalseV = "F"

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

-- notO - negacja zewnetrzna
-- notI - negacja wewnetrzna
notO, notI :: TriVal -> TriVal
notO TrueV = FalseV
notO _ = TrueV
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
  arbitrary = sized logic'


-- | Generator logiki LSB3
logic' :: Int -> Gen Logic
logic' 0 = C <$> sampleLogic' 0
logic' n = oneof [ Not <$> subtree, C <$> sampleLogic' n,
                   BinForm <$> arbitrary <*> subtree <*> subtree ]
                     where
                       subtree = logic' (n `div` 2)


-- | Generator logiki pozbawionej funktora C
sampleLogic' :: Int -> Gen Logic
sampleLogic' 0 = oneof [ Var <$> suchThat arbitrary isLower]
sampleLogic' n = oneof [ Not <$> subtree, BinForm <$> arbitrary <*> subtree <*> subtree ]
                           where
                             subtree = sampleLogic' (n `div` 2)


generateBigSample :: IO Logic
generateBigSample = generate . resize 200 $ arbitrary

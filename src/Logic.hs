{-
   Implementacja logiki LSB3
-}
module Logic where

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
  arbitrary = oneof
    [ Const <$> arbitrary
    , Var <$> (suchThat arbitrary isLower)
    , Not <$> arbitrary
    , BinForm <$> arbitrary <*> arbitrary <*> arbitrary
    , C <$> sampleLogic
    ]
  shrink (BinForm _ x y) = [x, y]
  shrink (Not x) = [x]
  shrink (C x) = [x]
  shrink _ = []


sampleLogic = oneof
    [ Const <$> arbitrary
    , Var <$> (suchThat arbitrary isLower)
    , Not <$> sampleLogic
    , BinForm <$> arbitrary <*> sampleLogic <*> sampleLogic
    ]

sample, sample2 :: Logic
sample = C $ BinForm Or (Const FalseV) $ BinForm And (Const Neither) (Const Neither)
sample2 = BinForm And (C $ Var 'q') $ C $ BinForm Or (Var 'p') $ BinForm And (Const Neither) (Const Neither)

-- (czy nie zawiera zaglebionego funktora C)
isValid :: Logic -> Bool
isValid = const True


-- notO - negacja zewnetrzna
-- notI - negacja wewnetrzna
notO, notI :: TriVal -> TriVal
notO TrueV = FalseV
notO _ = TrueV
notI TrueV = FalseV
notI FalseV = TrueV
notI x = x

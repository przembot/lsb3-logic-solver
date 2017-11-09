{-# LANGUAGE OverloadedStrings #-}
module ParserSpec (spec) where

import Test.Hspec
import Test.QuickCheck
import Data.Text (pack)
import Data.Either (isRight)

import Logic
import Parser

prop_parse_show :: Logic -> Bool
prop_parse_show expr = (parseLogic . pack . filter (/= ' ') . show) expr == Right expr

impl = BinForm Impl
equiv = BinForm Equiv

spec :: Spec
spec = do
  describe "property:" $
    it "parse . show == id" $
      property prop_parse_show
  describe "unit:" $ do
    it "C(C(a)) should fail" $
      isRight (parseLogic "C(C(a))") `shouldBe` False
    it "operators are left associative" $
      parseLogic "a -> b -> c" `shouldBe` Right (impl (impl (Var 'a') (Var 'b')) (Var 'c'))
    it "double negation is parsed properly" $
      parseLogic "C(~~a <-> a)" `shouldBe` Right (C (equiv (Not (Not (Var 'a'))) (Var 'a')))

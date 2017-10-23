module NaiveSpec (spec) where

import Test.Hspec

import Thesis

sample3 :: Logic
sample3 = Ct $ BinForm Implication (Var 'q') (BinForm Implication (Var 'p') (Var 'q'))

mponens, mponenst, mponensp :: Logic
mponens = BinForm Implication (BinForm And (BinForm Implication (Var 'p') (Var 'q')) (Var 'p')) (Var 'q')
mponenst = Ct mponens
mponensp = Cp mponens

przt, przp :: Logic
przemiennosc :: BinaryOp -> Logic
przemiennosc op = BinForm Equal (BinForm op (BinForm op (Var 'p') (Var 'q')) (Var 'r'))
                                (BinForm op (Var 'p') (BinForm op (Var 'q') (Var 'r')))
przt = Ct $ przemiennosc And
przp = Ct $ przemiennosc And


dm1, dm2 :: Logic
dm1 = BinForm Equal
      (BinForm Or (Var 'p') (Var 'q'))
      (Not (BinForm And (Not (Var 'p')) (Not (Var 'q'))))
dm2 = BinForm Equal
      (BinForm And (Var 'p') (Var 'q'))
      (Not (BinForm Or (Not (Var 'p')) (Not (Var 'q'))))

spec :: Spec
spec = do
  describe "basic verification" $ do
    it "sample3" $ do
      verifyNaive sample3 `shouldBe` Right ()
    it "mponenst" $ do
      verifyNaive mponenst `shouldBe` Right ()
    it "mponensp" $ do
      verifyNaive mponensp `shouldBe` Right ()
    it "przt" $ do
      verifyNaive przt `shouldBe` Right ()
    it "przp" $ do
      verifyNaive przp `shouldBe` Right ()
    it "de morgan 1" $ do
      verifyNaive dm1 `shouldBe` Right ()
    it "de morgan 2" $ do
      verifyNaive dm2 `shouldBe` Right ()
    it "de morgan Ct 1" $ do
      verifyNaive (Ct dm1) `shouldBe` Right ()
    it "de morgan Ct 2" $ do
      verifyNaive (Ct dm2) `shouldBe` Right ()
    it "de morgan Cp 1" $ do
      verifyNaive (Cp dm1) `shouldBe` Right ()
    it "de morgan Cp 2" $ do
      verifyNaive (Cp dm2) `shouldBe` Right ()

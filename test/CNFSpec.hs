module CNFSpec (spec) where

import Test.Hspec
import Test.QuickCheck
import Data.Maybe (isJust)

import Lib

prop_all :: Logic -> Bool
prop_all = isJust . convertToCnf


spec :: Spec
spec =
  describe "CNF conversion" $
    it "all valid logic expression should be converted to CNF" $
      within 2000000 . mapSize (const 10) $ property prop_all

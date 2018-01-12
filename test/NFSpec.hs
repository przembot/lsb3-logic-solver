module NFSpec (spec) where

import Test.Hspec
import Test.QuickCheck
import Data.Maybe (isJust)

import Lib

prop_all :: Logic -> Bool
prop_all = isJust . convertToNf


spec :: Spec
spec =
  describe "NF conversion" $
    it "all valid logic expression should be converted to NF" $
      within 3000000 . mapSize (const 10) $ property prop_all

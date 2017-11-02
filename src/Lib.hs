{-# LANGUAGE OverloadedStrings #-}
module Lib (
    module Logic
  , module CNF
  , module SAT
  , module Parser
  ) where

import Data.Text (Text)

import Logic
import Parser
import CNF
import SAT


sampleP :: Text
sampleP = "C(a * b + ~c) -> C(x)"

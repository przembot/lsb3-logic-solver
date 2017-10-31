module Main where

import Lib
import Graphics.QML
import Data.Text (Text)
import qualified Data.Text as T


main :: IO ()
main = do
  clazz <- newClass []
  ctx <- newObject clazz ()
  let doc = "qml/main.qml"
  runEngineLoop defaultEngineConfig {
    initialDocument = fileDocument doc,
    contextObject = Just $ anyObjRef ctx}

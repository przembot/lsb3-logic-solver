{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
module Main where

import Graphics.QML
import Control.Concurrent
import Control.Exception
import Data.IORef
import Data.Text (Text)
import qualified Data.Text as T

import Data.Either (either)

import Lib

-- | Lewa strona - rezultat dla LSB3_T
-- | prawa strona - rezultat dla LSB3_P
newtype LSBSatResult = LSBSatResult (SatResult, SatResult)
newtype LSBTautResult = LSBTautResult (TautResult, TautResult)

tShow :: Show a => a -> Text
tShow = T.pack . show

uniHandler ft fp wrap expr =
  let
    parsedexpr = either (Left . ParseFailure) Right . parseLogic $ expr
  in wrap (parsedexpr >>= ft, parsedexpr >>= fp)

uniRaport fr rest resp =
  T.concat ["Logika LSB3_T:\n", fr rest,
            "Logika LSB3_P:\n", fr resp]

satHandler :: Text -> LSBSatResult
satHandler = uniHandler (uniRunSat DPLL LSB3T) (uniRunSat DPLL LSB3P) LSBSatResult

tautHandler :: Text -> LSBTautResult
tautHandler = uniHandler (uniRunTaut DPLL LSB3T) (uniRunTaut DPLL LSB3P) LSBTautResult

satRaport :: LSBSatResult -> Text
satRaport (LSBSatResult (rest, resp)) = uniRaport satSingleReport rest resp

tautRaport :: LSBTautResult -> Text
tautRaport (LSBTautResult (rest, resp)) = uniRaport tautSingleReport rest resp

satSingleReport :: SatResult -> Text
satSingleReport (Left e) = T.concat ["Nastąpił błąd:\n", tShow e, "\n\n"]
satSingleReport (Right x) =
  T.append "Udane podstawienie:\n"
  (T.concat . map (\(var, val) -> T.concat [tShow var, ": ", tShow val, "\n"]) $ x)


tautSingleReport :: TautResult -> Text
tautSingleReport (Left (TautologyFail x)) =
  T.append "Formuła nie jest tautologią w badanej logice, dowód:\n"
  (T.concat . map (\(var, val) -> T.concat [tShow var, ": ", tShow val, "\n"]) $ x)
tautSingleReport (Left e) = T.concat ["Nastąpił błąd:\n", tShow e, "\n\n"]
tautSingleReport _ = "Podana formuła jest tautologią w badanej logice.\n"


runMethod resulttext sigkey raport handler obj txt = do
  writeIORef resulttext "Obliczam.."
  fireSignal sigkey obj
  _ <- forkIO $ do
    let out = raport . handler $ txt
    _ <- evaluate out
    writeIORef resulttext out
    fireSignal sigkey obj
  return ()


initMessage :: Text
initMessage = T.intercalate "\n"
            [ "Wyniki obliczeń pojawią się tutaj.."
            , "Użyj małych liter do oznaczenia zmiennych"
            , "Wynik czasami może nie zawierać wszystkich zmiennych opisanych wartościami,"
            , "co znaczy, że niewymienione zmienne mogą mieć dowolną wartość."
            ]


main :: IO ()
main = do
  resulttext <- newIORef initMessage
  sigkey <- newSignalKey
  clazz <- newClass [
      -- aktualizowanie wartosci pola tekstowego
      defPropertySigRO' "result" sigkey (\_ -> readIORef resulttext),
      defMethod' "runsat" (runMethod resulttext sigkey satRaport satHandler),
      defMethod' "runtaut" (runMethod resulttext sigkey tautRaport tautHandler)
    ]
  ctx <- newObject clazz ()
  let doc = "qml/main.qml"
  runEngineLoop defaultEngineConfig {
    initialDocument = fileDocument doc,
    contextObject = Just $ anyObjRef ctx}

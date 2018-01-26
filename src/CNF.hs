{-|
   Modul zawierajacy reprezentacje koniunkcyjnej postaci normalnej
   wraz z funkcjami do manipulacji na niej
   (m. in. modyfikacja wszystkich atomow).
   Ponadto, znajduja sie tutaj funkcji dokonujace konwersji
   formuly logicznej do koniunkcyjnej postaci normalnej.
-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module CNF (
    convertToCnf
  , unNegable
  , stripAtoms
  , filterVars
  , modifyAllAtoms
  , modifyAllVars
  , cnfToLogic
  , CNF
  , Clause
  , Elem
  , Negable (..)
  , Atom (..)
  ) where

import Control.Applicative (liftA2)
import Data.Maybe (mapMaybe)
import Data.List (foldl1')
import Logic

-- | Zamienia wynikanie i ekwiwalencje na sumy i iloczyny
replaceImpl :: Logic -> Logic
replaceImpl (BinForm Impl x y) =
  BinForm Or (Not (replaceImpl x)) (replaceImpl y)
replaceImpl (BinForm Equiv x y) =
  BinForm And
    (BinForm Or (Not (replaceImpl x)) (replaceImpl y))
    (BinForm Or (Not (replaceImpl y)) (replaceImpl x))
replaceImpl x = applyLogic replaceImpl x


stripLits :: Logic -> [Logic]
stripLits (BinForm And x y) = stripLits x ++ stripLits y
stripLits x = [x]


-- | Przeksztalca wyrazenie bez -> i <-> wyrazenia w postaci normalnej.
-- Wykorzystywane do uproszczenia wyrazenia pod funktorem przekonaniowym.
convertC :: Logic -> Logic
convertC (Not (Not x)) = convertC x
-- wartosc stala
convertC (Not (Const x)) = Const (notI x)
-- De Morgan
convertC (Not (BinForm And x y)) = convertC $ BinForm Or (Not x) (Not y)
convertC (Not (BinForm Or x y)) = convertC $ BinForm And (Not x) (Not y)
convertC (BinForm Or x y) =
  foldl1' (BinForm And) $
    BinForm Or <$> stripLits (convertC x) <*> stripLits (convertC y)
convertC (BinForm And x y) = BinForm And (convertC x) (convertC y)
convertC x = x


-- | Przeksztalca wyrazenie bez -> i <-> do postaci normalnej.
-- Zaklada, ze funktor przechowuje tylko i wylacznie jedna zmienna
-- z opcjonalna negacja.
-- Wykorzystywane do uproszczenia wyrazenia pod funktorem przekonaniowym.
convert :: Logic -> Maybe CNF
convert (C (Var x)) = Just [[Pure (Pure (VarE x))]]
convert (C (Not (Var x))) = Just [[Pure (NotE (VarE x))]]
convert (Not (C (Var x))) = Just [[NotE (Pure (VarE x))]]
convert (Not (C (Not (Var x)))) = Just [[NotE (NotE (VarE x))]]
-- wartosc stala
convert (C (Const x)) = Just [[Pure (Pure (Lit x))]]
convert (C (Not (Const x))) = Just [[Pure (NotE (Lit x))]]
convert (Not (C (Const x))) = Just [[NotE (Pure (Lit x))]]
convert (Not (C (Not (Const x)))) = Just [[NotE (NotE (Lit x))]]
convert (Not (Not x)) = convert x
-- De Morgan
convert (Not (BinForm And x y)) = convert $ BinForm Or (Not x) (Not y)
convert (Not (BinForm Or x y)) = convert $ BinForm And (Not x) (Not y)
convert (BinForm Or x y) =
  liftA2 (++) <$> convert x <*> convert y
convert (BinForm And x y) = (++) <$> convert x <*> convert y
convert _ = Nothing -- przy poprawnym wyrazeniu nie powinno tutaj dojsc


-- | Konweruje do koniunkcyjnej postaci normalnej
-- wszystko znajdujace sie pod funktorem przekonaniowym
-- oraz wydziela z funktora pojedyczne zmienne.
simplifyFunctors :: Logic -> Logic
simplifyFunctors (C x) = fixc . C . convertC $ x
simplifyFunctors (Not (C x)) = Not . fixc . C . convertC $ x
simplifyFunctors x = applyLogic simplifyFunctors x


-- | Przestawia funktor C na zewnatrz jezeli to mozliwe
fixc :: Logic -> Logic
fixc (C (BinForm And x y)) = BinForm And (fixc . C $ x) (fixc . C $ y)
fixc (C (BinForm Or x y)) = BinForm Or (fixc . C $ x) (fixc . C $ y)
fixc x = x


-- | Konwertuje wyrazenie do postaci CNF.
-- Nie ma zmiennych poza funktorem C() - inaczej zwroci Nothing
convertToCnf :: Logic -> Maybe CNF
convertToCnf = convert . simplifyFunctors . replaceImpl


-- | Koniunkcyjna postac normalna sklada sie
-- z listy klauzul
type CNF = [Clause]

-- | Klauzula stanowi liste elementow
type Clause = [Elem]

-- | Element klauzuli stanowi atom, ktory moze
-- miec negacje przed funktorem jak i wewnatrz
-- funktora przekonaniowego
type Elem = Negable (Negable Atom)


-- | Usuwa oznaczenie okreslajace polarnosc
-- sprzed dowolnego typu.
unNegable :: Negable x -> x
unNegable (Pure x) = x
unNegable (NotE x) = x

-- | Datatype oznaczajacy, ze cos moze byc zanegowane.
data Negable x =
    Pure x -- ^ dana x nie jest zanegowana
  | NotE x -- ^ dana x jest zanegowana
  deriving (Show, Eq, Functor, Foldable, Traversable)

-- | Pojedynczy atom wystepujacy w wyrazeniu CNF,
-- ktorym jest albo wartosc stala, albo zmienna zdaniowa.
data Atom =
    Lit TriVal
  | VarE Char
  deriving (Show, Eq)

-- | Zwraca liste wszystkich atomow, ktore wystepuja
-- w danej formule bedacej w postaci normalnej
stripAtoms :: CNF -> [Atom]
stripAtoms = map (unNegable . unNegable) . concat

getCharFromAtom :: Atom -> Maybe Char
getCharFromAtom (VarE x) = Just x
getCharFromAtom _ = Nothing

-- | Zwraca wszystkie zmienne zdaniowe wystepujace w lisce atomow
filterVars :: [Atom] -> String
filterVars = mapMaybe getCharFromAtom

-- | Modyfikuje wszystkie atomy w formule bedacej w postaci
-- normalnej wykorzystujac funkcje bedaca pierwszym
-- argumentem.
modifyAllAtoms :: (Atom -> Atom) -> CNF -> CNF
modifyAllAtoms = fmap . fmap . fmap . fmap

-- | Modyfikuje wszystkie zmienne zdaniowe w formule bedacej w postaci
-- normalnej wykorzystujac funkcje bedaca pierwszym
-- argumentem.
modifyAllVars :: (Char -> Atom) -> CNF -> CNF
modifyAllVars f = modifyAllAtoms
                    (\case
                      VarE x -> f x
                      a -> a
                    )

-- | Konwertuje formule ze struktury danych
-- reprezentujacej postac normalna
-- do struktury danych reprezentujacej
-- dowolne wyrazenie logiczne
cnfToLogic :: CNF -> Logic
cnfToLogic = foldl1' (BinForm And)
           . map clauseToLogic
    where
      clauseToLogic = foldl1' (BinForm Or)
                    . map funcToLogic
      funcToLogic (Pure l) = C (natomToLogic l)
      funcToLogic (NotE l) = Not $ C (natomToLogic l)
      natomToLogic (Pure x) = atomToLogic x
      natomToLogic (NotE x) = Not $ atomToLogic x
      atomToLogic (Lit x) = Const x
      atomToLogic (VarE x) = Var x

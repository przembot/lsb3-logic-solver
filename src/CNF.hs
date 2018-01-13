{-
   Modul zawierajacy opis i konwersje do NF
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
-- | Wykorzystywane do uproszczenia wyrazenia pod funktorem przekonaniowym.
convert :: (TriVal -> TriVal) -> Logic -> Logic
convert f (Not (Not x)) = convert f x
-- wartosc stala
convert f (Not (Const x)) = Const (f x)
-- De Morgan
convert f (Not (BinForm And x y)) = convert f $ BinForm Or (Not x) (Not y)
convert f (Not (BinForm Or x y)) = convert f $ BinForm And (Not x) (Not y)
convert f (BinForm Or x y) =
  foldl1' (BinForm And) $
    BinForm Or <$> stripLits (convert f x) <*> stripLits (convert f y)
convert f (BinForm And x y) = BinForm And (convert f x) (convert f y)
convert _ x = x


-- | Przeksztalca wyrazenie bez -> i <-> do postaci normalnej.
-- | Zaklada, ze funktor przechowuje tylko i wylacznie jedna zmienna
-- | z opcjonalna negacja.
-- | Wykorzystywane do uproszczenia wyrazenia pod funktorem przekonaniowym.
convertT :: Logic -> Maybe CNF
convertT (C (Var x)) = Just [[Pure (Pure (VarE x))]]
convertT (C (Not (Var x))) = Just [[Pure (NotE (VarE x))]]
convertT (Not (C (Var x))) = Just [[NotE (Pure (VarE x))]]
convertT (Not (C (Not (Var x)))) = Just [[NotE (NotE (VarE x))]]
-- wartosc stala
convertT (C (Const x)) = Just [[Pure (Pure (Lit x))]]
convertT (C (Not (Const x))) = Just [[Pure (NotE (Lit x))]]
convertT (Not (C (Const x))) = Just [[NotE (Pure (Lit x))]]
convertT (Not (C (Not (Const x)))) = Just [[NotE (NotE (Lit x))]]
convertT (Not (Not x)) = convertT x
-- De Morgan
convertT (Not (BinForm And x y)) = convertT $ BinForm Or (Not x) (Not y)
convertT (Not (BinForm Or x y)) = convertT $ BinForm And (Not x) (Not y)
convertT (BinForm Or x y) =
  foldr (:) [] <$> do
    a <- convertT x
    b <- convertT y
    return $ (++) <$> a <*> b
convertT (BinForm And x y) = (++) <$> convertT x <*> convertT y
convertT _ = Nothing -- przy poprawnym wyrazeniu nie powinno tutaj dojsc


-- | Konweruje do koniunkcyjnej postaci normalnej
-- | wszystko znajdujace sie pod funktorem przekonaniowym
-- | oraz wydziela z funktora pojedyczne zmienne.
simplifyFunctors :: Logic -> Logic
simplifyFunctors (C x) = fixc . C . convert notI $ x
simplifyFunctors (Not (C x)) = Not . fixc . C . convert notI $ x
simplifyFunctors x = applyLogic simplifyFunctors x


-- | Przestawia funktor C na zewnatrz jezeli to mozliwe
fixc :: Logic -> Logic
fixc (C (BinForm And x y)) = BinForm And (fixc . C $ x) (fixc . C $ y)
fixc (C (BinForm Or x y)) = BinForm Or (fixc . C $ x) (fixc . C $ y)
fixc x = x


-- | Konwertuje wyrazenie do postaci CNF
-- | Nie ma zmiennych poza funktorem C() - inaczej zwroci Nothing
convertToCnf :: Logic -> Maybe CNF
convertToCnf = convertT . simplifyFunctors . replaceImpl


type CNF = [Clause]
type Clause = [Elem]
type Elem = Negable (Negable Atom)


unNegable :: Negable x -> x
unNegable (Pure x) = x
unNegable (NotE x) = x

-- | Datatype oznaczajacy, ze cos moze byc zanegowane
data Negable x =
    Pure x
  | NotE x
  deriving (Show, Eq, Functor, Foldable, Traversable)

-- | Pojedynczy atom wystepujacy w wyrazeniu CNF
data Atom =
    Lit TriVal
  | VarE Char
  deriving (Show, Eq)

stripAtoms :: CNF -> [Atom]
stripAtoms = map (unNegable . unNegable) . concat

getCharFromAtom :: Atom -> Maybe Char
getCharFromAtom (VarE x) = Just x
getCharFromAtom _ = Nothing

filterVars :: [Atom] -> String
filterVars = mapMaybe getCharFromAtom

modifyAllAtoms :: (Atom -> Atom) -> CNF -> CNF
modifyAllAtoms = fmap . fmap . fmap . fmap

modifyAllVars :: (Char -> Atom) -> CNF -> CNF
modifyAllVars f = modifyAllAtoms
                    (\case
                      VarE x -> f x
                      a -> a
                    )

-- | Konwertuje formule ze struktury danych
-- | reprezentujacej postac normalna
-- | do struktury danych reprezentujacej
-- | dowolne wyrazenie logiczne
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



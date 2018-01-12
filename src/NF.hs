{-
   Modul zawierajacy opis i konwersje do NF
-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
module NF (
    convertToCnf
  , unNegable
  , stripAtoms
  , filterVars
  , modifyAllAtoms
  , modifyAllVars
  , cnfToLogic
  , NF
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


-- | Przeksztalca wyrazenie bez -> i <-> do postaci normalnej
convert :: Logic -> Logic
convert (Not (Not x)) = convert x
-- wartosc stala
convert (Not (Const x)) = Const (notO x)
-- De Morgan
convert (Not (BinForm And x y)) = convert $ BinForm Or (Not x) (Not y)
convert (Not (BinForm Or x y)) = convert $ BinForm And (Not x) (Not y)
convert (BinForm Or x y) =
  foldl1' (BinForm And) $
    BinForm Or <$> stripLits (convert x) <*> stripLits (convert y)
convert (BinForm And x y) = BinForm And (convert x) (convert y)
convert (C x) = fixc . C . convertI $ x
convert (Not (C x)) = fixnc . C . convertI $ x
convert x = x


-- | Przestawia funktor C na zewnatrz jezeli to mozliwe
fixc :: Logic -> Logic
fixc (C (BinForm And x y)) = BinForm And (fixc . C $ x) (fixc . C $ y)
fixc x = x


-- | Przestawia funktor C na zewnatrz w wyrazeniu ~C(a * b * c * ..)
-- | do postaci ~C(a) + ~C(b) + ..
fixnc :: Logic -> Logic
fixnc (C (BinForm And x y)) =
  BinForm Or (fixnc . C $ x) (fixnc . C $ y)
fixnc (C x) = Not . C $ x
fixnc x = x


-- | Przeksztalca wyrazenie bez -> i <-> do postaci normalnej
-- | wewnatrz funktora C
convertI :: Logic -> Logic
convertI (Not (Not x)) = convertI x
-- wartosc stala
convertI (Not (Const x)) = Const (notI x)
-- De Morgan
convertI (Not (BinForm And x y)) = convertI $ BinForm Or (Not x) (Not y)
convertI (Not (BinForm Or x y)) = convertI $ BinForm And (Not x) (Not y)
convertI (BinForm Or x y) =
  foldl1' (BinForm And) $
    BinForm Or <$> stripLits (convertI x) <*> stripLits (convertI y)
convertI (BinForm And x y) = BinForm And (convertI x) (convertI y)
convertI x = x


-- | Konwertuje wyrazenie do postaci NF
-- | Nie ma zmiennych poza funktorem C() - inaczej zwroci Nothing
convertToCnf :: Logic -> Maybe NF
convertToCnf = run . convert . replaceImpl
  where
    run :: Logic -> Maybe NF
    run (C x) = (\a -> [[Pure a]]) <$> stripElems x
    run (Not (C x)) = (\a -> [[NotE a]]) <$> stripElems x
    run (BinForm And x y) = (++) <$> run x <*> run y
    run (BinForm Or x y) = (: []) <$> ((++) <$> stripF x <*> stripF y)
    run _ = Nothing -- niepoprawne wyrazenie

    stripF :: Logic -> Maybe Clause
    stripF (C x) = (\a -> [Pure a]) <$> stripElems x
    stripF (Not (C x)) = (\a -> [NotE a]) <$> stripElems x
    stripF (BinForm Or x y) = (++) <$> stripF x <*> stripF y
    stripF _ = Nothing

    stripElems :: Logic -> Maybe [Elem]
    stripElems (Const a) = Just [Pure (Lit a)]
    stripElems (Not (Const a)) = Just [NotE (Lit a)]
    stripElems (Var a) = Just [Pure (VarE a)]
    stripElems (Not (Var a)) = Just [NotE (VarE a)]
    stripElems (BinForm Or x y) = (++) <$> stripElems x <*> stripElems y
    stripElems _ = Nothing -- niepoprawne wyrazenie


type NF = [Clause]
-- moze inny kontener niz lista? (set? sequence?)
type Clause = [Negable [Elem]]
type Elem = Negable Atom


unNegable :: Negable x -> x
unNegable (Pure x) = x
unNegable (NotE x) = x

-- | Datatype oznaczajacy, ze cos moze byc zanegowane
data Negable x =
    Pure x
  | NotE x
  deriving (Show, Eq, Functor, Foldable, Traversable)

-- | Pojedynczy atom wystepujacy w wyrazeniu NF
data Atom =
    Lit TriVal
  | VarE Char
  deriving (Show, Eq)

stripAtoms :: NF -> [Atom]
stripAtoms = map unNegable . concatMap unNegable . concat

getCharFromAtom :: Atom -> Maybe Char
getCharFromAtom (VarE x) = Just x
getCharFromAtom _ = Nothing

filterVars :: [Atom] -> String
filterVars = mapMaybe getCharFromAtom

modifyAllAtoms :: (Atom -> Atom) -> NF -> NF
modifyAllAtoms = fmap . fmap . fmap . fmap . fmap

modifyAllVars :: (Char -> Atom) -> NF -> NF
modifyAllVars f = modifyAllAtoms
                    (\case
                      VarE x -> f x
                      a -> a
                    )

-- | Konwertuje formule ze struktury danych
-- | reprezentujacej postac normalna
-- | do struktury danych reprezentujacej
-- | dowolne wyrazenie logiczne
cnfToLogic :: NF -> Logic
cnfToLogic = foldl1' (BinForm And)
           . map clauseToLogic
    where
      clauseToLogic = foldl1' (BinForm Or)
                    . map funcToLogic
      funcToLogic (Pure l) = C $ foldl1' (BinForm Or) (map natomToLogic l)
      funcToLogic (NotE l) = Not $ C $ foldl1' (BinForm Or) (map natomToLogic l)
      natomToLogic (Pure x) = atomToLogic x
      natomToLogic (NotE x) = Not $ atomToLogic x
      atomToLogic (Lit x) = Const x
      atomToLogic (VarE x) = Var x



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
convert x = x


simplifyFunctors :: Logic -> Logic
simplifyFunctors (C x) = fixc . C . convertI $ x
simplifyFunctors (Not (C x)) = Not . fixc . C . convertI $ x
simplifyFunctors x = applyLogic simplifyFunctors x

-- | Przestawia funktor C na zewnatrz jezeli to mozliwe
fixc :: Logic -> Logic
fixc (C (BinForm And x y)) = BinForm And (fixc . C $ x) (fixc . C $ y)
fixc (C (BinForm Or x y)) = BinForm Or (fixc . C $ x) (fixc . C $ y)
fixc x = x


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


-- | Konwertuje wyrazenie do postaci CNF
-- | Nie ma zmiennych poza funktorem C() - inaczej zwroci Nothing
convertToCnf :: Logic -> Maybe CNF
convertToCnf = run . convert . simplifyFunctors . replaceImpl
  where
    run :: Logic -> Maybe CNF
    run (C x) = (\a -> [[Pure a]]) <$> stripAtom x
    run (Not (C x)) = (\a -> [[NotE a]]) <$> stripAtom x
    run (BinForm And x y) = (++) <$> run x <*> run y
    run (BinForm Or x y) = (: []) <$> ((++) <$> stripF x <*> stripF y)
    run _ = Nothing -- niepoprawne wyrazenie

    stripF :: Logic -> Maybe Clause
    stripF (C x) = (\a -> [Pure a]) <$> stripAtom x
    stripF (Not (C x)) = (\a -> [NotE a]) <$> stripAtom x
    stripF (BinForm Or x y) = (++) <$> stripF x <*> stripF y
    stripF _ = Nothing

    stripAtom :: Logic -> Maybe (Negable Atom)
    stripAtom (Var x) = Just . Pure . VarE $ x
    stripAtom (Const x) = Just . Pure . Lit $ x
    stripAtom (Not (Var x)) = Just . NotE . VarE $ x
    stripAtom (Not (Const x)) = Just . NotE . Lit $ x
    stripAtom _ = Nothing


type CNF = [Clause]
-- moze inny kontener niz lista? (set? sequence?)
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



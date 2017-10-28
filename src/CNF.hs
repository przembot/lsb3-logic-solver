{-
   Modul zawierajacy opis i konwersje do CNF
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
  , CNF
  , Clause
  , Elem
  , Negable (..)
  , Atom (..)
  ) where

import Data.Maybe (mapMaybe)
import Logic

-- | Zamienia wynikanie i ekwiwalencje na sumy i iloczyny
replaceImpl :: Logic -> Logic
replaceImpl (BinForm Impl x y) =
  BinForm Or (Not (replaceImpl x)) (replaceImpl y)
replaceImpl (BinForm Equiv x y) =
  BinForm And
    (BinForm Or (Not (replaceImpl x)) (replaceImpl y))
    (BinForm Or (Not (replaceImpl y)) (replaceImpl x))
replaceImpl (BinForm op x y) = BinForm op (replaceImpl x) (replaceImpl y)
replaceImpl (Not x) = Not (replaceImpl x)
replaceImpl (C x) = C (replaceImpl x)
replaceImpl x = x

-- | Pozbywa sie zbednych negacji,
-- uzywajac praw De Morgana
-- i usuwajac podwojne negacje
removeNeg :: Logic -> Logic
removeNeg = removeNegO notO
  where
    -- Parametrem funkcji jest funkcja logiczna NOT, stosowana by dla funktora C uzyc innej
    removeNegO :: (TriVal -> TriVal) -> Logic -> Logic
    removeNegO _ (Not (Not x)) = x
    -- De Morgan
    removeNegO notX (Not (BinForm And x y)) = BinForm Or (removeNegO notX $ Not x) (removeNegO notX $ Not y)
    removeNegO notX (Not (BinForm Or x y)) = BinForm And (removeNegO notX $ Not x) (removeNegO notX $ Not y)
    -- wartosc stala
    removeNegO notX (Const x) = Const (notX x)
    -- rekurencja
    removeNegO notX (Not x) = Not (removeNegO notX x)
    removeNegO notX (BinForm op x y) = BinForm op (removeNegO notX x) (removeNegO notX y)
    removeNegO _ (C x) = C $ removeNegO notI x
    removeNegO _ x = x

-- | Zamienia A or (B and C) na (A or B) and (A or C)
distribute :: Logic -> Logic
distribute (BinForm Or x (BinForm And y z)) =
  BinForm And (BinForm Or (distribute x) (distribute y))
              (BinForm Or (distribute x) (distribute z))
distribute (BinForm Or (BinForm And y z) x) =
  BinForm And (BinForm Or (distribute x) (distribute y))
              (BinForm Or (distribute x) (distribute z))
distribute (BinForm op x y) = BinForm op (distribute x) (distribute y)
distribute (C x) = C (distribute x)
distribute (Not x) = Not (distribute x)
distribute x = x

normalizeToCnf :: Logic -> Logic
normalizeToCnf expr =
  if new == expr
     then expr
     else normalizeToCnf new
       where
         new = distribute . removeNeg . moveAndToOutside $ expr

-- C( .. AND ..) -> C(..) AND C(..)
moveAndToOutside :: Logic -> Logic
moveAndToOutside (C (BinForm And x y)) = BinForm And (C x) (C y) -- tautologia w lsb3
moveAndToOutside (C x) = C $ moveAndToOutside x
moveAndToOutside (Not x) = Not $ moveAndToOutside x
moveAndToOutside (BinForm op x y) = BinForm op (moveAndToOutside x) (moveAndToOutside y)
moveAndToOutside x = x

-- zalozenie - nie ma zmiennych poza funktorem C()
convertToCnf :: Logic -> Maybe CNF
convertToCnf = run . normalizeToCnf . replaceImpl
  where
    run :: Logic -> Maybe CNF
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


testSample :: Logic
testSample = BinForm And (Not $ C $ BinForm And (Var 'a') (Var 'b'))
                         (C $ BinForm Or (Var 'p') (Var 'q'))
testSample2 = BinForm Or (Not $ C $ BinForm Or (Var 'a') (Var 'b'))
                         (Not $ C $ BinForm Or (Var 'p') (Var 'q'))

type CNF = [Clause]
-- moze inny kontener niz lista? (set? sequence?)
type Clause = [Negable [Elem]]
type Elem = Negable Atom

unNegable :: Negable x -> x
unNegable (Pure x) = x
unNegable (NotE x) = x

data Negable x =
    Pure x
  | NotE x
  deriving (Show, Eq, Functor, Foldable, Traversable)

data Atom =
    Lit TriVal
  | VarE Char
  deriving (Show, Eq)

stripAtoms :: CNF -> [Atom]
stripAtoms = map unNegable . concatMap unNegable . concat

getCharFromAtom :: Atom -> Maybe Char
getCharFromAtom (VarE x) = Just x
getCharFromAtom _ = Nothing

filterVars :: [Atom] -> String
filterVars = mapMaybe getCharFromAtom

modifyAllAtoms :: (Atom -> Atom) -> CNF -> CNF
modifyAllAtoms f = map (map (fmap (map (fmap f))))

modifyAllVars :: (Char -> Atom) -> CNF -> CNF
modifyAllVars f = modifyAllAtoms
                    (\case
                      VarE x -> f x
                      a -> a
                    )

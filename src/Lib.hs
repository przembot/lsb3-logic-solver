{-
   Implementacja logiki LSB3
-}
module Lib where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (catMaybes, mapMaybe)
import Control.Applicative ((<|>))


-- | Wartosci wystepujace w logike LSB3
data TriVal =
    TrueV
  | Neither
  | FalseV
  deriving (Show, Eq)

-- | Operacje dwuargumentowe na logice
data BinaryOp =
    And
  | Or
  | Impl
  | Equiv
  deriving Eq

instance Show BinaryOp where
  show And = "/\\"
  show Or = "\\/"
  show Impl = "->"
  show Equiv = "<->"

-- | Reprezentacja wyrazenia
data Logic =
    Const TriVal
  | Var Char
  | Not Logic
  | BinForm BinaryOp Logic Logic
  | C Logic
  deriving Eq

instance Show Logic where
  show (Const val) = show val
  show (Var c) = show c
  show (Not x) = "~" ++ show x
  show (BinForm op p q) = unwords ["(", show p, show op, show q, ")"]
  show (C x) = unwords ["C(", show x, ")"]

sample, sample2 :: Logic
sample = C $ BinForm Or (Const FalseV) $ BinForm And (Const Neither) (Const Neither)
sample2 = BinForm And (Var 'q') $ C $ BinForm Or (Var 'p') $ BinForm And (Const Neither) (Const Neither)

-- | Weryfikuje, czy podane wyrazenie jest poprawne
-- (czy nie zawiera zaglebionego funktora C)
isValid :: Logic -> Bool
isValid = const True


-- notO - negacja zewnetrzna
-- notI - negacja wewnetrzna
notO, notI :: TriVal -> TriVal
notO TrueV = FalseV
notO _ = TrueV
notI TrueV = FalseV
notI FalseV = TrueV
notI x = x


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
    removeNegO _ (Not (C x)) = C (removeNegO notI (Not x)) -- TODO: test
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


-- | Szuka pierwszej lepszej niepodstawionej zmiennej w wyrazeniu
findFreeVar :: Logic -> Maybe Char
findFreeVar (Const _) = Nothing
findFreeVar (Var v) = Just v
findFreeVar (Not e) = findFreeVar e
findFreeVar (C e) = findFreeVar e
findFreeVar (BinForm _ x y) = findFreeVar x <|> findFreeVar y


-- | Podstawia dana zmienna z podana wartoscia
-- jak odroznic zmienna wewnatrz C? -- odroznic wielkoscia liter w wyrazeniu
guessVar :: Char -> TriVal -> Logic -> Logic
guessVar var val (Var v) = if v == var then Const val else Var v
guessVar var val (Not e) = Not (guessVar var val e)
guessVar var val (C e) = C (guessVar var val e)
guessVar var val (BinForm op x y) = BinForm op (guessVar var val x) (guessVar var val y)
guessVar _ _ x = x


-- otestowac..
convertToCnf :: Logic -> Logic
convertToCnf expr =
  if new == expr
     then expr
     else convertToCnf new
       where
         new = distribute . removeNeg $ expr


-- | Znajduje wszystkie zmienne znajdujace sie w wyrazeniu
variables :: Logic -> Set Char
variables (Var v) = Set.singleton v
variables (BinForm _ x y) = Set.union (variables x) (variables y)
variables (C x) = variables x
variables (Not x) = variables x
variables _ = Set.empty


data Polarity =
    Positive
  | Negative
  | Mixed
    deriving (Show, Eq)

variablePolarity :: Logic -> Char -> Maybe Polarity
variablePolarity (Var v) var =
  if var == v then Just Positive
              else Nothing
variablePolarity (Not (Var v)) var =
  if var == v then Just Negative
              else Nothing
variablePolarity (C x) var = variablePolarity x var
-- variablePolarity var (Not x) = error "impossible in cnf"
variablePolarity (BinForm _ x y) var =
  combinePolarity (variablePolarity x var) (variablePolarity y var)
variablePolarity _ _ = Nothing


combinePolarity :: Maybe Polarity -> Maybe Polarity -> Maybe Polarity
combinePolarity (Just Positive) (Just Positive) = Just Positive
combinePolarity (Just Negative) (Just Negative) = Just Negative
combinePolarity Nothing a = a
combinePolarity a Nothing = a
combinePolarity _ _ = Just Mixed


-- Usuwa zmienne wystepujace w jednym biegunie w calym wyrazeniu
literalElimination :: Logic -> Logic
literalElimination e =
  let
    lits = Set.toList $ variables e
    pols = map (variablePolarity e) lits

    applyAll = foldl (.) id . map (uncurry guessVar) . catMaybes . zipWith extractPolarized lits $ pols
  in applyAll e

extractPolarized :: Char -> Maybe Polarity -> Maybe (Char, TriVal)
extractPolarized v (Just Positive) = Just (v, TrueV)
extractPolarized v (Just Negative) = Just (v, FalseV)
extractPolarized _ _ = Nothing


-- Wyekstrahuj klauzule z wyrazenia CNF
clauses :: Logic -> [Logic]
clauses (BinForm And x y) = clauses x ++ clauses y
clauses (C x) = clauses x
clauses e = [e]

-- Sprawdz czy klauzula zawiera tylko jedna zmienna
unitClause :: Logic -> Maybe (Char, TriVal)
unitClause (Var v) = Just (v, TrueV)
unitClause (Not (Var v)) = Just (v, TrueV)
unitClause _ = Nothing

unitPropagation :: Logic -> Logic
unitPropagation expr = replaceAll expr
  where
    assignments = mapMaybe unitClause . clauses $ expr
    replaceAll = foldl (.) id (map (uncurry guessVar) assignments)


unConst :: Logic -> TriVal
unConst (Const x) = x
unConst (C (Const x)) = x
unConst x = error $ "unConst no const, but " ++ show x


-- | Funkcja upraszczajaca And w logice Cp
-- Zgodna z tabela prawdy
reduceAndP :: Logic -> Logic -> Logic
reduceAndP (Const FalseV) _ = Const FalseV
reduceAndP _ (Const FalseV) = Const FalseV
-- 1 jest elementem neutralnym
-- 1/2 w prawdzie nie jest elementem neutralnym,
-- jednak w problemie SAT nie spelnia zadnej roli
reduceAndP (Const _) x = x
reduceAndP x (Const _) = x
-- reduceAndP (Const Neither) (Const Neither) = Const Neither
-- reduceAndP (Const _) (Const _) = Const FalseV
reduceAndP x y = BinForm And x y -- nieredukowalne


-- | Funkcja upraszczajaca Or w logice Cp
-- Zgodna z tabela prawdy
reduceOrP :: Logic -> Logic -> Logic
reduceOrP (Const TrueV) _ = Const TrueV
reduceOrP _ (Const TrueV) = Const TrueV
-- 0 jest elementem neutralnym
-- 1/2 w prawdzie nie jest elementem neutralnym,
-- jednak w problemie SAT nie spelnia zadnej roli
reduceOrP (Const _) x = x
reduceOrP x (Const _) = x
reduceOrP x y = BinForm Or x y

-- | Upraszcza formule CNF wyrazenia Cp,
-- jezeli to mozliwe to redukuje wyrazenie do wartosci logicznej
simplifyP :: Logic -> Logic
simplifyP (Const a) = Const a
simplifyP (Var a) = Var a
simplifyP (Not x) =
  case simplifyP x of
    Const y -> Const (notI y)
    e -> Not e
simplifyP (BinForm And x y) =
  reduceAndP (simplifyP x) (simplifyP y)
simplifyP (BinForm Or x y) =
  reduceOrP (simplifyP x) (simplifyP y)
simplifyP x = x


-- | Upraszcza formule CNF z logiki LSB3_P
simplifyLP :: Logic -> Logic
simplifyLP a@(Const _) = a
simplifyLP a@(Var _) = a
-- simplifyLP (C a@(Const _)) = a
simplifyLP (Not x) =
  case simplifyLP x of
    Const y -> Const (notO y)
    e -> Not e
-- w przypadku wyrazenia Or/And redukcja zachodzi tak samo jak wewnatrz C_p
simplifyLP (BinForm And x y) =
  reduceAndP (simplifyLP x) (simplifyLP y)
simplifyLP (BinForm Or x y) =
  reduceOrP (simplifyLP x) (simplifyLP y)
simplifyLP (C x) =
  case simplifyP x of
    Const a -> Const a
    e -> C e
simplifyLP x = x

type Intepretation = [(Char, TriVal)]

runSatDPLL :: Logic -> Bool
runSatDPLL = satDPLL . convertToCnf . replaceImpl

runTautDPLL :: Logic -> Bool
runTautDPLL = (==False) . runSatDPLL . Not

-- satDPLL :: Intepretation -> Logic -> Maybe Intepretation
satDPLL :: Logic -> Bool
satDPLL expr =
  case findFreeVar expr' of
    Nothing -> (==TrueV) . unConst . simplifyLP $ expr'
    Just var ->
      let
        trueGuess = simplifyLP (guessVar var TrueV expr)
        neitherGuess = simplifyLP (guessVar var Neither expr)
        falseGuess = simplifyLP (guessVar var FalseV expr)
      in satDPLL trueGuess || satDPLL neitherGuess || satDPLL falseGuess
 where
   expr' = literalElimination . unitPropagation $ expr

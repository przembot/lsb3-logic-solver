module SAT (
    uniRunSat
  , uniRunTaut
  , LogicType (..)
  , SolverType (..)
  , Error (..)
  , Interpretation
  , SatResult
  , TautResult
  ) where

import Data.Maybe (mapMaybe, listToMaybe)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Control.Applicative ((<|>))
import Data.Foldable (foldl')

import Text.Parsec (ParseError)

import Logic
import CNF


-- | Porownanie polarnosci - jezeli sa zgodne, to zapamietuje polarnosc.
-- | W przeciwnym przypadku zapominam.
-- | Nothing oznacza pomieszane polarnosci.
comparePols :: Eq a => Maybe a -> a -> Maybe a
comparePols (Just x) y = if x == y then Just x
                                   else Nothing
comparePols _ _ = Nothing


-- | Aktualizacja danych w mapie opisujacej polarnosci zmiennych
updateHMData :: HashMap Char (Maybe TriVal)
             -> VarPol -> HashMap Char (Maybe TriVal)
updateHMData hm (VarPol (x, pols)) =
  case HM.lookup x hm of
    (Just oldpols) -> HM.insert x (comparePols oldpols pols) hm
    _ -> HM.insert x (Just pols) hm


-- | Wrapper na polarnosc i nazwe zmiennej
newtype VarPol = VarPol (Char, TriVal)


-- | Konwersja struktury zawierajaca zmienna oraz jej polarnosc
polToVPol :: Negable (Negable Atom) -> Maybe VarPol
polToVPol (Pure (Pure (VarE x))) = Just $ VarPol (x, TrueV)
polToVPol (Pure (NotE (VarE x))) = Just $ VarPol (x, FalseV)
polToVPol (NotE (Pure (VarE x))) = Just $ VarPol (x, FalseV)
polToVPol (NotE (NotE (VarE x))) = Just $ VarPol (x, TrueV)
polToVPol _ = Nothing


-- | Znajduje wszystkie zmienne bedace w jednej polarnosci
stripPolarities :: CNF -> HashMap Char TriVal
stripPolarities = HM.mapMaybe id
                . foldl' updateHMData HM.empty
                . mapMaybe polToVPol
                . concatMap sequence
                . concat


-- | Czy klauzula zawiera tylko jedna zmienna - i jezli tak to jaka oraz
-- | co za nia nalezy podstawic
isUnitClause :: Clause -> Maybe (Char, TriVal)
isUnitClause [Pure [Pure (VarE x)]] = Just (x, TrueV)
isUnitClause [Pure [NotE (VarE x)]] = Just (x, FalseV)
isUnitClause [NotE [Pure (VarE x)]] = Just (x, FalseV)
isUnitClause [NotE [NotE (VarE x)]] = Just (x, TrueV)
isUnitClause _ = Nothing


-- | Mapa zawierajaca informacje o mozliwych podstawieniach przy uzyciu
-- | Unit Propagation
assignments :: CNF -> HashMap Char TriVal
assignments = HM.fromList
            . mapMaybe isUnitClause


-- | Wykonuje mozliwe podstawienia heurtystyczne
-- | Literal elimination: Podstaw za zmienna bedaca w jednej polarnosci w calym wyrazeniu
-- | odpowiednia stala wartosc
-- | Unit propagation: Podstawia wartosci za zmienne wystepujace samodzielnie
composedHeuristics :: CNF -> (Interpretation, CNF)
composedHeuristics form =
  let
    subsmap = assignments form `HM.union` stripPolarities form
  in (HM.toList subsmap, modifyAllVars
    (\x -> case HM.lookup x subsmap of
                  Just val -> Lit val
                  _ -> VarE x
    ) form)

-- | Upraszcza wedle mozliwosci wyrazenie CNF,
-- | jezeli jest to mozliwe zostaje zredukowane do jednej wartosci
simplifyCNF :: ([Elem] -> [Elem]) -- ^ funkcja redukujaca wartosci wewnatrz funktora, zalezna od wybranego typu logiki T lub P
            -> CNF -> CNF
simplifyCNF se = foldl' reduceClauses []
               . map (simplifyClause se)

reduceClauses :: CNF -> Clause -> CNF
reduceClauses acc [] = filterElemF acc FalseV
reduceClauses acc [Pure []] = filterElemF acc FalseV
reduceClauses acc [NotE []] = filterElemF acc TrueV
reduceClauses acc [Pure [Pure (Lit x)]] = filterElemF acc x
reduceClauses acc [Pure [NotE (Lit x)]] = filterElemF acc (notI x)
reduceClauses acc [NotE [Pure (Lit x)]] = filterElemF acc (notO x)
reduceClauses acc [NotE [NotE (Lit x)]] = filterElemF acc (notO . notI $ x)
reduceClauses acc a = a:acc


-- | Wyrazenie CNF oznaczajace nieudana probe podstawien wartosci
failSat :: CNF
failSat = [[Pure [Pure (Lit FalseV)]]]


-- | Funkcja upraszczajaca klauzule
simplifyClause :: ([Elem] -> [Elem])
               -> Clause -> Clause
simplifyClause se = foldl' reduceClause []
                  . map (fmap se)


reduceClause :: Clause -> Negable [Elem] -> Clause
reduceClause acc (Pure []) = filterElemT acc FalseV
reduceClause acc (NotE []) = filterElemT acc TrueV
reduceClause acc (Pure [Pure (Lit x)]) = filterElemT acc x
reduceClause acc (Pure [NotE (Lit x)]) = filterElemT acc (notI x)
reduceClause acc (NotE [Pure (Lit x)]) = filterElemT acc (notO x)
reduceClause acc (NotE [NotE (Lit x)]) = filterElemT acc (notO . notI $ x)
reduceClause acc a = a:acc

filterElemT :: Clause -> TriVal -> Clause
filterElemT _ TrueV = trueClause
filterElemT acc _ = acc

filterElemF :: CNF -> TriVal -> CNF
filterElemF acc TrueV = acc
filterElemF _ _ = failSat

-- | Klauzula oznaczajaca udane podstawienie wewnatrz niej
trueClause :: Clause
trueClause = [Pure [Pure (Lit TrueV)]]

simplifyElems :: [Elem] -> [Elem]
simplifyElems = foldl' simplifyElem []

simplifyElem :: [Elem] -> Elem -> [Elem]
simplifyElem [Pure (Lit TrueV)] _ = [Pure (Lit TrueV)] -- klauzula juz prawdziwa
simplifyElem _ (Pure (Lit TrueV)) = [Pure (Lit TrueV)]
simplifyElem _ (NotE (Lit FalseV)) = [Pure (Lit TrueV)]
-- LSB3_P, 1/2 jest obojetna
simplifyElem acc (Pure (Lit _)) = acc
simplifyElem acc (NotE (Lit _)) = acc
simplifyElem acc a = a:acc

simplifyElemsT :: [Elem] -> [Elem]
simplifyElemsT = snd . foldl' simplifyElemT (False, [])

simplifyElemT :: (Bool, [Elem]) -> Elem -> (Bool, [Elem])
simplifyElemT acc@(_, [Pure (Lit TrueV)]) _ = acc
simplifyElemT (s, _) (Pure (Lit TrueV)) = (s, [Pure (Lit TrueV)])
simplifyElemT (s, _) (NotE (Lit FalseV)) = (s, [Pure (Lit TrueV)])
simplifyElemT acc (Pure (Lit FalseV)) = acc
simplifyElemT acc (NotE (Lit TrueV)) = acc
-- LSB3_T, trzeba pamietac i brac pod uwage wystapienie 1/2
simplifyElemT (s, acc) (Pure (Lit Neither)) =
  if s then (s, [Pure (Lit TrueV)])
       else (True, acc)
simplifyElemT (s, acc) (NotE (Lit Neither)) =
  if s then (s, [Pure (Lit TrueV)])
       else (True, acc)
simplifyElemT (s, acc) a = (s, a:acc)

-- | Znajdz w wyrazeniu, jezeli istnieje, nieprzypisana zmienna
findVar :: CNF -> Maybe Char
findVar = listToMaybe . filterVars . stripAtoms


-- | Jezeli w wyrazeniu znajduje sie wolna zmienna, zwraca ja
-- | jezeli nie, to zwraca wartosc calego wyrazenia
isSimplified :: CNF -> Either Char TriVal
isSimplified [] = Right TrueV
isSimplified [[Pure [Pure (Lit x)]]] = Right x
isSimplified form = case findVar form of
                      (Just x) -> Left x
                      _ -> Right FalseV

-- | Podstaw wartosc za dana zmienna
substitudeVar :: Char -> TriVal -> CNF -> CNF
substitudeVar var val = modifyAllVars
                          (\v -> if v == var then Lit val
                                             else VarE v
                          )


-- | Typ reprezentujacy podstawienia dajace spelnialna formule
type Interpretation = [(Char, TriVal)]


-- | Glowny silnik rozwiazywania problemu SAT przy uzyciu heurystyk
-- | zgodnie z algorytmem DPLL dostosowanym do logiki LSB3
satDPLL :: Interpretation -> ([Elem] -> [Elem]) -> CNF -> Maybe Interpretation
satDPLL hist se expr =
  case isSimplified expr' of
    Right x -> if x == TrueV then Just (histheur++hist) else Nothing
    Left var ->
      let
        trueGuess = simplifyCNF' (substitudeVar var TrueV expr')
        neitherGuess = simplifyCNF' (substitudeVar var Neither expr')
        falseGuess = simplifyCNF' (substitudeVar var FalseV expr')
      in satDPLL' (addHist var TrueV) trueGuess
         <|> satDPLL' (addHist var Neither) neitherGuess
         <|> satDPLL' (addHist var FalseV) falseGuess
   where
     (histheur, c) = composedHeuristics expr
     expr' = simplifyCNF' c
     simplifyCNF' = simplifyCNF se
     satDPLL' h = satDPLL h se
     addHist var val = (var,val):(histheur++hist)


-- | Silnik sluzacy do rozwiazywania problemu SAT
-- | przy uzyciu naiwnego algorytmu prob i bledow
satNaive :: Interpretation -> ([Elem] -> [Elem]) -> CNF -> Maybe Interpretation
satNaive hist se expr =
  case isSimplified expr' of
    Right x -> if x == TrueV then Just hist else Nothing
    Left var ->
      let
        trueGuess = simplifyCNF' (substitudeVar var TrueV expr)
        neitherGuess = simplifyCNF' (substitudeVar var Neither expr)
        falseGuess = simplifyCNF' (substitudeVar var FalseV expr)
      in satNaive' (addHist var TrueV) trueGuess
         <|> satNaive' (addHist var Neither) neitherGuess
         <|> satNaive' (addHist var FalseV) falseGuess
   where
     expr' = simplifyCNF' expr
     simplifyCNF' = simplifyCNF se
     satNaive' h = satNaive h se
     addHist var val = (var,val):hist



-- | Opakowanie na bledy mogace wystapic przy probie uzycia programu
data Error =
    ParseFailure ParseError
  | CNFConversionFail
  | NoInterpretationFound
  | TautologyFail Interpretation
  deriving (Show, Eq)

throwOnNothing :: Error -> Maybe a -> Either Error a
throwOnNothing _ (Just a) = Right a
throwOnNothing e _ = Left e

type SatResult = Either Error Interpretation
type TautResult = Either Error ()

satToTautRes :: SatResult -> TautResult
satToTautRes (Left NoInterpretationFound) = Right ()
satToTautRes (Left x) = Left x
satToTautRes (Right x) = Left . TautologyFail $ x


runSat :: ([Elem] -> [Elem]) -> Logic -> SatResult
runSat f = (>>= throwOnNothing NoInterpretationFound)
         . fmap (satDPLL [] f)
         . throwOnNothing CNFConversionFail
         . convertToCnf


runNaiveSat :: ([Elem] -> [Elem]) -> Logic -> SatResult
runNaiveSat f = (>>= throwOnNothing NoInterpretationFound)
              . fmap (satNaive [] f)
              . throwOnNothing CNFConversionFail
              . convertToCnf


data LogicType = LSB3T
               | LSB3P
               deriving Eq

data SolverType = Naive
                | DPLL
                deriving Eq

uniLogicMapper :: LogicType -> [Elem] -> [Elem]
uniLogicMapper LSB3T = simplifyElemsT
uniLogicMapper LSB3P = simplifyElems


uniRunSat :: SolverType -> LogicType -> Logic -> SatResult
uniRunSat Naive = runNaiveSat . uniLogicMapper
uniRunSat DPLL = runSat . uniLogicMapper


uniRunTaut :: SolverType -> LogicType -> Logic -> TautResult
uniRunTaut s l = satToTautRes . uniRunSat s l . Not

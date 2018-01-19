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

import Data.Maybe (mapMaybe, listToMaybe, maybe)
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
updateHMData :: HashMap Char (Maybe (Bool, Bool))
             -> VarPol -> HashMap Char (Maybe (Bool, Bool))
updateHMData hm (VarPol (x, pols)) =
  case HM.lookup x hm of
    (Just oldpols) -> HM.insert x (comparePols oldpols pols) hm
    _ -> HM.insert x (Just pols) hm


-- | Wrapper na polarnosc i nazwe zmiennej
newtype VarPol = VarPol (Char, (Bool, Bool))


-- | Konwersja struktury zawierajaca zmienna oraz jej polarnosc
polToVPol :: Negable (Negable Atom) -> Maybe VarPol
polToVPol (Pure (Pure (VarE x))) = Just $ VarPol (x, (True, True))
polToVPol (Pure (NotE (VarE x))) = Just $ VarPol (x, (True, False))
polToVPol (NotE (Pure (VarE x))) = Just $ VarPol (x, (False, True))
polToVPol (NotE (NotE (VarE x))) = Just $ VarPol (x, (False, False))
polToVPol _ = Nothing

polsToVal :: (Bool, Bool) -> TriVal
polsToVal (True, True) = TrueV
polsToVal (True, False) = FalseV
polsToVal (False, True) = FalseV
polsToVal (False, False) = TrueV

-- | Znajduje wszystkie zmienne bedace w jednej polarnosci
stripPolarities :: CNF -> HashMap Char TriVal
stripPolarities = HM.mapMaybe (fmap polsToVal)
                . foldl' updateHMData HM.empty
                . mapMaybe polToVPol
                . concat


-- | Czy klauzula zawiera tylko jedna zmienna - i jezli tak to jaka oraz
-- | co za nia nalezy podstawic
isUnitClause :: Clause -> Maybe (Char, TriVal)
isUnitClause [Pure (Pure (VarE x))] = Just (x, TrueV)
isUnitClause [Pure (NotE (VarE x))] = Just (x, FalseV)
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
simplifyCNF :: CNF -> CNF
simplifyCNF = foldl' reduceClauses []
           . map simplifyClause

reduceClauses :: CNF -> Clause -> CNF
reduceClauses acc [] = filterElemF acc FalseV
reduceClauses acc [Pure (Pure (Lit x))] = filterElemF acc x
reduceClauses acc [Pure (NotE (Lit x))] = filterElemF acc (notI x)
reduceClauses acc [NotE (Pure (Lit x))] = filterElemF acc (notO x)
reduceClauses acc [NotE (NotE (Lit x))] = filterElemF acc (notO . notI $ x)
reduceClauses acc a = a:acc


-- | Wyrazenie CNF oznaczajace nieudana probe podstawien wartosci
failSat :: CNF
failSat = [[Pure (Pure (Lit FalseV))]]


-- | Funkcja upraszczajaca klauzule
simplifyClause :: Clause -> Clause
simplifyClause = foldl' reduceClause []
               . simplifyElems


reduceClause :: Clause -> Elem -> Clause
reduceClause acc (Pure (Pure (Lit x))) = filterElemT acc x
reduceClause acc (Pure (NotE (Lit x))) = filterElemT acc (notI x)
reduceClause acc (NotE (Pure (Lit x))) = filterElemT acc (notO x)
reduceClause acc (NotE (NotE (Lit x))) = filterElemT acc (notO . notI $ x)
reduceClause acc a = a:acc

filterElemT :: Clause -> TriVal -> Clause
filterElemT _ TrueV = trueClause
filterElemT acc _ = acc

filterElemF :: CNF -> TriVal -> CNF
filterElemF acc TrueV = acc
filterElemF _ _ = failSat

-- | Klauzula oznaczajaca udane podstawienie wewnatrz niej
trueClause :: Clause
trueClause = [Pure (Pure (Lit TrueV))]

simplifyElems :: [Elem] -> [Elem]
simplifyElems = foldl' simplifyElem []

simplifyElem :: [Elem] -> Elem -> [Elem]
-- klauzula juz prawdziwa
simplifyElem [Pure (Pure (Lit TrueV))] _ = [Pure (Pure (Lit TrueV))]
-- wynika z tabel prawdy
simplifyElem _ (Pure (Pure (Lit TrueV))) = [Pure (Pure (Lit TrueV))]
simplifyElem _ (NotE (NotE (Lit TrueV))) = [Pure (Pure (Lit TrueV))]
simplifyElem acc (NotE (Pure (Lit TrueV))) = acc
simplifyElem acc (Pure (NotE (Lit TrueV))) = acc

simplifyElem acc (Pure (Pure (Lit Neither))) = acc
simplifyElem _ (NotE (NotE (Lit Neither))) = [Pure (Pure (Lit TrueV))]
simplifyElem _ (NotE (Pure (Lit Neither))) = [Pure (Pure (Lit TrueV))]
simplifyElem acc (Pure (NotE (Lit Neither))) = acc

simplifyElem acc (Pure (Pure (Lit FalseV))) = acc
simplifyElem acc (NotE (NotE (Lit FalseV))) = acc
simplifyElem _ (NotE (Pure (Lit FalseV))) = [Pure (Pure (Lit TrueV))]
simplifyElem _ (Pure (NotE (Lit FalseV))) = [Pure (Pure (Lit TrueV))]
simplifyElem acc a = a:acc


-- | Znajdz w wyrazeniu, jezeli istnieje, nieprzypisana zmienna
findVar :: CNF -> Maybe Char
findVar = listToMaybe . filterVars . stripAtoms


-- | Jezeli w wyrazeniu znajduje sie wolna zmienna, zwraca ja
-- | jezeli nie, to zwraca wartosc calego wyrazenia
isSimplified :: CNF -> Either Char TriVal
isSimplified [] = Right TrueV
isSimplified [[Pure (Pure (Lit x))]] = Right x
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
-- | zgodnie z algorytmem DPLL dostosowanym do logiki LSB3_P
satDPLL :: Interpretation -> CNF -> Maybe Interpretation
satDPLL hist expr =
  case isSimplified expr' of
    Right x -> if x == TrueV
                  then Just (histheur++hist)
                  else Nothing
    Left var ->
      let
        branch val = satDPLL (addHist var val) (simplifyCNF (substitudeVar var val expr'))
      in
        branch TrueV <|> branch Neither <|> branch FalseV
   where
     (histheur, c) = composedHeuristics expr
     expr' = simplifyCNF c
     addHist var val = (var,val):(histheur++hist)


-- | Silnik sluzacy do rozwiazywania problemu SAT
-- | przy uzyciu naiwnego algorytmu prob i bledow
satNaive :: LogicType -> Interpretation -> Logic -> Maybe Interpretation
satNaive lt hist expr =
  case findUnassignedVar expr of
    Just var ->
      let
        branch val = satNaive' (addHist var val) (substitudeNaiveVar var val expr)
      in
        branch TrueV <|> branch Neither <|> branch FalseV
    Nothing ->
      if evalLogic lt expr == Just TrueV
         then Just hist
         else Nothing
   where
     addHist var val = (var,val):hist
     satNaive' = satNaive lt

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


runSat :: Logic -> SatResult
runSat = (>>= throwOnNothing NoInterpretationFound)
       . fmap (satDPLL [])
       . throwOnNothing CNFConversionFail
       . convertToCnf


runNaiveSat :: LogicType -> Logic -> SatResult
runNaiveSat lt = maybe (Left NoInterpretationFound) Right
               . satNaive lt []


data SolverType = Naive
                | DPLL
                deriving (Eq, Show)


uniRunSat :: LogicType -> SolverType -> Logic -> SatResult
uniRunSat LSB3T _ = runNaiveSat LSB3T
uniRunSat LSB3P DPLL = runSat
uniRunSat LSB3P Naive = runNaiveSat LSB3P


uniRunTaut :: LogicType -> SolverType -> Logic -> TautResult
uniRunTaut l s = satToTautRes . uniRunSat l s . Not

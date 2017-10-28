{-# LANGUAGE LambdaCase #-}
module SAT where

import Data.Maybe (mapMaybe, listToMaybe)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

import Logic
import CNF


stripVar :: Atom -> Maybe Char
stripVar (VarE x) = Just x
stripVar _ = Nothing

comparePols :: Maybe BoolT -> Maybe BoolT -> Maybe BoolT
comparePols (Just x) (Just y) = if x == y then Just x
                                          else Nothing
comparePols _ _ = Nothing

-- | Nothing oznacza pomieszane polarnosci
updateHMData :: HashMap Char (Maybe BoolT)
             -> VarPol -> HashMap Char (Maybe BoolT)
updateHMData hm (VarPol (x, pols)) =
  case HM.lookup x hm of
    Nothing -> HM.insert x (Just pols) hm
    (Just oldpols) -> HM.insert x (comparePols oldpols (pure pols)) hm

type BoolT = (Bool, Bool)
newtype VarPol = VarPol (Char, BoolT)

polToVPol :: Negable (Negable Char) -> VarPol
polToVPol (Pure (Pure x)) = VarPol (x, (True, True))
polToVPol (Pure (NotE x)) = VarPol (x, (True, False))
polToVPol (NotE (Pure x)) = VarPol (x, (False, True))
polToVPol (NotE (NotE x)) = VarPol (x, (False, False))


-- | Znajduje wszystkie zmienne bedace w jednej polarnosci
stripPolarities :: CNF -> HashMap Char BoolT
stripPolarities = HM.mapMaybe id -- catMaybes
                  . foldl updateHMData HM.empty
                  . mapMaybe (fmap polToVPol . traverse sequence . fmap (fmap stripVar))
                  . concatMap (\case
                                  Pure l -> map Pure l
                                  NotE l -> map NotE l)
                  . concat

-- | Zwraca odpowiednie podstawienie przy daniej polaryzacji zmiennej
subs :: BoolT -> TriVal
subs (True, True) = TrueV
subs (False, True) = FalseV
subs (True, False) = FalseV
subs (False, False) = TrueV


-- | Podstaw za zmienna bedaca w jednej polarnosci odpowiednia stala wartosc
literalElimination :: CNF -> CNF
literalElimination form =
  let
    varpols = stripPolarities form
  in modifyAllVars
    (\x -> case HM.lookup x varpols of
                  Just pols -> Lit (subs pols)
                  _ -> VarE x
    ) form

-- mozliwa optymalizacja, wyrzucic subs?
isUnitClause :: Negable [Elem] -> Maybe (Char, TriVal)
isUnitClause (Pure [Pure (VarE x)]) = Just (x, curry subs True True)
isUnitClause (Pure [NotE (VarE x)]) = Just (x, curry subs True False)
isUnitClause (NotE [Pure (VarE x)]) = Just (x, curry subs False True)
isUnitClause (NotE [NotE (VarE x)]) = Just (x, curry subs False False)
isUnitClause _ = Nothing

assignments :: CNF -> HashMap Char TriVal
assignments = HM.fromList
            . mapMaybe isUnitClause
            . concat

-- | Podstawia wartosci za zmienne wystepujace samodzielnie
unitPropagation :: CNF -> CNF
unitPropagation form =
  let
    subsmap = assignments form
  in modifyAllVars
    (\x -> case HM.lookup x subsmap of
                  Just val -> Lit val
                  _ -> VarE x
    ) form

isNonEmptyClause :: Clause -> Bool
isNonEmptyClause [Pure []] = False
isNonEmptyClause [NotE []] = False
isNonEmptyClause [] = False
isNonEmptyClause _ = True

simplifyCNF :: ([Elem] -> [Elem])
            -> CNF -> CNF
simplifyCNF se = foldl reduceClauses []
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

failSat = [[Pure [Pure (Lit FalseV)]]]


simplifyClause :: ([Elem] -> [Elem])
               -> Clause -> Clause
simplifyClause se = foldl reduceClause []
                  . map (fmap se)


reduceClause :: Clause -> Negable [Elem] -> Clause
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

trueClause = [Pure [Pure (Lit TrueV)]]

simplifyElems :: [Elem] -> [Elem]
simplifyElems = foldl simplifyElem []

simplifyElem :: [Elem] -> Elem -> [Elem]
simplifyElem [Pure (Lit TrueV)] _ = [Pure (Lit TrueV)] -- klauzula juz prawdziwa
simplifyElem _ (Pure (Lit TrueV)) = [Pure (Lit TrueV)]
simplifyElem _ (NotE (Lit FalseV)) = [Pure (Lit TrueV)]
simplifyElem acc (Pure (Lit FalseV)) = acc
simplifyElem acc (NotE (Lit TrueV)) = acc
-- LSB3_P, 1/2 jest obojetna
simplifyElem acc (Pure (Lit Neither)) = acc
simplifyElem acc (NotE (Lit Neither)) = acc
simplifyElem acc a = a:acc

simplifyElemsT :: [Elem] -> [Elem]
simplifyElemsT = snd . foldl simplifyElemT (False, [])

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

-- satDPLL :: Intepretation -> Logic -> Maybe Intepretation
satDPLL :: ([Elem] -> [Elem]) -> CNF -> Bool
satDPLL se expr =
  case isSimplified expr' of
    Right x -> x == TrueV
    Left var ->
      let
        trueGuess = simplifyCNF' (substitudeVar var TrueV expr)
        neitherGuess = simplifyCNF' (substitudeVar var Neither expr)
        falseGuess = simplifyCNF' (substitudeVar var FalseV expr)
      in satDPLL' trueGuess || satDPLL' neitherGuess || satDPLL' falseGuess
   where
     expr' = simplifyCNF' . literalElimination . unitPropagation $ expr
     simplifyCNF' = simplifyCNF se
     satDPLL' = satDPLL se

xD :: Maybe x -> x
xD (Just x) = x
xD _ = error "maybe fail"


runSat :: ([Elem] -> [Elem]) -> Logic -> Maybe Bool
runSat f = fmap (satDPLL f) . convertToCnf


runSatPDPLL, runSatTDPLL :: Logic -> Bool
runSatPDPLL = xD . runSat simplifyElems
runSatTDPLL = xD . runSat simplifyElemsT

runTautPDPLL, runTautTDPLL :: Logic -> Bool
runTautPDPLL = (==False) . runSatPDPLL . Not
runTautTDPLL = (==False) . runSatTDPLL . Not

{-|
   Modul w ktorym zrealizowany zostal parser formuly logiki LSB3.
-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoStrict #-}
module Parser (
  parseLogic
  ) where

import Text.Parsec
import Data.Text (Text)
import qualified Data.Text as T

import Logic

{-
Gramatyka

Powtarzajace sie elementy:
binop := "*" | "+" | "->" | "<->" ;
unop := "~" ;
var := char ;
const := T | N | F ;
atom := var | const ;

Gramatyka poczatkowa:

expr := expr binop expr
      | unop expr
      | "C(" expr ")"
      | "(" expr ")"
      | atom
      ;


bez lewej rekursji: (gramatyka LL(1))

expr := phrase {binop phrase}

phrase := unop phrase
        | "C(" expr ")"
        | "(" expr ")"
        | atom
        ;

gramatyka, ktora nie dopuszcza zagniezdzonego funktora C:

expr := phrase {binop phrase}

phrase := unop expr
        | "(" expr ")"
        | "C(" exprL ")"
        | atom
        ;

exprL := phraseL {binop phraseL}
phraseL := unop exprL
        | "(" exprL ")"
        | atom
        ;
-}

type Parser = Parsec Text ()


-- | Skladanie operatorow binarnych we wlasciwej kolejnosci
mergeOp :: BinaryOp -> [BinaryOp] -> [Logic] -> ([BinaryOp], [Logic])
mergeOp op opers (ex:exprs) = foldl f ([], [ex]) (zip opers exprs)
  where
    -- lista [Logic] nie moze byc pusta, wynika to z pattern matcha wyzej
    f (ops, e:es) (curop, l) =
      if curop == op
         then (ops, BinForm op e l:es)
         else (curop:ops, e:l:es)
mergeOp _ ops e = (ops, e)


-- | Sklada w pojedyczne wyrazenie zbior formul wraz z operatorami,
-- | ktore je oddzielaja
mergeOps :: [BinaryOp] -> [Logic] -> Logic
mergeOps ops = head . snd
         . uncurry (mergeOp Equiv)
         . uncurry (mergeOp Impl)
         . uncurry (mergeOp Or)
         . mergeOp And ops

-- | Generyczny generator parsera wyrazenia
exprGen :: Parser Logic -- ^ parser formuly
        -> Parser Logic
exprGen phr = do
  x <- phr
  (ops, exprs) <- unzip <$> many ((,) <$> binaryOp <*> phr)
  return $ mergeOps ops (x:exprs)


-- | Parser wyrazenia logiki LSB3
expr :: Parser Logic
expr = exprGen phrase


-- | Parser wyrazenia znajdujacego sie wewnatrz funktora C()
exprInside :: Parser Logic
exprInside = exprGen phraseInside


phrase :: Parser Logic
phrase = C <$> (char 'C' >> parens exprInside)
           <|> phraseSimple expr


-- | Parser frazy znajdujacej sie wewnatrz funktora (nie dopuszcza zagniezdzenia C())
phraseInside :: Parser Logic
phraseInside = phraseSimple exprInside


-- | Parser pojedynczej frazy
phraseSimple :: Parser Logic -- ^ parser calego wyrazenia (dla rekurencji)
             -> Parser Logic
phraseSimple rec = Not <$> (char '~' >> phrase)
               <|> parens rec
               <|> atom


atom :: Parser Logic
atom = constVal
   <|> var
   <?> "const value or variable"


constVal :: Parser Logic
constVal = (char 'T' >> return (Const TrueV))
       <|> (char 'N' >> return (Const Neither))
       <|> (char 'F' >> return (Const FalseV))
       <?> "const value"


var :: Parser Logic
var = Var <$> lower


binaryOp :: Parser BinaryOp
binaryOp = (char '*' >> return And)
       <|> (char '+' >> return Or)
       <|> (string "->" >> return Impl)
       <|> (string "<->" >> return Equiv)
       <?> "binary operator"


parens :: Parser Logic -> Parser Logic
parens = between (char '(') (char ')')


-- | Funkcja konwertujaca wyrazenie zapisane tekstowo
-- na reprezentacje uzywana w aplikacji.
parseLogic :: Text -> Either ParseError Logic
parseLogic = parse expr "" . T.filter (/=' ')

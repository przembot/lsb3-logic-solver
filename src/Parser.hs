{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
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


expr :: Parser Logic
expr = do
  x <- phrase
  (ops, exprs) <- unzip <$> many expr'
  let (_, [e]) = uncurry (mergeOp Equiv)
               . uncurry (mergeOp Impl)
               . uncurry (mergeOp Or)
               . mergeOp And ops $ (x:exprs)
  return e


expr' :: Parser (BinaryOp, Logic)
expr' = (,) <$> binaryOp <*> phrase


phrase :: Parser Logic
phrase = Not <$> (char '~' >> phrase)
     <|> C <$> (char 'C' >> parens expr)
     <|> parens expr
     <|> atom


atom :: Parser Logic
atom = constVal
   <|> var


constVal :: Parser Logic
constVal = (char 'T' >> return (Const TrueV))
       <|> (char 'N' >> return (Const Neither))
       <|> (char 'F' >> return (Const FalseV))


var :: Parser Logic
var = Var <$> lower


binaryOp :: Parser BinaryOp
binaryOp = (char '*' >> return And)
       <|> (char '+' >> return Or)
       <|> (string "->" >> return Impl)
       <|> (string "<->" >> return Equiv)


parens :: Parser Logic -> Parser Logic
parens = between (char '(') (char ')')


parseLogic :: Text -> Either ParseError Logic
parseLogic = parse expr "" . T.filter (/=' ')

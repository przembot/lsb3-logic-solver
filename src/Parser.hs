{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
module Parser (
  parseExp
  ) where

import Text.Parsec
import Text.Parsec.Expr
import Data.Text (Text)
import qualified Data.Text as T

import Logic

{-
Gramatyka

expr := expr binop expr
      | unop expr
      | "C(" expr ")"
      | "(" expr ")"
      | atom
      ;
binop := "*" | "+" | "->" | "<->" ;
unop := "~" ;
var := char ;
atom := T | N | F ;


bez lewej rekursji: (gramatyka LL(1))

expr := phrase {binop phrase}

phrase := unop phrase
        | "C(" expr ")"
        | "(" expr ")"
        | atom
        ;
binop := "*" | "+" | "->" | "<->" ;
unop := "~" ;
var := char ;
atom := T | N | F ;
-}

type Parser = Parsec Text ()

expr :: Parser Logic
expr = buildExpressionParser table term
     <?> "expression"

term :: Parser Logic
term = C <$> (char 'C' >> parens expr)
    <|> parens expr
    <|> constVal
    <|> var
    <?> "simple expression"

constVal :: Parser Logic
constVal = (char 'T' >> return (Const TrueV))
       <|> (char 'N' >> return (Const Neither))
       <|> (char 'F' >> return (Const FalseV))

var :: Parser Logic
var = Var <$> lower

table = [ [prefix "~" Not]
        , [binary "*" (BinForm And)]
        , [binary "+" (BinForm Or)]
        , [binary "->" (BinForm Impl), binary "<->" (BinForm Equiv)]
        ]

binary name fun = Infix (string name >> return fun) AssocLeft
prefix name fun = Prefix (string name >> return fun)

parens :: Parser Logic -> Parser Logic
parens = between (char '(') (char ')')

parseExp :: Text -> Either ParseError Logic
parseExp = parse expr "" . T.filter (/=' ')

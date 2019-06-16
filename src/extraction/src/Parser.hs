module Parser where

import Typing
import SimpleTypes
import Datatypes
import Data.Char
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

-- Grammar
                         
abst = do
      reservedOp "\\"
      v <- var
      reservedOp "->"
      e <- expr
      return $ Coq_lam_t (stringToCoq_id v)  e

letExpr = do
      reserved "let"
      id <- var
      reservedOp "="
      e1 <- expr
      reservedOp "in"
      e2 <- expr
      return $ Coq_let_t (stringToCoq_id id) e1 e2 

conInt = do
      _ <- integer
      return $ Coq_const_t O

table = [ [Infix (return (Coq_app_t)) AssocLeft] ]

expr :: Parser Coq_term
expr = buildExpressionParser table expr'

expr' = parens expr <|> abst
                    <|> conInt
                    <|> letExpr
                    <|> liftM (Coq_var_t . stringToCoq_id) var
                    
comma = do
        reservedOp ","
        return ()

pip = do
        reservedOp "|"
        return ()

stringToListNum256 s = map ord s
listNumBaseToNum256 l = sum $ zipWith (\a e -> a * 256 ^ e) l [0..(Prelude.length l)] 
num256ToListNumBase  n | n < 256  = [n]
                      | otherwise =  mod n 256 : num256ToListNumBase (n `div` 256)

numToCoq_id 0 = O::SimpleTypes.Coq_id
numToCoq_id n
         | n < 0 = O 
         | n > 0 = S (numToCoq_id (n-1))

coq_idToNum O = 0
coq_idToNum (S n) = 1 + coq_idToNum n

stringToCoq_id = numToCoq_id . listNumBaseToNum256 . stringToListNum256

-- Lex

languageDef = emptyDef { 
          Token.identStart      = lower
         , caseSensitive = True
         , Token.identLetter     = alphaNum
         , Token.reservedOpNames = ["\\", "->"]
         , Token.reservedNames = ["let", "in"]
         }

lexer = Token.makeTokenParser languageDef

var = Token.identifier lexer
parens     = Token.parens lexer
reservedOp = Token.reservedOp lexer
reserved   = Token.reserved lexer
integer    = Token.integer lexer

runParser s = parse expr "erro" s

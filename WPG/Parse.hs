{-# LANGUAGE FlexibleContexts #-}
module WPG.Parse(progParse) where

import Prelude
import Text.Parsec
import WPG.Prog_lang
import Data.Functor
import Data.Either
import Data.Functor.Identity

alpha = ['a'..'z'] ++ ['A'..'Z']
num = ['0'..'9']
specials = "_\'"
ws = " \n\r\t"

skipws :: Parsec String st a -> Parsec String st a
skipws p = skipws' *> p <* skipws'
    where
        skipws' = skipMany (oneOf ws)

varParse = skipws $ (:) <$> oneOf alpha <*> many (oneOf (alpha ++ num ++ specials))

pnumParse = read <$> many1 (oneOf num)

numParse = skipws $ char '-' *> (negate <$> pnumParse) <|> pnumParse

adParse = skipws $ char '+' $> Ad
suParse = skipws $ char '-' $> Su
muParse = skipws $ char '*' $> Mu
diParse = skipws $ char '/' $> Di

openPar = skipws $ char '('

closePar = skipws $ char ')'

aexpParse =
    addParse

addParse = chainl1 exp' oper
    where
        exp' = mulParse <|> between openPar closePar aexpParse
        oper = flip Op <$> (adParse <|> suParse)

mulParse = chainl1 exp' oper
    where
        exp' = atomParse <|> between openPar closePar aexpParse
        oper = flip Op <$> (muParse <|> diParse)

atomParse = try (N <$> numParse) <|> try (V <$> varParse)

bexpParse :: Parsec String st Bexp
bexpParse = try qParse <|> impParse

faParse = skipws $ string "forall" $> Uni
exParse = skipws $ string "exists" $> Exi

periodParse = skipws $ char '.'
commaParse = skipws $ char ','

qxParse = 
    try (faParse <*> varParse <* periodParse) <|>
    (exParse <*> varParse <* periodParse)

qParse = qxParse <*> bexpParse

negateParse = skipws $ char '~' $> Neg
implyParse = skipws $ string ">>" $> Imp
conjunctParse = skipws $ string "&" $> Con
disjunctParse = skipws $ string "|" $> Dis

impParse = chainr1 exp' oper
    where
        exp' = disParse <|> between openPar closePar bexpParse
        oper = implyParse

disParse = chainl1 exp' oper
    where
        exp' = conParse <|> between openPar closePar bexpParse
        oper = disjunctParse

conParse = chainl1 exp' oper
    where
        exp' = 
            try negParse <|> 
            try compParse <|> 
            try batomParse <|> 
            between openPar closePar bexpParse
        oper = conjunctParse

negParse = 
    negateParse <*> (
        try negParse <|> 
        try compParse <|> 
        try batomParse <|>
        between openPar closePar bexpParse)

batomParse = try (skipws $ string "true" $> Tru) <|> skipws (string "false" $> Fls)

eqParse = skipws $ string "==" $> Eq
ltParse = skipws $ string "<" $> Lt
gtParse = skipws $ string ">" $> Gt
leParse = skipws $ string "<=" $> Le
geParse = skipws $ string ">=" $> Ge

compopParse = try eqParse <|> try leParse <|> try geParse <|> try ltParse <|> gtParse

compParse = A <$> aexpParse <*> compopParse <*> aexpParse

openCrl = skipws $ char '{'
closeCrl = skipws $ char '}'

comParse = choiceParse

sqParse = skipws $ string ";" $> Seq
chParse = skipws $ string "[]" $> Choice
atParse = skipws $ string "|-" $> Assert
amParse = skipws $ string "-|" $> Assume
vrParse :: Parsec String st (String -> Com)
vrParse = skipMany (oneOf ws) *> string "var" *> oneOf ws $> Var
anParse = skipws $ string ":=" $> Assign
ghParse :: Parsec String st (Com -> Com)
ghParse = skipMany (oneOf ws) *> string "g" *> oneOf ws $> Ghost

choiceParse = chainr1 exp' oper
    where
        exp' = 
            try seqParse <|> 
            between openCrl closeCrl comParse
        oper = chParse

seqParse = chainr1 exp' oper
    where
        exp' = 
            try ghostParse <|> 
            try catomParse <|>
            between openCrl closeCrl comParse
        oper = sqParse

ghostParse = ghParse <*> (
    try ghostParse <|> 
    try catomParse <|>
    between openCrl closeCrl comParse)

catomParse = 
    try varcParse <|>
    try assumeParse <|>
    try assertParse <|>
    assignParse

varcParse = vrParse <*> varParse
assumeParse = amParse <*> bexpParse
assertParse = atParse <*> bexpParse


assignParse = varParse >>= (\s -> (($s) <$> anParse) <*> aexpParse)


openSqr = skipws $ char '['
closeSqr = skipws $ char ']'

progParse = (,) <$> between openSqr closeSqr (try varsParse <|> (skipMany (oneOf ws) $> [])) <*> comParse <* eof
    where
        varsParse = chainr1 ((:[]) <$> varParse) (commaParse $> (++))

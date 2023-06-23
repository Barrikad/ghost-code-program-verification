{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module
  WPG.Prog_lang(Aop(..), Acomp(..), Aexp(..), Bexp(..), Com(..), aexp_fv, bexp_fv,
             bsubst, fresh)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Word, Int, Integer, Show, negate, abs, divMod,
  Char, String, Bool(True, False), Maybe(Nothing, Just), otherwise, maximum, show, succ, flip);;
import qualified Prelude;
import Data.Set (Set,empty,singleton,insert,member,union,delete);

data Aop = Ad | Su | Mu | Di deriving Show;

data Acomp = Eq | Lt | Le | Gt | Ge deriving Show;

data Aexp = N Integer | V String | Op Aexp Aop Aexp deriving Show;

data Bexp = Tru | Fls | Neg Bexp | Con Bexp Bexp | Dis Bexp Bexp | Imp Bexp Bexp 
  | Uni String Bexp | Exi String Bexp | A Aexp Acomp Aexp deriving Show;

data Com = Assert Bexp | Assume Bexp | Var String | Assign String Aexp
  | Seq Com Com | Choice Com Com | Ghost Com deriving Show;

eql :: Aexp -> Aexp -> Bexp;
eql = flip A Eq ;

fresh :: Set String -> String;
fresh ss = fresh' 0 0
  where {
    letters = ['x'..'z'] ++ ['a'..'c'];
    fresh' :: Int -> Word -> String;
    fresh' x i 
      | not $ s `member` ss = s 
      | x + 1 < Prelude.length letters = fresh' (x + 1) i
      | otherwise = fresh' 0 (i + 1)
      where {
        s = (letters !! x):show i
      };
  };

asubst :: String -> Aexp -> Aexp -> Aexp;
asubst x a (N v) = N v;
asubst x a (V y) = if x == y then a else V y;
asubst x a (Op b p c) = Op (asubst x a b) p (asubst x a c);

aexp_fv :: Aexp -> Set String;
aexp_fv (N v) = empty;
aexp_fv (V y) = singleton y;
aexp_fv (Op b p c) = union (aexp_fv b) (aexp_fv c);

bexp_fv :: Bexp -> Set String;
bexp_fv (Neg p) = bexp_fv p;
bexp_fv (Con p q) = union (bexp_fv p) (bexp_fv q);
bexp_fv (Dis p q) = union (bexp_fv p) (bexp_fv q);
bexp_fv (Imp p q) = union (bexp_fv p) (bexp_fv q);
bexp_fv (Uni y p) = delete y (bexp_fv p);
bexp_fv (Exi y p) = delete y (bexp_fv p);
bexp_fv (A b p c) = union (aexp_fv b) (aexp_fv c);
bexp_fv _ = empty;

bsubst :: String -> Aexp -> Bexp -> Bexp;
bsubst x a (Neg p) = Neg (bsubst x a p);
bsubst x a (Con p q) = Con (bsubst x a p) (bsubst x a q);
bsubst x a (Dis p q) = Dis (bsubst x a p) (bsubst x a q);
bsubst x a (Imp p q) = Imp (bsubst x a p) (bsubst x a q);
bsubst x a (Uni y p)
  | x == y = Uni y p
  | member y (aexp_fv a) = 
    let {
        ya = fresh (union (insert x (aexp_fv a)) (bexp_fv p));
    } in Uni ya (bsubst x a (bsubst y (V ya) p))
  | otherwise = Uni y (bsubst x a p);
bsubst x a (Exi y p)
  | x == y = Exi y p
  | member y (aexp_fv a) = 
    let {
        ya = fresh (union (insert x (aexp_fv a)) (bexp_fv p));
    } in Exi ya (bsubst x a (bsubst y (V ya) p))
  | otherwise = Exi y (bsubst x a p);
bsubst x a (A v c w) = A (asubst x a v) c (asubst x a w);
bsubst _ _ x = x;

}

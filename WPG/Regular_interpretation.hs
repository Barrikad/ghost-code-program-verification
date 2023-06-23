{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module WPG.Regular_interpretation(uni_form,g_uni_form) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just), foldr);
import qualified Prelude;
import WPG.Prog_lang;
import Data.Set as S;

uni_form :: WPG.Prog_lang.Bexp -> [String] -> WPG.Prog_lang.Bexp;
uni_form = Prelude.foldr WPG.Prog_lang.Uni;

g_uni_form :: (String -> Bool) -> Bexp -> Bexp;
g_uni_form g p = uni_form p $ toList $ S.filter g $ bexp_fv p

}

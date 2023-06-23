{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module WPG.Weakest_precondition(wp, gwp, rwp, rc_pure, rc_obligs) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, Show, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Data.Set;
import qualified WPG.Prog_lang;
import qualified WPG.Regular_interpretation;
import WPG.Regular_interpretation (g_uni_form);

wp :: WPG.Prog_lang.Bexp -> WPG.Prog_lang.Com -> WPG.Prog_lang.Bexp;
wp q (WPG.Prog_lang.Assert r) = WPG.Prog_lang.Con r q;
wp q (WPG.Prog_lang.Assume r) = WPG.Prog_lang.Imp r q;
wp q (WPG.Prog_lang.Var x) = WPG.Prog_lang.Uni x q;
wp q (WPG.Prog_lang.Assign x a) = WPG.Prog_lang.bsubst x a q;
wp q (WPG.Prog_lang.Choice s1 s2) = WPG.Prog_lang.Con (wp q s1) (wp q s2);
wp q (WPG.Prog_lang.Seq s1 s2) = wp (wp q s2) s1;
wp q (WPG.Prog_lang.Ghost s) = wp q s;

gwp :: WPG.Prog_lang.Bexp -> WPG.Prog_lang.Com -> WPG.Prog_lang.Bexp;
gwp q (WPG.Prog_lang.Assert r) = q;
gwp q (WPG.Prog_lang.Assume r) = WPG.Prog_lang.Imp r q;
gwp q (WPG.Prog_lang.Var x) = WPG.Prog_lang.Uni x q;
gwp q (WPG.Prog_lang.Assign x a) = WPG.Prog_lang.bsubst x a q;
gwp q (WPG.Prog_lang.Choice s1 s2) = WPG.Prog_lang.Con (gwp q s1) (gwp q s2);
gwp q (WPG.Prog_lang.Seq s1 s2) = gwp (gwp q s2) s1;
gwp q (WPG.Prog_lang.Ghost s) = gwp q s;

rwp :: WPG.Prog_lang.Bexp -> WPG.Prog_lang.Com -> WPG.Prog_lang.Bexp;
rwp q (WPG.Prog_lang.Assert r) = WPG.Prog_lang.Con r q;
rwp q (WPG.Prog_lang.Assume r) = WPG.Prog_lang.Imp r q;
rwp q (WPG.Prog_lang.Var x) = WPG.Prog_lang.Uni x q;
rwp q (WPG.Prog_lang.Assign x a) = WPG.Prog_lang.bsubst x a q;
rwp q (WPG.Prog_lang.Choice s1 s2) = WPG.Prog_lang.Con (rwp q s1) (rwp q s2);
rwp q (WPG.Prog_lang.Seq s1 s2) = rwp (rwp q s2) s1;
rwp q (WPG.Prog_lang.Ghost s) = gwp q s;

rc_pure :: (String -> Bool) -> WPG.Prog_lang.Com -> Bool;
rc_pure g (WPG.Prog_lang.Assert b) =
  (not . any g) (WPG.Prog_lang.bexp_fv b);
rc_pure g (WPG.Prog_lang.Assume b) =
  (not . any g) (WPG.Prog_lang.bexp_fv b);
rc_pure g (WPG.Prog_lang.Var x) = not (g x);
rc_pure g (WPG.Prog_lang.Assign x a) =
  not (g x) && (not . any g) (WPG.Prog_lang.aexp_fv a);
rc_pure g (WPG.Prog_lang.Choice s1 s2) = rc_pure g s1 && rc_pure g s2;
rc_pure g (WPG.Prog_lang.Seq s1 s2) = rc_pure g s1 && rc_pure g s2;
rc_pure g (WPG.Prog_lang.Ghost s) = True;


rc_obligs :: (String -> Bool) -> WPG.Prog_lang.Bexp -> WPG.Prog_lang.Com -> [WPG.Prog_lang.Bexp];
rc_obligs g q (WPG.Prog_lang.Assert b) = [];
rc_obligs g q (WPG.Prog_lang.Assume b) = [];
rc_obligs g q (WPG.Prog_lang.Var x) = [];
rc_obligs g q (WPG.Prog_lang.Assign x a) = [];
rc_obligs g q (WPG.Prog_lang.Choice s1 s2) = rc_obligs g q s1 ++ rc_obligs g q s2;
rc_obligs g q (WPG.Prog_lang.Seq s1 s2) =
  rc_obligs g (WPG.Weakest_precondition.rwp q s2) s1 ++ rc_obligs g q s2;
rc_obligs g q (WPG.Prog_lang.Ghost s) = [WPG.Prog_lang.Imp (g_uni_form g (gwp q s)) q];


}

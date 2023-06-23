module WPG.Verify(typeCheck,hoareTriple) where

import Prelude
import WPG.Prog_lang
import WPG.Regular_interpretation
import WPG.Weakest_precondition
import Data.Set as S
import Data.Map as M
import Data.SBV
import Data.Functor as F
import Data.Maybe
import Control.Monad

gFromSet :: Ord a => Set a -> a -> Bool
gFromSet s = (`S.member` s)

data Q = U String | E String deriving Show

qName (U s) = s
qName (E s) = s

--will not rename bound variables to names in used
prenex :: Set String -> Bool ->  Bexp -> ([Q], Bexp)
prenex used s (Neg b) =
    let (qs,b') = prenex used (not s) b in
    (qs,Neg b')
prenex used s (Con b1 b2) =
    let (qs1,b1') = prenex used s b1
        (qs2,b2') = prenex (S.union used $ S.fromList $ Prelude.map qName qs1) s b2 in
    (qs1 ++ qs2, Con b1' b2')
prenex used s (Dis b1 b2) =
    let (qs1,b1') = prenex used s b1
        (qs2,b2') = prenex (S.union used $ S.fromList $ Prelude.map qName qs1) s b2 in
    (qs1 ++ qs2, Dis b1' b2')
prenex used s (Imp b1 b2) =
    let (qs1,b1') = prenex used (not s) b1
        (qs2,b2') = prenex (S.union used $ S.fromList $ Prelude.map qName qs1) s b2 in
    (qs1 ++ qs2, Imp b1' b2')
prenex used s (Uni x b) =
    let y = fresh used
        (qs,b') = prenex (S.insert y used) s (bsubst x (V y) b) in
    ((if s then U else E) y : qs, b')
prenex used s (Exi x b) =
    let y = fresh used
        (qs,b') = prenex (S.insert y used) s (bsubst x (V y) b) in
    ((if s then E else U) y : qs, b')
prenex used s a = ([],a)

type Env = M.Map String SInteger

envLookup :: String -> Env -> SInteger
envLookup s e = fromMaybe (error $ "Var not found: " ++ s) (M.lookup s e)

quantify :: Q -> Symbolic SInteger
quantify (U x) = sbvForall x
quantify (E x) = sbvExists x

--returns negated b
bexpToPredicate :: Bexp -> Predicate
bexpToPredicate b = do
    fv_syms <- mapM sbvForall lfv :: Symbolic [SInteger]
    qs_syms <- mapM quantify qs :: Symbolic [SInteger]
    let env = (M.fromList . zip (vs ++ qns)) (fv_syms ++ qs_syms)
    bToI env b'
    where
        fv = bexp_fv b
        lfv = S.toList fv
        (qs,b') = prenex fv True ( b)
        qns = Prelude.map qName qs
        vs = lfv ++ qns

        bToI :: Env -> Bexp -> Symbolic SBool
        bToI e Tru = return sTrue
        bToI e Fls = return sFalse
        bToI e (Neg b') = bToI e b' <&> sNot
        bToI e (Con b1 b2) = liftM2 (.&&) (bToI e b1) (bToI e b2)
        bToI e (Dis b1 b2) = liftM2 (.||) (bToI e b1) (bToI e b2)
        bToI e (Imp b1 b2) = liftM2 (.=>) (bToI e b1) (bToI e b2)
        bToI e (A a1 c a2) = liftM2 (cToF c) (aToI e a1) (aToI e a2)
        bToI e (Uni x b') = error "Not in prenex"
        bToI e (Exi x b') = error "Not in prenex"

        cToF :: Acomp -> SInteger -> SInteger -> SBool
        cToF Eq = (.==)
        cToF Lt = (.<)
        cToF Le = (.<=)
        cToF Gt = (.>)
        cToF Ge = (.>=)

        aToI :: Env -> Aexp -> Symbolic SInteger
        aToI e (N i) = return $ fromInteger i
        aToI e (V s) = return $ envLookup s e
        aToI e (Op a1 o a2) = liftM2 (oToF o) (aToI e a1) (aToI e a2)

        oToF :: Aop -> SInteger -> SInteger -> SInteger
        oToF Ad = (+)
        oToF Su = (-)
        oToF Mu = (*)
        oToF Di = sDiv

data VResult = Valid | Invalid | Undet deriving (Show, Eq)

vOr Valid _ = Valid
vOr _ Valid = Valid
vOr Undet _ = Undet
vOr _ Undet = Undet
vOr _ _ = Invalid

vAnd Valid Valid = Valid
vAnd Valid Undet = Undet
vAnd Undet Valid = Undet
vAnd Undet Undet = Undet
vAnd _ _ = Invalid

vAnds :: [VResult] -> VResult
vAnds = Prelude.foldr vAnd Valid

extractVResult :: ThmResult -> VResult
extractVResult (ThmResult r) = extractVResult' r
    where
        extractVResult' (Unsatisfiable _ _) = Valid
        extractVResult' (Satisfiable _ _) = Invalid
        extractVResult' DeltaSat {} = Invalid
        extractVResult' (SatExtField _ _) = Invalid
        extractVResult' _ = Undet

bexpProve :: Bexp -> IO VResult
bexpProve p =
    let r = prove (bexpToPredicate p) in
    extractVResult <$> r

typeCheck :: [String] -> Bexp -> Com -> IO Bool
typeCheck gs q c =
    let g = (`S.member` S.fromList gs)
        os = rc_obligs g q c
        ors = mapM bexpProve os
        or = ors <&> vAnds
        isPure = rc_pure g c in
    do
        putStrLn $ "Is pure?: " ++ show isPure
        putStrLn $ "Checking obligs: " ++ show os
        putStr "Obligs result: "
        ors >>= print
        fmap (isPure &&) (or <&> (==Valid))

hoareTriple :: Bexp -> Com -> Bexp -> IO Bool
hoareTriple p c q =
    let oblig = Imp p (wp q c)
        or = bexpProve oblig in
    do
        putStrLn $ "Checking oblig: " ++ show oblig
        putStr "Obligs result: "
        or >>= print
        or <&> (== Valid)

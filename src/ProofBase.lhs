\begin{code}
module ProofBase where

import Term
import Environment as Env
import Substitution as Subst
import Evaluation as Eval
import ProofSearch
import Util

import Prelude hiding (lookup)
import Control.Applicative
import Control.Monad

import Data.Monoid
import Data.List
import Data.Maybe

import Data.Map (Map)
import qualified Data.Map as Map

import Debug.Trace

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

-- ProofBase

data ProofBase = ProofBase
  { proofBaseFull     :: Map Term [(Term, [Term])]
  , proofBaseSkeleton :: Map TermSkeleton [(Term, Int, [TermSkeleton])]
  }

instance Show ProofBase where
  show (ProofBase bFull _) = mconcat $ (\(key,dat) -> "\n" ++ show key <+> mconcat (("\n\t" ++) . show . snd <$> dat)) <$> Map.toList bFull

empty :: ProofBase
empty = ProofBase Map.empty Map.empty

insertProofItem :: ProofSearchItem -> Term -> ProofBase -> ProofBase
insertProofItem item@(ProofSearchItem env t) prf base@(ProofBase bFull bSkel) =
  let pIsom = proofSearchItemIsomorphism item in
  let pTerm = isomorphismMemberType t in
  let pEnv = isomorphismMemberType <$> env in
  let lIndex = maybe 0 length $ Map.lookup pTerm bFull in
  let prf' = Application (isomorphismTo pIsom) prf in
  let fEntry = (prf', pEnv) in
  let sEntry = (pTerm, lIndex, skeleton <$> pEnv) in
  ProofBase
    (Map.alter (Just . maybe [fEntry] (++ [fEntry])) pTerm bFull)
    (Map.alter (Just . maybe [sEntry] (++ [sEntry])) (skeleton pTerm) bSkel)

insertProof :: Term -> Term -> ProofBase -> ProofBase
insertProof prop proof base =
  case runEC $ do
    propTy <- typecheck Env.empty prop
    unify Env.empty propTy SetType
    prop' <- normalise Env.empty prop
    proofTy <- typecheck Env.empty proof
    unify Env.empty proofTy prop
    return prop'
  of
    Right prop' -> case runPC $ proofSearch Env.empty prop' of
      Right (ProofSearch isom pItems) ->
        let pTaus = uncurry liftBy <$> zip [0..] (isomorphismMemberType . proofSearchItemIsomorphism <$> pItems) in
        foldr (uncurry insertProofItem) base $ zip pItems (($ Application (isomorphismTo isom) proof) <$> (Application . tupleProjection pTaus) <$> [0..]) -- TODO : change id
      Left err -> traceShow err $ base
    Left err -> traceShow err $ base

insertProofList :: ProofBase -> [(Term, Term)] -> ProofBase
insertProofList = foldr (uncurry insertProof)


-- Bad. TODO : lift all environment term on the same level, so as to avoid comparisons between -> Variables (1-le1) / (1-le2) denote environment variables. 
-- TODO : add a binding between the variables if we choose to bind them together. Only used in binding recollection for proof reconstructions.

lookupProofItem :: ProofSearchItem -> ProofBase -> Maybe Term
lookupProofItem item@(ProofSearchItem env t) base@(ProofBase bFull bSkel) =
  let pIsom = proofSearchItemIsomorphism item in
  let pTerm = isomorphismMemberType t in
  let pEnv = isomorphismMemberType <$> env in
  let pSkelEnv = skeleton <$> pEnv in do
    candidates <- Map.lookup (skeleton pTerm) bSkel
    listToMaybe . catMaybes . flip fmap candidates $ \(cTerm, cId, cSkel) -> do
      skeletonSubList pSkelEnv cSkel -- Should filter most
      (cIsom, cEnv) <- (!! cId) <$> Map.lookup cTerm bFull
      let lpEnv = (uncurry liftBy) <$> zip [1..] pEnv
      let lcEnv = (uncurry liftBy) <$> zip [1..] cEnv
      bindings <- bindingsFrom 0 pTerm cTerm
      fBindings <- fullSubList bindings 1 lpEnv 1 lcEnv
      traceShow fBindings $ return SetType

  where
    skeletonSubList :: [TermSkeleton] -> [TermSkeleton] -> Maybe ()
    skeletonSubList _ []             = Just ()
    skeletonSubList [] (_:_)         = Nothing
    skeletonSubList (x:xs) (y:ys)
      | x == y                       = skeletonSubList xs ys
      | otherwise                    = skeletonSubList xs (y:ys)

    fullSubList :: Map Int Int -> Int -> [Term] -> Int -> [Term] -> Maybe (Map Int Int)
    fullSubList bindings i _ j []                 = Just bindings
    fullSubList bindings i [] j (_:_)             = Nothing
    fullSubList bindings i (x:xs) j (y:ys)
      | skeleton x == skeleton y                  = listToMaybe . catMaybes $
        [ do
            nBindings <- bindingsFrom 0 x y
            aBindings <- bindingsUnions [bindings, nBindings, Map.singleton i j]
            fullSubList aBindings (i+1) xs (j+1) ys
        , fullSubList bindings (i+1) xs j (y:ys)
        ]
      | otherwise                                 = fullSubList bindings (i+1) xs j (y:ys)

    bindingsFrom :: Int -> Term -> Term -> Maybe (Map Int Int)
    bindingsFrom i (Variable j1) (Variable j2)
      | j1 >= i && j2 >= i                                                               = Just (Map.singleton (j1-i) (j2-i))
      | j1 < i && j2 < i                                                                 = Just Map.empty
      | otherwise                                                                        = Nothing
    bindingsFrom i (Application f1 t1) (Application f2 t2)                               = (bindingsUnions =<<) $ sequence $ [bindingsFrom i f1 f2, bindingsFrom i t1 t2]
    bindingsFrom i SetType SetType                                                       = Just Map.empty
    bindingsFrom i (Abstraction tau1 t1) (Abstraction tau2 t2)                           = (bindingsUnions =<<) $ sequence $ [bindingsFrom i tau1 tau2, bindingsFrom (i + 1) t1 t2]
    bindingsFrom i (FunctionType tau1 sigma1) (FunctionType tau2 sigma2)                 = (bindingsUnions =<<) $ sequence $ [bindingsFrom i tau1 tau2, bindingsFrom (i + 1) sigma1 sigma2]
    bindingsFrom i (TupleType taus1) (TupleType taus2)                                   = (bindingsUnions =<<) $ sequence $ (uncurry3 bindingsFrom <$> zip3 [i..] taus1 taus2)
    bindingsFrom i (TupleConstruct taus1 ts1) (TupleConstruct taus2 ts2)                 = (bindingsUnions =<<) $ sequence $ (uncurry3 bindingsFrom <$> zip3 [i..] taus1 taus2) ++ (uncurry (bindingsFrom i) <$> zip ts1 ts2)
    bindingsFrom i (TupleDestruct taus1 sigma1 f1) (TupleDestruct taus2 sigma2 f2)       = (bindingsUnions =<<) $ sequence $ (uncurry3 bindingsFrom <$> zip3 [i..] taus1 taus2) ++ [bindingsFrom i sigma1 sigma2, bindingsFrom i f1 f2]
    bindingsFrom i (TupleIdentity taus1 t1) (TupleIdentity taus2 t2)                     = (bindingsUnions =<<) $ sequence $ (uncurry3 bindingsFrom <$> zip3 [i..] taus1 taus2) ++ [bindingsFrom i t1 t2]
    bindingsFrom i (CoTupleType taus1) (CoTupleType taus2)                               = (bindingsUnions =<<) $ sequence $ (uncurry (bindingsFrom i) <$> zip taus1 taus2)
    bindingsFrom i (CoTupleConstruct taus1 j1 t1) (CoTupleConstruct taus2 j2 t2)         = (bindingsUnions =<<) $ sequence $ (uncurry (bindingsFrom i) <$> zip taus1 taus2) ++ [bindingsFrom i t1 t2]
    bindingsFrom i (CoTupleDestruct taus1 sigma1 fs1) (CoTupleDestruct taus2 sigma2 fs2) = (bindingsUnions =<<) $ sequence $ (uncurry (bindingsFrom i) <$> zip taus1 taus2) ++ [bindingsFrom i sigma1 sigma2] ++ (uncurry (bindingsFrom i) <$> zip fs1 fs2)
    bindingsFrom i (IdentityType tau1 x1 y1) (IdentityType tau2 x2 y2)                   = (bindingsUnions =<<) $ sequence $ [bindingsFrom i tau1 tau2, bindingsFrom i x1 x2, bindingsFrom i y1 y2]
    bindingsFrom i (IdentityReflective tau1 x1) (IdentityReflective tau2 x2)             = (bindingsUnions =<<) $ sequence $ [bindingsFrom i tau1 tau2, bindingsFrom i x1 x2]
    bindingsFrom i (IdentityDestruct tau1 x1 y1) (IdentityDestruct tau2 x2 y2)           = (bindingsUnions =<<) $ sequence $ [bindingsFrom i tau1 tau2, bindingsFrom i x1 x2, bindingsFrom i y1 y2]
    bindingsFrom i NatType NatType                                                       = Just Map.empty
    bindingsFrom i NatZ NatZ                                                             = Just Map.empty
    bindingsFrom i NatS NatS                                                             = Just Map.empty
    bindingsFrom i (NatInduction tau1 f1 x1) (NatInduction tau2 f2 x2)                   = (bindingsUnions =<<) $ sequence $ [bindingsFrom i tau1 tau2, bindingsFrom i f1 f2, bindingsFrom i x1 x2]

    bindingsUnion :: Map Int Int -> Map Int Int -> Maybe (Map Int Int)
    bindingsUnion b1 b2
      | all (== True) . Map.elems $ Map.intersectionWith (==) b1 b2    = Just $ Map.union b1 b2
      | otherwise                                                      = Nothing
    bindingsUnions :: [Map Int Int] -> Maybe (Map Int Int)
    bindingsUnions                                                     = foldr (\x -> (>>= bindingsUnion x)) (Just Map.empty)


lookupProof :: Term -> ProofBase -> Maybe Term
lookupProof prop base =
  case runEC $ do
    propTy <- typecheck Env.empty prop
    unify Env.empty propTy SetType
    normalise Env.empty prop
  of
    Right prop' -> case runPC $ proofSearch Env.empty prop' of
      Right (ProofSearch isom pItems) -> do
        pItems' <- forM pItems $ \pItem -> lookupProofItem pItem base
        traceShow pItems' $ return ()
        Nothing -- return $ Application (isomorphismFrom isom) $ TupleConstruct (uncurry liftBy <$> (zip [0..] $ isomorphismMemberType . proofSearchItemIsomorphism <$> pItems)) pItems'
      Left err -> traceShow err $ Nothing
    Left err -> traceShow err $ Nothing

\end{code}
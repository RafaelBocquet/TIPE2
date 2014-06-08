\begin{code}
module ProofBase where

import Term
import Environment as Env
import Substitution as Subst
import Evaluation as Eval
import ProofSearch

import Prelude hiding (lookup)
import Control.Applicative
import Control.Monad

import Data.Monoid
import Data.List

import Data.Map (Map)
import qualified Data.Map as Map

import Debug.Trace

-- ProofBase

data ProofBase = ProofBase
  { proofBaseFull     :: Map Term [(Term, [Term])]
  , proofBaseSkeleton :: Map TermSkeleton [(Term, Int, [TermSkeleton])]
  }
  deriving (Show)

--insertProofSearch :: ProofBase -> ProofSearch -> ProofBase
--insertProofSearch (ProofBase bFull bSkel) (ProofSearch t (Environment env)) =
--  let env' = 

empty :: ProofBase
empty = ProofBase Map.empty Map.empty

insertProofItem :: ProofSearchItem -> Term -> ProofBase -> ProofBase
insertProofItem item@(ProofSearchItem env t) prf base@(ProofBase bFull bSkel) =
  let pIsom = proofSearchItemIsomorphism item in
  let pTerm = isomorphismMemberType t in
  let pEnv = isomorphismMemberType <$> env in
  let lIndex = maybe 0 length $ Map.lookup pTerm bFull in
  let fEntry = (Application (isomorphismTo pIsom) prf, pEnv) in
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
      Right (ProofSearch _ pItems) ->
        foldr insertProofItem base pItems -- TupleProjecttion + zip
      Left err -> traceShow err $ base
    Left err -> traceShow err $ base

lookupProof :: Term -> ProofBase -> Maybe Term
lookupProof _ _ = Nothing

insertProofList :: ProofBase -> [(Term, Term)] -> ProofBase
insertProofList = foldr (\(prop, proof) base -> insertProof base prop proof)

\end{code}
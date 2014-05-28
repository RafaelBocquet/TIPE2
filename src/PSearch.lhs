\begin{code}
module PSearch where

import Expression as Expr
import Environment as Env
import Evaluation

import Control.Applicative
import Control.Monad

import Control.Monad.Trans.Either
import Control.Monad.Error.Class
import Control.Monad.Identity

import Text.Dot
import Debug.Trace

import qualified Data.Set as Set
import qualified Data.Map as Map

data PNError = PNError | PNTCError TCError
  deriving(Eq, Show)

type PN a = EitherT PNError Identity a

runPN :: PN a -> Either PNError a
runPN = runIdentity . runEitherT

pnOfTC :: TC a -> PN a
pnOfTC = either (throwError . PNTCError) return . runTC

data PExpression = PExpression Environment Expression
  deriving(Eq, Show)

--expressionOfPExpression :: PExpression -> Expression
--expressionOfPExpression = 

showDotPExpression :: PExpression -> String
showDotPExpression (PExpression (Environment env) t) = showDot $ do
  endNode <- node [("label", showLatexExpression t), ("color", "red")]
  iNodes <- flip mapM env $ \tau -> do {nId <- node [("label", showLatexExpression tau)]; return (tau, nId)}
  forM_ ((t,endNode):iNodes) $ \(tau, nId) ->
    forM_ (Set.elems $ dependencies 0 tau) $ \mId ->
      edge (snd $ iNodes !! mId) nId []

pNormalise :: Expression -> PN PExpression
pNormalise e = (pNormalise' Env.empty e) >>= pNormaliseSort
  where
    pNormalise' :: Environment -> Expression -> PN PExpression
    pNormalise' gamma e = do
      whnfE <- pnOfTC $ do
        eTy <- typecheck gamma e
        unify gamma eTy SetType
        normaliseHead gamma e
        return e
      case whnfE of
        Variable i -> return $ PExpression gamma (Variable i)
        SetType -> return $ PExpression gamma SetType
        Abstraction _ _ -> throwError PNError
        Application f t -> return $ PExpression gamma (Application f t)
        FunctionType tau sigma -> do
          -- tau' <- pNormalise gamma tau
          pNormalise' (tau `bind` gamma) sigma
        _ -> throwError PNError
    pNormaliseSort :: PExpression -> PN PExpression
    pNormaliseSort (PExpression (Environment env) e') = do
      let deps      = dependencies 0 <$> env
      let revDeps   = flip fmap [0 .. length env - 1] $ \i -> Set.fromList $ fmap fst $ filter (Set.member i . snd) $ zip [0..] deps
      let sortPerm  = topSort env . Map.fromList $ zip [0..] revDeps
      return $ PExpression (Env.applyPermutation (Environment env) sortPerm) $ (Expr.applyPermutation 0 sortPerm e')
      --traceShow revDeps $ trace (" --- " ++ show sortPerm) $ 
      --  throwError PNError
    topSort :: [Expression] -> Map.Map Int (Set.Set Int) -> [Int]
    topSort env revDeps =
      if Map.null revDeps
        then []
        else
          let nEdge = minimum' env . Map.keys . Map.filter ((==) Set.empty) $ revDeps in nEdge : (topSort env . fmap (Set.delete nEdge) $ Map.delete nEdge revDeps)
    minimum' :: [Expression] -> [Int] -> Int
    minimum' _ [x] = x
    minimum' env (x:xs)
      | (env !! x) < (env !! minimum' env xs)   = x
      | otherwise                               = minimum' env xs

\end{code}


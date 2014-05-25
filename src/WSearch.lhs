\begin{code}
module WSearch where

import Expression
import Environment as Env
import Evaluation

import Control.Applicative
import Control.Monad

import Control.Monad.Trans.Either
import Control.Monad.Error.Class
import Control.Monad.Identity

import Text.Dot

import qualified Data.Set as Set

data WCError = WCError | WCTCError TCError
  deriving(Eq, Show)

type WC a = EitherT WCError Identity a

runWC :: WC a -> Either WCError a
runWC = runIdentity . runEitherT

wcOfTC :: TC a -> WC a
wcOfTC = either (throwError . WCTCError) return . runTC

data WExpression = WExpression Environment Expression
  deriving(Eq, Show)

showDotWExpression :: WExpression -> String
showDotWExpression (WExpression (Environment env) t) = showDot $ do
  endNode <- node [("label", showLatexExpression t)]
  iNodes <- flip mapM env $ \tau -> do {nId <- node [("label", showLatexExpression tau)]; return (tau, nId)}
  forM_ ((t,endNode):iNodes) $ \(tau, nId) ->
    forM_ (Set.elems $ dependencies 0 tau) $ \(mId) ->
      edge (snd $ iNodes !! mId) nId []

wNormalise :: Environment -> Expression -> WC WExpression
wNormalise gamma e = do
  whnfE <- wcOfTC $ do
    eTy <- typecheck gamma e
    unify gamma eTy SetType
    normaliseHead gamma e
  case whnfE of
    Variable i -> return $ WExpression Env.empty (Variable i)
    SetType -> return $ WExpression Env.empty SetType
    Abstraction _ _ -> throwError WCError
    FunctionType tau sigma -> do
      -- tau' <- wNormalise gamma tau
      WExpression (Environment sigmaL) sigma' <- wNormalise (tau `bind` gamma) sigma
      return $ WExpression (Environment $ tau : sigmaL) sigma'
    _ -> throwError WCError


\end{code}

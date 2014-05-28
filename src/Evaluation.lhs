\begin{code}
module Evaluation where

import Expression
import Environment
import Util

import Prelude hiding (lookup)
import Control.Applicative
import Control.Monad

import Control.Monad.Trans.Either
import Control.Monad.Error.Class
import Control.Monad.Identity

import Debug.Trace

data TCError =
    OtherError String
  | FreeVariable
  | UnificationFailure Environment Expression Expression
  | ExceptedFunction Expression
  | UnifyErrorTrace Environment Expression Expression TCError
  | TypecheckErrorTrace Environment Expression TCError
  deriving(Eq)

instance Show TCError where
  show (OtherError s)                    = "\n\t" ++ red "OtherError" ++ " : " ++ s
  show FreeVariable                      = "\n\t" ++ red "FreeVariable"
  show (ExceptedFunction ty)             = "\n\t" ++ red "ExceptedFunction : got " ++ show ty
  show (UnificationFailure gamma e1 e2)        = "\n\t" ++ red "Can't unify" ++ " (" ++ show e1 ++ ") " ++ red "\n\t\twith" ++ " (" ++ show e2 ++ ") " ++ red "\n\t\tin " ++ show gamma
  show (UnifyErrorTrace gamma e1 e2 err)       = "\n\t" ++ red "In unification of" ++ " (" ++ show e1 ++ ") " ++ red "\n\t\twith" ++ " (" ++ show e2 ++ ") " ++ red "\n\t\tin " ++ show gamma ++ " : " ++ show err
  show (TypecheckErrorTrace gamma e err) = "\n\t" ++ red "When typechecking" ++ " (" ++ show e ++ ") " ++ red "\n\t\tin " ++ show gamma ++ " : " ++ show err

type TC a = EitherT TCError Identity a

runTC :: TC a -> Either TCError a
runTC = runIdentity . runEitherT

-- Unification
-- Tries not to fully evaluate the expressions when possible
-- Returns the unified expression
unify :: Environment -> Expression -> Expression -> TC Expression
unify gamma e1 e2
  | e1 == e2 = return e1
  | otherwise = do
      e'1 <- normaliseHead gamma e1
      e'2 <- normaliseHead gamma e2
      unify' gamma e'1 e'2
    `catchError` (throwError . UnifyErrorTrace gamma e1 e2)
  where
    unify' gamma (Abstraction tau t) (Abstraction sigma s) = do
      tau' <- unify gamma tau sigma
      t' <- unify (tau' `bind` gamma) t s
      return $ Abstraction tau' t'
    unify' gamma (FunctionType tau sigma) (FunctionType upsilon omega) = do
      tau' <- unify gamma tau upsilon
      sigma' <- unify (tau' `bind` gamma) sigma omega
      return $ Abstraction tau' sigma'
    unify' gamma e1 e2 = throwError $ UnificationFailure gamma e1 e2

-- Normalisation in WHNF of a typechecked expression
normaliseHead :: Environment -> Expression -> TC Expression
normaliseHead gamma (Renaming str t) = normaliseHead gamma t
normaliseHead gamma (Application f t)                    = do
  f' <- normaliseHead gamma f
  case f' of
    Abstraction tau e -> normaliseHead gamma $ substitute 0 t e
    Variable i -> return $ Application (Variable i) t
    _ -> throwError $ OtherError $ show f'
normaliseHead gamma e                                    = return e

-- Full Normalisation
normalise :: Environment -> Expression -> TC Expression
normalise gamma e = throwError $ OtherError "Unimplemented !"

-- Typechecks an expression
typecheck :: Environment -> Expression -> TC Expression
typecheck gamma e = typecheck' gamma e `catchError` (throwError . TypecheckErrorTrace gamma e)
  where
    typecheck' gamma (Variable i)                         = maybe (throwError FreeVariable) return $ lookup gamma i
    typecheck' gamma (Application f t)                    = do
      fTy <- typecheck gamma f
      fTy <- normaliseHead gamma fTy
      tTy <- typecheck gamma t
      case fTy of
        FunctionType tau sigma -> do
          unify gamma tTy tau
          return $ substitute 0 t sigma
        _ -> throwError $ ExceptedFunction fTy
    typecheck' gamma SetType                              = return SetType
    typecheck' gamma (Abstraction tau t)                  = do
      tauTy <- typecheck gamma tau
      unify gamma tauTy SetType
      tTy <- typecheck (tau `bind` gamma) t
      return $ FunctionType tau tTy
    typecheck' gamma (FunctionType tau sigma)             = do
      tauTy <- typecheck gamma tau
      unify gamma tauTy SetType
      sigmaTy <- typecheck (tau `bind` gamma) sigma
      unify (tau `bind` gamma) sigmaTy SetType
      return SetType
    typecheck' gamma (Renaming str t) = typecheck' gamma t

\end{code}
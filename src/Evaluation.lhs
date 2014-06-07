\begin{code}
module Evaluation where

import Term
import Environment as Env
import Substitution as Subst
import Util

import Prelude hiding (lookup)
import Control.Applicative
import Control.Monad

import Control.Monad.Trans.Either
import Control.Monad.Error.Class
import Control.Monad.Identity

import Debug.Trace

-- Error

data ECError =
    OtherError String
  | FreeVariable Int
  | UnificationFailure Environment Term Term
  | ExceptedFunction Term
  | UnifyErrorTrace Environment Term Term ECError
  | TypecheckErrorTrace Environment Term ECError

instance Show ECError where
  show (OtherError s)                          = "\n\t" ++ red "OtherError" <+> ":" <+> s
  show (FreeVariable i)                        = "\n\t" ++ red "FreeVariable" <+> show i
  show (ExceptedFunction ty)                   = "\n\t" ++ red "ExceptedFunction : got" <+> show ty
  show (UnificationFailure gamma e1 e2)        = "\n\t" ++ red "Can't unify" <+> "(" ++ show e1 ++ ")" ++ red "\n\t\twith" <+> "(" ++ show e2 ++ ")" ++ red "\n\t\tin" <+> show gamma
  show (UnifyErrorTrace gamma e1 e2 err)       = "\n\t" ++ red "In unification of" <+> "(" ++ show e1 ++ ")" ++ red "\n\t\twith" <+> "(" ++ show e2 ++ ")" ++ red "\n\t\tin " ++ show gamma ++ " : " ++ show err
  show (TypecheckErrorTrace gamma e err)       = "\n\t" ++ red "When typechecking" <+> "(" ++ show e ++ ")" ++ red "\n\t\tin" <+> show gamma <+> ":" <+> show err

-- Monad

type EC a = EitherT ECError Identity a

runEC :: EC a -> Either ECError a
runEC = runIdentity . runEitherT

-- Unification

unify :: Environment -> Term -> Term -> EC Term
unify gamma e1 e2 = do
    e1' <- normaliseHead gamma e1
    e2' <- normaliseHead gamma e2
    if e1' == e2'
      then return e1'
      else (unify' gamma e1' e2') `catchError` (throwError . UnifyErrorTrace gamma e1 e2)
  where
    unify' gamma (Application f1 t1) (Application f2 t2)                               = do
      f' <- unify gamma f1 f2
      t' <- unify gamma t1 t2
      return $ Application f' t'
    unify' gamma (Abstraction tau1 t1) (Abstraction tau2 t2)                           = do
      tau' <- unify gamma tau1 tau2
      t' <- unify (tau' `Env.bind` gamma) t1 t2
      return $ Abstraction tau' t'
    unify' gamma (FunctionType tau1 sigma1) (FunctionType tau2 sigma2)                 = do
      tau' <- unify gamma tau1 tau2
      sigma' <- unify (tau' `Env.bind` gamma) sigma1 sigma2
      return $ FunctionType tau' sigma'
    unify' gamma (TupleType taus1) (TupleType taus2)                                   = do
      TupleType . snd <$> foldM (\(gamma', taus') (tau1, tau2) -> do
          tau' <- unify gamma' tau1 tau2
          return $ (tau' `Env.bind` gamma, tau' : taus')
        ) (gamma, []) (zip taus1 taus2)
    unify' gamma (TupleConstruct taus1 ts1) (TupleConstruct taus2 ts2)                 = do
      uncurry TupleConstruct . snd <$> foldM (\(gamma', (taus', ts')) ((tau1, t1), (tau2, t2)) -> do
          tau' <- unify gamma' tau1 tau2
          t' <- unify gamma' t1 t2
          return $ (tau' `Env.bind` gamma, (tau' : taus', t' : ts'))
        ) (gamma, ([], [])) (zip (zip taus1 ts1) (zip taus2 ts2))
    unify' gamma (TupleDestruct taus1 sigma1 f1) (TupleDestruct taus2 sigma2 f2)       = do
      taus' <- snd <$> foldM (\(gamma', taus') (tau1, tau2) -> do
          tau' <- unify gamma' tau1 tau2
          return $ (tau' `Env.bind` gamma, tau' : taus')
        ) (gamma, []) (zip taus1 taus2)
      sigma' <- unify gamma sigma1 sigma2
      f' <- unify gamma f1 f2
      return $ TupleDestruct taus' sigma' f'
    unify' gamma (TupleIdentity taus1 t1) (TupleIdentity taus2 t2)                     = do
      taus' <- snd <$> foldM (\(gamma', taus') (tau1, tau2) -> do
          tau' <- unify gamma' tau1 tau2
          return $ (tau' `Env.bind` gamma, tau' : taus')
        ) (gamma, []) (zip taus1 taus2)
      t' <- unify gamma t1 t2
      return $ TupleIdentity taus' t'
    unify' gamma (CoTupleType taus1) (CoTupleType taus2)                               = do
      CoTupleType <$> mapM (uncurry $ unify gamma) (zip taus1 taus2)
    unify' gamma e1@(CoTupleConstruct taus1 j1 t1) e2@(CoTupleConstruct taus2 j2 t2)
      | j1 == j2                                                                       = do
        taus' <- mapM (uncurry $ unify gamma) (zip taus1 taus2)
        t' <- unify gamma t1 t2
        return $ CoTupleConstruct taus' j1 t'
      | otherwise                                                                      = throwError $ UnificationFailure gamma e1 e2
    unify' gamma (CoTupleDestruct taus1 sigma1 fs1) (CoTupleDestruct taus2 sigma2 fs2) = do
      taus' <- mapM (uncurry $ unify gamma) (zip taus1 taus2)
      sigma' <- unify (CoTupleType taus' `Env.bind` gamma) sigma1 sigma2
      fs' <- mapM (uncurry $ unify gamma) (zip fs1 fs2)
      return $ CoTupleDestruct taus' sigma' fs'
    unify' gamma (IdentityType tau1 x1 y1) (IdentityType tau2 x2 y2) = do
      tau' <- unify gamma tau1 tau2
      x' <- unify gamma x1 x2
      y' <- unify gamma y1 y2
      return $ IdentityType tau' x' y'
    unify' gamma (IdentityReflective tau1 x1) (IdentityReflective tau2 x2) = do
      tau' <- unify gamma tau1 tau2
      x' <- unify gamma x1 x2
      return $ IdentityReflective tau' x'
    unify' gamma (IdentityDestruct tau1 x1 y1) (IdentityDestruct tau2 x2 y2) = do
      tau' <- unify gamma tau1 tau2
      x' <- unify gamma x1 x2
      y' <- unify gamma y1 y2
      return $ IdentityDestruct tau' x' y'
    unify' gamma (NatInduction tau1 f1 x1) (NatInduction tau2 f2 x2) = do
      tau' <- unify gamma tau1 tau2
      f' <- unify gamma f1 f2
      x' <- unify gamma x1 x2
      return $ NatInduction tau' f' x'
    unify' gamma e1 e2 = throwError $ UnificationFailure gamma e1 e2
-- Normalisation (term must be valid)

normaliseHead :: Environment -> Term -> EC Term
normaliseHead gamma (Variable i)                                      = return $ Variable i
normaliseHead gamma (Application (Abstraction tau e) t)               = normaliseHead gamma $ substitute (Subst.single t) e
normaliseHead gamma e@(Application (TupleDestruct taus sigma f) t)    = do
  t' <- normaliseHead gamma t
  case t' of
    TupleConstruct _ ts ->
      normaliseHead gamma $ applicationList f ts
    otherwise ->
      return e
normaliseHead gamma e@(Application (CoTupleDestruct taus sigma fs) t) = do
  t' <- normaliseHead gamma t
  case t' of
    CoTupleConstruct _ j t ->
      normaliseHead gamma $ Application (fs !! j) t
    otherwise ->
      return e
normaliseHead gamma (Application (Application (Application (IdentityDestruct tau x y) prf) p) px) = do
  return px
normaliseHead gamma (Application e@(NatInduction tau f t) n@(Application NatS n')) = do
  normaliseHead gamma (Application (Application f n) (Application e n'))
normaliseHead gamma (Application (NatInduction tau f t) NatZ) = do
  return t
normaliseHead gamma e@(Application f t)                               = return e
normaliseHead gamma SetType                                           = return SetType
normaliseHead gamma e@(Abstraction tau t)                             = return e
normaliseHead gamma e@(FunctionType tau sigma)                        = return e
normaliseHead gamma e@(TupleType taus)                                = return e
normaliseHead gamma e@(TupleConstruct taus ts)                        = return e
normaliseHead gamma e@(TupleDestruct taus sigma f)                    = return e
normaliseHead gamma e@(TupleIdentity taus t)                          = return e
normaliseHead gamma e@(CoTupleType taus)                              = return e
normaliseHead gamma e@(CoTupleConstruct taus j t)                     = return e
normaliseHead gamma e@(CoTupleDestruct taus sigma fs)                 = return e
normaliseHead gamma e@(IdentityType tau x y)                          = return e
normaliseHead gamma e@(IdentityReflective tau x)                      = return e
normaliseHead gamma e@(IdentityDestruct tau x y)                      = return e
normaliseHead gamma NatType                                           = return NatType
normaliseHead gamma NatZ                                              = return NatZ
normaliseHead gamma NatS                                              = return NatS
normaliseHead gamma e@(NatInduction tau f x)                          = return e

normalise :: Environment -> Term -> EC Term
normalise gamma e = normalise' =<< (normaliseHead gamma e)
  where
    normalise' e@(Variable i)                       = return e
    normalise' (Application f t)                    = do
      f' <- normalise gamma f
      t' <- normalise gamma t
      return $ Application f' t'
    normalise' SetType                              = return SetType
    normalise' (Abstraction tau t)                  = do
      tau' <- normalise gamma tau
      t' <- normalise (tau' `Env.bind` gamma) t
      return $ Abstraction tau' t'
    normalise' (FunctionType tau sigma)             = do
      tau' <- normalise gamma tau
      sigma' <- normalise (tau' `Env.bind` gamma) sigma
      return $ FunctionType tau' sigma'
    normalise' (TupleType taus) =
      TupleType . snd <$> foldM (\(gamma', taus') tau -> do
          tau' <- normalise gamma' tau
          return (tau `Env.bind` gamma, tau' : taus') 
        ) (gamma, []) taus
    normalise' (TupleConstruct taus ts)             = do
      TupleType taus' <- normalise gamma $ TupleType taus
      ts' <- mapM (normalise gamma) ts
      return $ TupleConstruct taus' ts'
    normalise' (TupleDestruct taus sigma f)         = do
      TupleType taus' <- normalise gamma $ TupleType taus
      sigma' <- normalise (TupleType taus' `Env.bind` gamma) sigma
      f' <- normalise gamma f
      return $ TupleDestruct taus' sigma' f'
    normalise' (TupleIdentity taus t)         = do
      TupleType taus' <- normalise gamma $ TupleType taus
      t' <- normalise gamma t
      return $ TupleIdentity taus' t'
    normalise' (CoTupleType taus)                   = do
      CoTupleType <$> mapM (normalise gamma) taus
    normalise' (CoTupleConstruct taus j t)          = do
      CoTupleType taus' <- normalise gamma (CoTupleType taus)
      t' <- normalise gamma t
      return $ CoTupleConstruct taus' j t'
    normalise' (CoTupleDestruct taus sigma fs)      = do
      CoTupleType taus' <- normalise gamma (CoTupleType taus)
      sigma' <- normalise (CoTupleType taus' `Env.bind` gamma) sigma
      fs' <- mapM (normalise gamma) fs
      return $ CoTupleDestruct taus' sigma' fs'
    normalise' (IdentityType tau x y)               = do
      tau' <- normalise gamma tau
      x' <- normalise gamma x
      y' <- normalise gamma y
      return $ IdentityType tau' x' y'
    normalise' (IdentityReflective tau x)           = do
      tau' <- normalise gamma tau
      x' <- normalise gamma x
      return $ IdentityReflective tau' x'
    normalise' (IdentityDestruct tau x y)           = do
      tau' <- normalise gamma tau
      x' <- normalise gamma x
      y' <- normalise gamma y
      return $ IdentityDestruct tau' x' y'
    normalise' NatType                              = return NatType
    normalise' NatZ                                 = return NatZ
    normalise' NatS                                 = return NatS
    normalise' (NatInduction tau f x)               = do
      tau' <- normalise (NatType `Env.bind` gamma) tau
      f' <- normalise (NatType `Env.bind` gamma) f
      x' <- normalise gamma x
      return $ NatInduction tau' f' x'

-- Typechecking

typecheck :: Environment -> Term -> EC Term
typecheck gamma t = (typecheck' gamma t) `catchError` (throwError . TypecheckErrorTrace gamma t)
  where
    typecheck' gamma (Variable i)                         = do
      maybe (throwError $ FreeVariable i) return $ lookup gamma i
    typecheck' gamma (Application f t)                    = do
      fTy <- typecheck gamma f
      case fTy of
        FunctionType tau sigma -> do
          tTy <- typecheck gamma t
          unify gamma tTy tau
          return $ substitute (t `Subst.bind` Subst.empty) sigma
        otherwise -> throwError $ ExceptedFunction fTy
    typecheck' gamma SetType                              = do
      return SetType
    typecheck' gamma (Abstraction tau t)                  = do
      tauTy <- typecheck gamma tau
      unify gamma tauTy SetType
      tTy <- typecheck (tau `Env.bind` gamma) t
      return $ FunctionType tau tTy
    typecheck' gamma (FunctionType tau sigma)             = do
      tauTy <- typecheck gamma tau
      unify gamma tauTy SetType
      sigmaTy <- typecheck (tau `Env.bind` gamma) sigma
      unify gamma sigmaTy SetType
      return SetType
    typecheck' gamma (TupleType taus)                     = do
      foldM_ (\gamma' tau -> do
          tauTy <- typecheck gamma' tau
          unify gamma' tauTy SetType
          return $ tau `Env.bind` gamma
        ) gamma taus
      return SetType
    typecheck' gamma (TupleConstruct taus ts)             = do
      foldM_ (\(gamma', s)  (tau, t) -> do
          tauTy <- typecheck gamma' tau
          unify gamma' tauTy SetType
          tTy <- typecheck gamma t
          unify gamma tTy $ substitute s tau
          return $ (tau `Env.bind` gamma, t `Subst.bind` s)
        ) (gamma, Subst.empty) (zip taus ts)
      return $ TupleType taus
    typecheck' gamma (TupleDestruct taus sigma f)         = do
      typecheck' gamma (TupleType taus)
      sigmaTy <- typecheck gamma sigma
      unify gamma sigmaTy $ functionTypeList taus SetType
      fTy <- typecheck gamma f
      unify gamma fTy $ functionTypeList taus sigma
    typecheck' gamma (TupleIdentity taus t)               = do
      typecheck' gamma (TupleType taus)
      tTy <- typecheck gamma t
      unify gamma tTy (TupleType taus)
      return $ IdentityType (TupleType taus) t (TupleConstruct taus $ (\i -> Application (tupleProjection taus i) t) <$> [0..length taus - 1])
    typecheck' gamma (CoTupleType taus)                   = do
      forM_ taus $ \tau -> do
        tauTy <- typecheck gamma tau
        unify gamma tau SetType
      return SetType
    typecheck' gamma (CoTupleConstruct taus j t)          = do
      typecheck' gamma (CoTupleType taus)
      tTy <- typecheck gamma t
      unify gamma tTy $ taus !! j
      return $ CoTupleType taus
    typecheck' gamma (CoTupleDestruct taus sigma fs)      = do
      typecheck' gamma (CoTupleType taus)
      sigmaTy <- typecheck gamma sigma
      unify (CoTupleType taus `Env.bind` gamma) sigmaTy SetType
      forM_ (zip taus fs) $ \(tau, f) -> do
        fTy <- typecheck gamma f
        unify gamma fTy $ FunctionType tau sigma
      return $ FunctionType (CoTupleType taus) $ lift sigma
    typecheck' gamma (IdentityType tau x y)               = do
      tauTy <- typecheck gamma tau
      unify gamma tauTy SetType
      xTy <- typecheck gamma x
      unify gamma xTy tau
      yTy <- typecheck gamma y
      unify gamma yTy tau
      return SetType
    typecheck' gamma (IdentityReflective tau x)           = do
      tauTy <- typecheck gamma tau
      unify gamma tauTy SetType
      xTy <- typecheck gamma x
      unify gamma xTy tau
      return $ IdentityType tau x x
    typecheck' gamma (IdentityDestruct tau x y)           = do
      typecheck' gamma (IdentityType tau x y)
      return $ functionTypeList [IdentityType tau x y, FunctionType (lift tau) SetType, Application (Variable 0) $ liftBy 2 0 x] (Application (Variable 1) $ liftBy 3 0 y)
    typecheck' gamma NatType                              = return SetType
    typecheck' gamma NatZ                                 = return $ NatType
    typecheck' gamma NatS                                 = return $ FunctionType NatType NatType
    typecheck' gamma (NatInduction tau f x)               = do
      tauTy <- typecheck gamma tau
      unify gamma tauTy $ FunctionType NatType SetType
      fTy <- typecheck gamma f
      unify gamma fTy $ functionTypeList [NatType, Application (lift tau) (Variable 0)] $ Application (liftBy 2 0 tau) $ Application NatS (Variable 1)
      xTy <- typecheck gamma x
      unify gamma xTy $ Application tau NatZ
      return $ FunctionType NatType $ Application tau (Variable 0)

-- Todo : move to other module

-- explore

\end{code}
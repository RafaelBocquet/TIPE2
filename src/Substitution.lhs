\begin{code}
module Substitution where

import Term

import Prelude hiding (lookup)
import Control.Applicative

newtype Substitution = Substitution [Term]
  deriving(Eq, Show)

empty :: Substitution
empty = Substitution []

bind :: Term -> Substitution -> Substitution
e `bind` (Substitution env) = Substitution $ e : env


substitute :: Substitution -> Term -> Term
substitute (Substitution s) = substitute' 0
  where
    substitute' i (Variable j)
      | j >= i + length s                                = Variable (j - length s)
      | j >= i && j < i + length s                       = s !! (j - i)
      | otherwise                                        = Variable j
    substitute' i (Application f t)                    = Application (substitute' i $ f) (substitute' i $ t)
    substitute' i SetType                              = SetType
    substitute' i (Abstraction tau t)                  = Abstraction (substitute' i $ tau) (substitute' (i + 1) $ t)
    substitute' i (FunctionType tau sigma)             = FunctionType (substitute' i $ tau) (substitute' (i + 1) $ sigma)
    substitute' i (TupleType taus)                     = TupleType (uncurry substitute' <$> zip [i..] taus)
    substitute' i (TupleConstruct taus ts)             = TupleConstruct (uncurry substitute' <$> zip [i..] taus) (substitute' i <$> ts)
    substitute' i (TupleDestruct taus sigma f)         = TupleDestruct (uncurry substitute' <$> zip [i..] taus) (substitute' (i + 1) $ sigma) (substitute' i $ f)
    substitute' i (CoTupleType taus)                   = CoTupleType (substitute' i <$> taus)
    substitute' i (CoTupleConstruct taus j t)          = CoTupleConstruct (substitute' i <$> taus) j (substitute' i $ t)
    substitute' i (CoTupleDestruct taus sigma fs)      = CoTupleDestruct (substitute' i <$> taus) (substitute' (i + 1) $ sigma) (substitute' i <$> fs)
    substitute' i (IdentityType tau x y)               = IdentityType (substitute' i $ tau) (substitute' i $ x) (substitute' i $ y)
    substitute' i (IdentityReflective tau x)           = IdentityReflective (substitute' i $ tau) (substitute' i $ x)
    substitute' i (IdentityDestruct tau x y)           = IdentityDestruct (substitute' i $ tau) (substitute' i $ x) (substitute' i $ y)


\end{code}
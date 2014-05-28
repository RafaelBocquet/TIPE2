\begin{code}
module Environment where

import Expression as Expr

import Prelude hiding (lookup)
import Control.Applicative

newtype Environment = Environment [Expression]
  deriving(Eq, Show)

empty :: Environment
empty = Environment []

bind :: Expression -> Environment -> Environment
e `bind` (Environment env) = Environment $ (lift 0) <$> (e :  env)

lookup :: Environment -> Int -> Maybe Expression
lookup (Environment env) i = lookup' env i
  where
    lookup' [] _     = Nothing
    lookup' (x:_) 0  = Just x
    lookup' (_:xs) i = lookup' xs (i-1)

applyPermutation :: Environment -> [Int] -> Environment
applyPermutation (Environment env) p = Environment $ flip fmap [0 .. length env - 1] $ \i -> Expr.applyPermutation 0 p (env !! (p !! i))

\end{code}
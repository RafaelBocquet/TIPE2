\begin{code}
module Environment where

import Term

import Prelude hiding (lookup)
import Control.Applicative

newtype Environment = Environment [Term]
  deriving(Eq, Show)

empty :: Environment
empty = Environment []

bind :: Term -> Environment -> Environment
e `bind` (Environment env) = Environment $ e : env

lookup :: Environment -> Int -> Maybe Term
lookup (Environment env) i = liftBy (i + 1) <$> lookup' env i
  where
    lookup' [] _     = Nothing
    lookup' (x:_) 0  = Just x
    lookup' (_:xs) i = lookup' xs (i-1)

--applyPermutation :: Environment -> [Int] -> Environment
--applyPermutation (Environment env) p = Environment $ flip fmap [0 .. length env - 1] $ \i -> Expr.applyPermutation 0 p (env !! (p !! i))


\end{code}
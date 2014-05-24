\begin{code}
module Environment where

import Expression

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

\end{code}
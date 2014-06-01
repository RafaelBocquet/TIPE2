\begin{code}
module Main where

import Term
import Environment as Env
import Evaluation

import Util

testTypecheck :: String -> Term -> Term -> IO ()
testTypecheck s t tau = do
  putStrLn . either ((yellow s <+> ":" <+>) . show) ((yellow s <+> ":" <+>) . show . runEC . unify Env.empty tau) . runEC . typecheck Env.empty $ t

unitIsContractileType :: Term
unitIsContractileType =
  FunctionType unitType $ IdentityType unitType unitValue (Variable 0)

main :: IO ()
main = do
  putStrLn $ red "Tipe 2"
  testTypecheck "unitValue" unitValue unitType
  testTypecheck "refl unitValue" (IdentityReflective unitType unitValue) (IdentityType unitType unitValue unitValue)
  testTypecheck "unitIsContractileType" unitIsContractileType SetType
\end{code}
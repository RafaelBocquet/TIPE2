\begin{code}
module Main where

import Term
import Environment as Env
import Evaluation

import Util

import Control.Monad

testTypecheck :: String -> Term -> Term -> IO ()
testTypecheck s t tau = do
  putStrLn . either ((yellow s <+> ":" <+>) . show) ((yellow s <+> ":" <+>) . show . runEC . (unify Env.empty tau <=< normalise Env.empty)) . runEC . typecheck Env.empty $ t

unitIsContractibleType :: Term
unitIsContractibleType =
  FunctionType unitType $ IdentityType unitType (Variable 0) unitValue

unitIsConstractible :: Term
unitIsConstractible =
  Abstraction unitType $ TupleIdentity [] (Variable 0)

idSymmetricType :: Term
idSymmetricType = 
  functionTypeList
  [ SetType
  , Variable 0
  , Variable 1
  , IdentityType (Variable 2) (Variable 1) (Variable 0)
  ] $ IdentityType (Variable 3) (Variable 1) (Variable 2)

idSymmetric :: Term
idSymmetric =
  abstractionList
  [ SetType
  , Variable 0
  , Variable 1
  , IdentityType (Variable 2) (Variable 1) (Variable 0)
  ] $ applicationList (IdentityDestruct (Variable 3) (Variable 2) (Variable 1))
    [ Variable 0
    , Abstraction (Variable 3) (IdentityType (Variable 4) (Variable 0) (Variable 3))
    , IdentityReflective (Variable 3) (Variable 2)
    ]

idCType :: Term
idCType =
  functionTypeList
  [ SetType
  , Variable 0
  , Variable 1
  , IdentityType (Variable 2) (Variable 1) (Variable 0)
  , SetType
  , FunctionType (Variable 4) (Variable 1)
  ] $ IdentityType (Variable 1) (Application (Variable 0) (Variable 4)) (Application (Variable 0) (Variable 3))

idC :: Term
idC = 
  abstractionList
  [ SetType
  , Variable 0
  , Variable 1
  , IdentityType (Variable 2) (Variable 1) (Variable 0)
  , SetType
  , FunctionType (Variable 4) (Variable 1)
  ] $ applicationList (IdentityDestruct (Variable 5) (Variable 4) (Variable 3))
    [ Variable 2
    , Abstraction (Variable 5) (IdentityType (Variable 2) (Application (Variable 1) (Variable 5)) (Application (Variable 1) (Variable 0)))
    , IdentityReflective (Variable 1) (Application (Variable 0) (Variable 4))
    ]

one :: Term
one = Application NatS NatZ

indSuccIsNatType' = IdentityType NatType (Variable 0) (Application (NatInduction (Abstraction NatType NatType) (Abstraction NatType NatS) NatZ) (Variable 0))

indSuccIsNatType :: Term
indSuccIsNatType =
  FunctionType NatType $ indSuccIsNatType'

indSuccIsNat :: Term
indSuccIsNat =
  NatInduction
    (Abstraction NatType $ indSuccIsNatType')
    (Abstraction NatType $ Abstraction indSuccIsNatType' $
      applicationList idC
      [ NatType
      , Variable 1
      , Application (NatInduction (Abstraction NatType NatType) (Abstraction NatType NatS) NatZ) (Variable 1)
      , Variable 0
      , NatType
      , NatS
      ]
    )
    (IdentityReflective NatType NatZ)

main :: IO ()
main = do
  putStrLn $ red "Tipe 2"
  testTypecheck "unitValue" unitValue unitType
  testTypecheck "refl unitValue" (IdentityReflective unitType unitValue) (IdentityType unitType unitValue unitValue)
  testTypecheck "unitIsContractibleType" unitIsContractibleType SetType
  testTypecheck "unitIsContractible" unitIsConstractible unitIsContractibleType
  testTypecheck "idSymmetricType" idSymmetricType SetType
  testTypecheck "idSymmetric" idSymmetric idSymmetricType
  testTypecheck "idCType" idCType SetType
  testTypecheck "idC" idC idCType
  testTypecheck "one" one NatType
  testTypecheck "indSuccIsNatType" indSuccIsNatType SetType
  testTypecheck "indSuccIsNat" indSuccIsNat indSuccIsNatType
\end{code}
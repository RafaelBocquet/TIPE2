\begin{code}
module Main where

import Term as T
import Environment as Env
import Evaluation as Eval
import ProofBase as PB 
import ProofSearch as PS

import Util

import Control.Monad

testTypecheck :: String -> Term -> Term -> IO ()
testTypecheck s t tau = do
  putStrLn . either ((yellow s <+> ":" <+>) . show) ((yellow s <+> ":" <+>) . show . runEC . (unify Env.empty tau <=< normalise Env.empty)) . runEC . typecheck Env.empty $ t

testProofSearch :: String -> Term -> IO ()
testProofSearch s tau = do
  putStrLn . (yellow s <+> ":" <+>) . show . runPC . proofSearch Env.empty $ tau

unitIsUniqueType :: Term
unitIsUniqueType =
  FunctionType unitType $ IdentityType unitType (Variable 0) unitValue

unitIsUnique :: Term
unitIsUnique =
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

proj1Type :: Term
proj1Type = functionTypeList [SetType, SetType, TupleType [Variable 1, Variable 1]] $ Variable 2

proj1 :: Term
proj1 = abstractionList [SetType, SetType] $ tupleProjection [Variable 1, Variable 1] 0

proj2Type :: Term
proj2Type = functionTypeList [SetType, SetType, TupleType [Variable 1, Variable 1]] $ Variable 1

proj2 :: Term
proj2 = abstractionList [SetType, SetType] $ tupleProjection [Variable 1, Variable 1] 1

decidable :: Term
decidable = Abstraction SetType $ CoTupleType [Variable 0, T.negate $ Variable 0]

modusPonensBisType :: Term
modusPonensBisType = functionTypeList [SetType, SetType, TupleType [Variable 1, FunctionType (Variable 2) (Variable 2)]] $ Variable 1

modusPonensBis :: Term
modusPonensBis = abstractionList [SetType, SetType] $
  TupleDestruct
    [Variable 1, FunctionType (Variable 2) (Variable 2)]
    (Variable 1)
    (abstractionList [Variable 1, FunctionType (Variable 2) (Variable 2)] $ Application (Variable 0) (Variable 1))

mainBase :: ProofBase
mainBase = insertProofList PB.empty
  [ (SetType, unitType)
  , (unitType, unitValue)
  , (unitIsUniqueType, unitIsUnique)
  , (idSymmetricType, idSymmetric)
  , (idCType, idC)
  , (indSuccIsNatType, indSuccIsNat)
  , (proj1Type, proj1)
  , (proj2Type, proj2)
  ]

main :: IO ()
main = do
  putStrLn $ red "Tipe 2"
  testTypecheck "unitValue" unitValue unitType
  testTypecheck "refl unitValue" (IdentityReflective unitType unitValue) (IdentityType unitType unitValue unitValue)
  testTypecheck "unitIsUniqueType" unitIsUniqueType SetType
  testTypecheck "unitIsUnique" unitIsUnique unitIsUniqueType
  testTypecheck "idSymmetricType" idSymmetricType SetType
  testTypecheck "idSymmetric" idSymmetric idSymmetricType
  testTypecheck "idCType" idCType SetType
  testTypecheck "idC" idC idCType
  testTypecheck "one" one NatType
  testTypecheck "indSuccIsNatType" indSuccIsNatType SetType
  testTypecheck "indSuccIsNat" indSuccIsNat indSuccIsNatType
  testTypecheck "proj1Type" proj1Type SetType
  testTypecheck "proj1" proj1 proj1Type
  testTypecheck "proj2Type" proj2Type SetType
  testTypecheck "proj2" proj2 proj2Type
  testTypecheck "modusPonensBisType" modusPonensBisType SetType
  testTypecheck "modusPonensBis" modusPonensBis modusPonensBisType

  putStrLn $ blue " --- ProofSearch --- "

  testProofSearch "SetType" SetType
  testProofSearch "unitType" unitType
  testProofSearch "proj1Type" proj1Type
  testProofSearch "proj2Type" proj2Type
  testProofSearch "idSymmetricType" idSymmetricType
  testProofSearch "idCType" idCType
  testProofSearch "indSuccIsNatType" indSuccIsNatType

  putStrLn $ blue " --- ProofBase --- "
  putStrLn $ show mainBase
\end{code}
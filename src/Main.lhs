\begin{code}
module Main where

import Expression as Expr
import Environment as Env
import Evaluation as Eval
import PSearch

import Util

negate :: Expression -> Expression
negate tau =
  FunctionType tau (lift 0 bottomType)

add2negate :: Expression -> Expression
add2negate tau =
  abstractionList [tau, lift 0 $ Main.negate tau] $ Application (Variable 0) (Variable 1)

identitySymetric :: Expression
identitySymetric =
  functionTypeList [SetType, Variable 0, Variable 1, identityType (Variable 2) (Variable 1) (Variable 0)] $
  identityType (Variable 3) (Variable 1) (Variable 2)

identitySymetricPrf :: Expression
identitySymetricPrf =
  abstractionList
    [ SetType
    , Variable 0
    , Variable 1
    , identityType (Variable 2) (Variable 1) (Variable 0)
    ] $
  applicationList (Variable 0)
    [ Abstraction (Variable 3) $ identityType (Variable 4) (Variable 0) (Variable 3)
    , identityReflective (Variable 3) (Variable 2)
    ]


identityCongTy :: Expression
identityCongTy = functionTypeList
  [ SetType
  , Variable 0
  , Variable 1
  , identityType (Variable 2) (Variable 1) (Variable 0)
  , SetType
  , FunctionType (Variable 4) (Variable 1)
  ] $ identityType (Variable 1) (Application (Variable 0) (Variable 4)) (Application (Variable 0) (Variable 3))

identityCong :: Expression
identityCong = abstractionList
  [ SetType
  , Variable 0
  , Variable 1
  , identityType (Variable 2) (Variable 1) (Variable 0)
  , SetType
  , FunctionType (Variable 4) (Variable 1)
  ] $ applicationList (Variable 2)
    [ Abstraction (Variable 5) $ identityType (Variable 2) (Application (Variable 1) (Variable 5)) (Application (Variable 1) (Variable 0))
    , identityReflective (Variable 1) (Application (Variable 0) (Variable 4))
    ]

isContractibleType :: Expression
isContractibleType =
  functionTypeList
    [ SetType
    , Variable 0
    , Variable 1
    ] $ identityType (Variable 2) (Variable 1) (Variable 0)

unitTypeUnique :: Expression
unitTypeUnique = applicationList isContractibleType [unitType, unitValue]

unitTypeUniquePrf :: Expression
unitTypeUniquePrf =
  Abstraction unitType $ abstractionList
    [ FunctionType unitType SetType
    , Application (Variable 0) (Variable 1)
    ] $ Variable 0

compose :: Expression
compose = abstractionList
  [ SetType
  , FunctionType (Variable 0) SetType
  , functionTypeList [Variable 1, Application (Variable 1) (Variable 0)] SetType
  , functionTypeList [Variable 2, Application (Variable 2) (Variable 0)] (applicationList (Variable 2) [Variable 1, Variable 0])
  , FunctionType (Variable 3) (Application (Variable 3) (Variable 0))
  , Variable 4
  ] $ applicationList (Variable 2) [Variable 0, Application (Variable 1) (Variable 0)]

natType :: Expression
natType = Renaming "Nat" $ functionTypeList [SetType, FunctionType (Variable 0) (Variable 1), Variable 1] $ Variable 2
zero :: Expression
zero = Renaming "Z" $ abstractionList [SetType, FunctionType (Variable 0) (Variable 1), Variable 1] $ Variable 0
one :: Expression
one = abstractionList [SetType, FunctionType (Variable 0) (Variable 1), Variable 1] $ Application (Variable 1) (Variable 0)
succ :: Expression
succ = Renaming "S" $ abstractionList [natType, SetType, FunctionType (Variable 0) (Variable 1), Variable 1] $ applicationList (Variable 3) [Variable 2, Variable 1, Application (Variable 1) (Variable 0)]
two = Application Main.succ one
three = Application Main.succ two
four = Application Main.succ three
five = Application Main.succ four

vect :: Expression
vect = abstractionList [SetType, natType] $ applicationList (Variable 0) [SetType, Abstraction SetType $ simplePairType (Variable 2) (Variable 0), unitType]


testTypecheckExpression :: String -> Expression -> IO ()
testTypecheckExpression s e = putStrLn $ red s ++ " : " ++ (show . runTC . typecheck Env.empty $ e)
testTypecheckUnifyExpression :: String -> Expression -> Expression -> IO ()
testTypecheckUnifyExpression s e t = putStrLn . ((red s ++ " : ") ++) $ show . runTC $ do
  eTy <- typecheck Env.empty e
  unify Env.empty eTy t
testPNormalise :: String -> Expression -> IO ()
testPNormalise s e = putStrLn $ red s ++ " : " ++ (show . runPN $ pNormalise e)

testLatexTypecheckExpression :: String -> Expression -> IO ()
testLatexTypecheckExpression s e = putStrLn $ s ++ " : \n" ++ showLatexExpression e ++ "\n typechecks to \n" ++ (either show showLatexExpression . runTC . typecheck Env.empty $ e) ++ "\n"
testLatexPNormalise :: String -> Expression -> IO ()
testLatexPNormalise s e = putStrLn $ s ++ " : \n" ++ showLatexExpression e ++ "\n normalises to \n" ++ (either show ((("\\digraph{" ++ s ++ "}{") ++) . (++ "}") . showDotPExpression) . runPN . pNormalise $ e) ++ "\n"

main :: IO ()
main = do
  putStrLn "Tipe 2"
  testTypecheckExpression "unitType" unitType
  testTypecheckUnifyExpression "unitValue" unitValue unitType
  testTypecheckExpression "unitTypeUnique" unitTypeUnique
  -- testTypecheckUnifyExpression "unitTypeUnique" unitTypeUniquePrf unitTypeUnique
  testTypecheckExpression "identitySymetric" identitySymetric
  testTypecheckUnifyExpression "identitySymetricPrf" identitySymetricPrf identitySymetric
  testTypecheckUnifyExpression "zero" zero natType
  testTypecheckUnifyExpression "one" one natType
  testTypecheckUnifyExpression "succ" Main.succ (FunctionType natType natType)
  testTypecheckExpression "compose" compose
  testTypecheckExpression "vect" vect
  testTypecheckExpression "vect Nat 5" (applicationList vect [natType, five])
  testTypecheckUnifyExpression "identityCong" identityCong identityCongTy
  testTypecheckExpression "isContractibleType" isContractibleType
  putStrLn $ yellow "Testing pNormalise"
  testPNormalise "identitySymetric" identitySymetric
  testPNormalise "identityCongTy" identityCongTy
  testPNormalise "isContractibleType" isContractibleType

  testLatexTypecheckExpression "identityCongTy" identityCongTy
  testLatexTypecheckExpression "identityCong" identityCong
  testLatexTypecheckExpression "identitySymetricPrf" identitySymetricPrf

  testLatexPNormalise "identitySymetric" identitySymetric
  testLatexPNormalise "identityCongTy" identityCongTy
\end{code}
\begin{code}
module Expression where

import Pretty
import Util

import Control.Applicative
import Control.Monad

import Debug.Trace

import Data.Char

data Expression =
    Variable Int
  | Application Expression Expression

  | SetType

  | Abstraction Expression Expression
  | FunctionType Expression Expression

  | Renaming String Expression
  deriving (Eq)

instance Show Expression where
  show = show' 0
    where
      show' i (Variable j)
        | j < i                    = yellow [chr $ (ord 'a') + i - j - 1]
        | otherwise                = blue "E" ++ yellow (subScriptInt (j - i))
      show' i (Application f t)    = "(" ++ show' i f ++ " " ++ show' i t ++ ")"

      show' i SetType              = blue "SetType"

      show' i (Abstraction tau t)  = "(" ++ blue "λ(" ++ yellow [chr $ (ord 'a') + i] ++ " : " ++ show' i tau ++ ")" ++ blue ". " ++ show' (i + 1) t ++ ")"
      show' i (FunctionType tau t) = "(" ++ blue "Π(" ++ yellow [chr $ (ord 'a') + i] ++ " : " ++ show' i tau ++ ")" ++ blue ". " ++ show' (i + 1) t ++ ")"

      show' i (Renaming str t)     = yellow str

lift :: Int -> Expression -> Expression
lift i (Variable j)
  | i > j                                     = Variable j
  | otherwise                                 = Variable (j+1)
lift i (Application f t)                      = Application (lift i f) (lift i t)
lift i SetType                                = SetType
lift i (Abstraction tau t)                    = Abstraction (lift i tau) (lift (i+1) t)
lift i (FunctionType tau sigma)               = FunctionType (lift i tau) (lift (i+1) sigma)
lift i (Renaming s e)                         = Renaming s (lift i e)

liftOf :: Int -> Expression -> Expression
liftOf 0 = id
liftOf n = lift 0 . liftOf (n-1)

substitute :: Int -> Expression -> Expression -> Expression
substitute i e' (Variable j)
  | i < j                                     = Variable (j-1)
  | i == j                                    = e'
  | i > j                                     = Variable j
substitute i e' (Application f t)                      = Application (substitute i e' f) (substitute i e' t)
substitute i e' SetType                                = SetType
substitute i e' (Abstraction tau t)                    = Abstraction (substitute i e' tau) (substitute (i+1) (lift 0 e') t)
substitute i e' (FunctionType tau sigma)               = FunctionType (substitute i e' tau) (substitute (i+1) (lift 0 e') sigma)
substitute i e' (Renaming s e)                         = Renaming s (substitute i e' e)


-- some functions
applicationList :: Expression -> [Expression] -> Expression
applicationList = foldl Application

abstractionList :: [Expression] -> Expression -> Expression
abstractionList = flip $ foldr Abstraction

functionTypeList :: [Expression] -> Expression -> Expression
functionTypeList = flip $ foldr FunctionType

unitType :: Expression
unitType = Renaming "UnitType" $ functionTypeList [SetType, Variable 0] $ Variable 1

unitValue :: Expression
unitValue = Renaming "UnitValue" $ abstractionList [SetType, Variable 0] $ Variable 0

simplePairType :: Expression -> Expression -> Expression
simplePairType tau1 tau2 =
  functionTypeList [SetType, functionTypeList [lift 0 tau1, liftOf 2 tau2] $ Variable 2] $ Variable 1

simplePairConstruct :: Expression -> Expression -> Expression -> Expression -> Expression
simplePairConstruct tau1 tau2 t1 t2 =
  abstractionList [SetType, functionTypeList [lift 0 tau1, liftOf 2 tau2] $ Variable 2] $ applicationList (Variable 0) [liftOf 2 t1, liftOf 2 t2]

copairType :: Expression -> Expression -> Expression
copairType tau1 tau2 =
  functionTypeList [SetType, FunctionType (lift 0 tau1) (Variable 1), FunctionType (liftOf 2 tau2) (Variable 2)] $ Variable 2

coPairConstruct1 :: Expression -> Expression -> Expression -> Expression
coPairConstruct1 tau1 tau2 t1 =
  abstractionList [SetType, FunctionType (lift 0 tau1) (Variable 1), FunctionType (liftOf 2 tau2) (Variable 2)] $ Application (Variable 1) t1

coPairConstruct2 :: Expression -> Expression -> Expression -> Expression
coPairConstruct2 tau1 tau2 t2 =
  abstractionList [SetType, FunctionType (lift 0 tau1) (Variable 1), FunctionType (liftOf 2 tau2) (Variable 2)] $ Application (Variable 0) t2

bottomType :: Expression
bottomType = Renaming "BottomType" $ FunctionType SetType $ Variable 0

identityType :: Expression -> Expression -> Expression -> Expression
identityType tau x y = functionTypeList [FunctionType tau SetType, Application (Variable 0) $ lift 0 x] $ Application (Variable 1) $ liftOf 2 y

identityReflective :: Expression -> Expression -> Expression
identityReflective tau x = abstractionList [FunctionType tau SetType, Application (Variable 0) $ lift 0 x] $ Variable 0
\end{code}
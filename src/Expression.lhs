\begin{code}
module Expression where

import Pretty
import Util

import Control.Applicative
import Control.Monad

import qualified Data.Set as Set
import Data.Char


data Expression =
    Variable Int
  | Application Expression Expression

  | SetType

  | Abstraction Expression Expression
  | FunctionType Expression Expression

  | Renaming String Expression
  deriving (Eq, Ord)

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

showLatexExpression :: Expression -> String
showLatexExpression e = "\\large\n\\begin{math}\n" ++ showLatexExpression' 0 e ++ "\n\\end{math}"
  where
    showLatexExpression' i (Variable j)
      | j < i                    = [chr $ (ord 'a') + i - j - 1]
      | otherwise                = "E_{" ++ show (j - i) ++ "}"
    showLatexExpression' i (Application f t)    = "(" ++ showLatexExpression' i f ++ " " ++ showLatexExpression' i t ++ ")"

    showLatexExpression' i SetType              = "\\top"

    showLatexExpression' i (Abstraction tau t)  = "\\Lambda{(" ++ [chr $ (ord 'a') + i] ++ " : " ++ showLatexExpression' i tau ++ ")} \\rightarrow " ++ showLatexExpression' (i+1) t
    showLatexExpression' i (FunctionType tau sigma) = "\\Pi{(" ++ [chr $ (ord 'a') + i] ++ " : " ++ showLatexExpression' i tau ++ ")} \\rightarrow " ++ showLatexExpression' (i+1) sigma

    showLatexExpression' i (Renaming str t)     = "\\text{" ++ str ++ "}"

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
substitute i e' (Application f t)             = Application (substitute i e' f) (substitute i e' t)
substitute i e' SetType                       = SetType
substitute i e' (Abstraction tau t)           = Abstraction (substitute i e' tau) (substitute (i+1) (lift 0 e') t)
substitute i e' (FunctionType tau sigma)      = FunctionType (substitute i e' tau) (substitute (i+1) (lift 0 e') sigma)
substitute i e' (Renaming s e)                = Renaming s (substitute i e' e)

dependencies :: Int -> Expression -> Set.Set Int
dependencies i (Variable j)
  | j < i                                     = Set.empty
  | otherwise                                 = Set.singleton (j - i)
dependencies i (Application f t)              = Set.union (dependencies i f) (dependencies i t)
dependencies i SetType                        = Set.empty
dependencies i (Abstraction tau t)            = Set.union (dependencies i tau) (dependencies (i + 1) t)
dependencies i (FunctionType tau sigma)       = Set.union (dependencies i tau) (dependencies (i + 1) sigma)
dependencies i (Renaming s e)                 = dependencies i e

applyPermutation :: Int -> [Int] -> Expression -> Expression
applyPermutation i p (Variable j)
  | j < i                                     = Variable j
  | otherwise                                 = Variable $ p !! (j - i)
applyPermutation i p (Application f t)        = Application (applyPermutation i p f) (applyPermutation i p t)
applyPermutation i p SetType                  = SetType
applyPermutation i p (Abstraction tau t)      = Abstraction (applyPermutation i p tau) (applyPermutation (i + 1) p t)
applyPermutation i p (FunctionType tau sigma) = FunctionType (applyPermutation i p tau) (applyPermutation (i + 1) p sigma)
applyPermutation i p (Renaming s e)           = Renaming s $ applyPermutation i p e

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
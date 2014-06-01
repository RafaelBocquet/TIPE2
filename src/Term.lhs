\begin{code}
module Term where

import Util

import Control.Applicative
import Control.Monad

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Char

-- Term

data Term =
    Variable Int
  | Application Term Term

  | SetType

  | Abstraction Term Term
  | FunctionType Term Term

  | TupleType [Term]
  | TupleConstruct [Term] [Term]
  | TupleDestruct [Term] Term Term

  | CoTupleType [Term]
  | CoTupleConstruct [Term] Int Term
  | CoTupleDestruct [Term] Term [Term]

  | IdentityType Term Term Term
  | IdentityReflective Term Term
  | IdentityDestruct Term Term Term

  -- Nat instead of inductive / coinductive types for simplicity
  -- | NatType
  -- | NatValue Int
  -- | NatInduction
  deriving (Eq)

showWithEnvironment :: [String] -> Term -> String
showWithEnvironment env = showWithEnvironment' 0
  where
    showWithEnvironment' :: Int -> Term -> String
    showWithEnvironment' i (Variable j)
      | j <= i                                 =
          (yellow . show . chr) (ord 'a' + i - j)
      | j <= i + length env                    =
          yellow $ env !! (j - i)
      | otherwise                              =
          blue "E" ++ yellow (subScriptInt $ j - i - length env)
    showWithEnvironment' i (Application f t)   =
          "(" ++ showWithEnvironment' i f <+> showWithEnvironment' i t ++ ")"
    showWithEnvironment' i SetType             =
          blue "U"
    showWithEnvironment' i (Abstraction tau t) =
          "(" ++ blue "Λ" ++ "(" ++ (show . chr) (ord 'a' + i) <+> red ":" <+> showWithEnvironment' i tau ++ ")" ++ red "." <+> showWithEnvironment' (i + 1) t ++ ")"
    showWithEnvironment' i (FunctionType tau sigma) =
          "(" ++ blue "Π" ++ "(" ++ (show . chr) (ord 'a' + i) <+> red ":" <+> showWithEnvironment' i tau ++ ")" ++ red "." <+> showWithEnvironment' (i + 1) sigma ++ ")"
    showWithEnvironment' i (TupleType []) =
          blue "⊤"
    showWithEnvironment' i (TupleType (tau:taus)) =
          "(" ++ blue "Σ" ++ "(" ++ (show . chr) (ord 'a' + i) <+> red ":" <+> showWithEnvironment' i tau ++ ")" ++ red "." <+> showWithEnvironment' (i + 1) (TupleType taus) ++ ")"
    showWithEnvironment' i (TupleConstruct [] []) =
          blue "()"
    showWithEnvironment' i (TupleConstruct (tau:taus) (t:ts)) =
          "(" ++ showWithEnvironment' i t ++ ", " ++ showWithEnvironment' i (TupleConstruct taus ts) ++ ")"
    showWithEnvironment' i (TupleDestruct taus sigma f) =
          "(" ++ blue "match" <+> showWithEnvironment' i (TupleType taus) <+> red "to" <+> showWithEnvironment' (i + 1) sigma <+> red "with" <+> showWithEnvironment' i f ++ ")"
    showWithEnvironment' i (CoTupleType []) =
          blue "⊥"
    showWithEnvironment' i (CoTupleType (tau:taus)) =
          "⟨" ++ showWithEnvironment' i tau ++ ", " ++ showWithEnvironment' i (CoTupleType taus) ++ "⟩"
    showWithEnvironment' i (CoTupleConstruct [] j t) =
          blue "⊥"
    showWithEnvironment' i (CoTupleConstruct (tau:taus) 0 t) =
          red "⟨" ++ showWithEnvironment' i t ++ ", " ++ showWithEnvironment' i (CoTupleConstruct taus (-1) t) ++ red "⟩"
    showWithEnvironment' i (CoTupleConstruct (tau:taus) j t) =
          "⟨" ++ showWithEnvironment' i tau ++ ", " ++ showWithEnvironment' i (CoTupleConstruct taus (j - 1) t) ++ "⟩"
    showWithEnvironment' i (CoTupleDestruct taus sigma fs) =
          "(" ++ blue "match" <+> showWithEnvironment' i (CoTupleType taus) <+> red "to" <+> showWithEnvironment' (i + 1) sigma <+> red "with" <+> showWithEnvironment' i (CoTupleType fs) ++ ")"
    showWithEnvironment' i (IdentityType tau x y) =
          "(" ++ blue "Id" <+> showWithEnvironment' i tau <+> showWithEnvironment' i x <+> showWithEnvironment' i y ++ ")"




instance Show Term where
  show = showWithEnvironment []

liftBy :: Int -> Int -> Term -> Term
liftBy n i (Variable j)
  | j >= i                                      = Variable (j + n)
  | otherwise                                   = Variable j
liftBy n i (Application f t)                    = Application (liftBy n i $ f) (liftBy n i $ t)
liftBy n i SetType                              = SetType
liftBy n i (Abstraction tau t)                  = Abstraction (liftBy n i $ tau) (liftBy n (i + 1) $ t)
liftBy n i (FunctionType tau sigma)             = FunctionType (liftBy n i $ tau) (liftBy n (i + 1) $ sigma)
liftBy n i (TupleType taus)                     = TupleType (uncurry (liftBy n) <$> zip [i..] taus)
liftBy n i (TupleConstruct taus ts)             = TupleConstruct (uncurry (liftBy n) <$> zip [i..] taus) (liftBy n i <$> ts)
liftBy n i (TupleDestruct taus sigma f)         = TupleDestruct (uncurry (liftBy n) <$> zip [i..] taus) (liftBy n (i + 1) $ sigma) (liftBy n i $ f)
liftBy n i (CoTupleType taus)                   = CoTupleType (liftBy n i <$> taus)
liftBy n i (CoTupleConstruct taus j t)          = CoTupleConstruct (liftBy n i <$> taus) j (liftBy n i $ t)
liftBy n i (CoTupleDestruct taus sigma fs)      = CoTupleDestruct (liftBy n i <$> taus) (liftBy n (i + 1) $ sigma) (liftBy n i <$> fs)
liftBy n i (IdentityType tau x y)               = IdentityType (liftBy n i $ tau) (liftBy n i $ x) (liftBy n i $ y)
liftBy n i (IdentityReflective tau x)           = IdentityReflective (liftBy n i $ tau) (liftBy n i $ x)
liftBy n i (IdentityDestruct tau x y)           = IdentityDestruct (liftBy n i $ tau) (liftBy n i $ x) (liftBy n i $ y)

lift :: Term -> Term
lift = liftBy 1 0

-- Smart constructors

applicationList :: Term -> [Term] -> Term
applicationList = foldr Application

abstractionList :: [Term] -> Term -> Term
abstractionList = flip $ foldl Abstraction

functionTypeList :: [Term] -> Term -> Term
functionTypeList = flip $ foldl FunctionType

unitType :: Term
unitType = TupleType []

unitValue :: Term
unitValue = TupleConstruct [] []

bottomType :: Term
bottomType = CoTupleType []

\end{code}
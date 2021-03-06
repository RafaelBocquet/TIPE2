\begin{code}
module Term where

import Util

import Control.Applicative
import Control.Monad

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
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
  | TupleIdentity [Term] Term -- x : (TupleType t) = TupleDestruct . TupleConstruct x

  | CoTupleType [Term]
  | CoTupleConstruct [Term] Int Term
  | CoTupleDestruct [Term] Term [Term]

  | IdentityType Term Term Term
  | IdentityReflective Term Term
  | IdentityDestruct Term Term Term

  -- Nat instead of inductive / coinductive types for simplicity
  | NatType
  | NatZ
  | NatS
  | NatInduction Term Term Term
  deriving (Eq, Ord)

-- TermSkeleton

data TermSkeleton =
    SVariable
  | SApplication TermSkeleton TermSkeleton

  | SSetType

  | SAbstraction TermSkeleton TermSkeleton
  | SFunctionType TermSkeleton TermSkeleton

  | STupleType [TermSkeleton]
  | STupleConstruct [TermSkeleton] [TermSkeleton]
  | STupleDestruct [TermSkeleton] TermSkeleton TermSkeleton
  | STupleIdentity [TermSkeleton] TermSkeleton

  | SCoTupleType [TermSkeleton]
  | SCoTupleConstruct [TermSkeleton] Int TermSkeleton
  | SCoTupleDestruct [TermSkeleton] TermSkeleton [TermSkeleton]

  | SIdentityType TermSkeleton TermSkeleton TermSkeleton
  | SIdentityReflective TermSkeleton TermSkeleton
  | SIdentityDestruct TermSkeleton TermSkeleton TermSkeleton

  | SNatType
  | SNatZ
  | SNatS
  | SNatInduction TermSkeleton TermSkeleton TermSkeleton
  deriving (Eq, Ord, Show)

skeleton :: Term -> TermSkeleton
skeleton (Variable i) = SVariable
skeleton (Application f t)                    = SApplication (skeleton $ f) (skeleton $ t)
skeleton SetType                              = SSetType
skeleton (Abstraction tau t)                  = SAbstraction (skeleton $ tau) (skeleton $ t)
skeleton (FunctionType tau sigma)             = SFunctionType (skeleton $ tau) (skeleton $ sigma)
skeleton (TupleType taus)                     = STupleType (skeleton <$> taus)
skeleton (TupleConstruct taus ts)             = STupleConstruct (skeleton <$> taus) (skeleton <$> ts)
skeleton (TupleDestruct taus sigma f)         = STupleDestruct (skeleton <$> taus) (skeleton $ sigma) (skeleton $ f)
skeleton (TupleIdentity taus t)               = STupleIdentity (skeleton <$> taus) (skeleton $ t)
skeleton (CoTupleType taus)                   = SCoTupleType (skeleton <$> taus)
skeleton (CoTupleConstruct taus j t)          = SCoTupleConstruct (skeleton <$> taus) j (skeleton $ t)
skeleton (CoTupleDestruct taus sigma fs)      = SCoTupleDestruct (skeleton <$> taus) (skeleton $ sigma) (skeleton <$> fs)
skeleton (IdentityType tau x y)               = SIdentityType (skeleton $ tau) (skeleton $ x) (skeleton $ y)
skeleton (IdentityReflective tau x)           = SIdentityReflective (skeleton $ tau) (skeleton $ x)
skeleton (IdentityDestruct tau x y)           = SIdentityDestruct (skeleton $ tau) (skeleton $ x) (skeleton $ y)
skeleton NatType                              = SNatType
skeleton NatZ                                 = SNatZ
skeleton NatS                                 = SNatS
skeleton (NatInduction tau f x)               = SNatInduction (skeleton $ tau) (skeleton $ f) (skeleton $ x)
--

showWithEnvironment :: [String] -> Term -> String
showWithEnvironment env = showWithEnvironment' 0
  where
    showWithEnvironment' :: Int -> Term -> String
    showWithEnvironment' i (Variable j)
      | j < i                                 =
          (yellow . (: []) . chr) (ord 'a' + i - j - 1)
      | j < i + length env                    =
          yellow $ env !! (j - i - 1)
      | otherwise                              =
          blue "E" ++ yellow (subScriptInt $ j - i - length env)
    showWithEnvironment' i (Application f t)   =
          "(" ++ showWithEnvironment' i f <+> showWithEnvironment' i t ++ ")"
    showWithEnvironment' i SetType             =
          blue "U"
    showWithEnvironment' i (Abstraction tau t) =
          "(" ++ blue "Λ" ++ "(" ++ (yellow . (: []) . chr) (ord 'a' + i) <+> red ":" <+> showWithEnvironment' i tau ++ ")" ++ red "." <+> showWithEnvironment' (i + 1) t ++ ")"
    showWithEnvironment' i (FunctionType tau sigma) =
          "(" ++ blue "Π" ++ "(" ++ (yellow . (: []) . chr) (ord 'a' + i) <+> red ":" <+> showWithEnvironment' i tau ++ ")" ++ red "." <+> showWithEnvironment' (i + 1) sigma ++ ")"
    showWithEnvironment' i (TupleType []) =
          blue "⊤"
    showWithEnvironment' i (TupleType (tau:taus)) =
          "(" ++ blue "Σ" ++ "(" ++ (yellow . (: []) . chr) (ord 'a' + i) <+> red ":" <+> showWithEnvironment' i tau ++ ")" ++ red "." <+> showWithEnvironment' (i + 1) (TupleType taus) ++ ")"
    showWithEnvironment' i (TupleConstruct [] []) =
          blue "()"
    showWithEnvironment' i (TupleConstruct (tau:taus) (t:ts)) =
          "(" ++ showWithEnvironment' i t ++ ", " ++ showWithEnvironment' i (TupleConstruct taus ts) ++ ")"
    showWithEnvironment' i (TupleConstruct taus ts) = blue "ERROR !!!!!"
    showWithEnvironment' i (TupleDestruct taus sigma f) =
          "(" ++ blue "match" <+> showWithEnvironment' i (TupleType taus) <+> red "to" <+> showWithEnvironment' (i + 1) sigma <+> red "with" <+> showWithEnvironment' i f ++ ")"
    showWithEnvironment' i (TupleIdentity _ t) =
          "(" ++ blue "TupleIdentity" <+> showWithEnvironment' i t ++ ")"
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
    showWithEnvironment' i (IdentityReflective tau x) =
          "(" ++ blue "IdR" <+> showWithEnvironment' i tau <+> showWithEnvironment' i x ++ ")"
    showWithEnvironment' i (IdentityDestruct tau x y) =
          "(" ++ blue "IdD" <+> showWithEnvironment' i tau <+> showWithEnvironment' i x <+> showWithEnvironment' i y ++ ")"
    showWithEnvironment' i NatType = blue "ℕ"
    showWithEnvironment' i NatZ = blue "Z"
    showWithEnvironment' i NatS = blue "S"
    showWithEnvironment' i (NatInduction tau f x) = blue "natind"

instance Show Term where
  show = showWithEnvironment []

liftBy' :: Int -> Int -> Term -> Term
liftBy' n i (Variable j)
  | j >= i                                       = Variable (j + n)
  | otherwise                                    = Variable j
liftBy' n i (Application f t)                    = Application (liftBy' n i $ f) (liftBy' n i $ t)
liftBy' n i SetType                              = SetType
liftBy' n i (Abstraction tau t)                  = Abstraction (liftBy' n i $ tau) (liftBy' n (i + 1) $ t)
liftBy' n i (FunctionType tau sigma)             = FunctionType (liftBy' n i $ tau) (liftBy' n (i + 1) $ sigma)
liftBy' n i (TupleType taus)                     = TupleType (uncurry (liftBy' n) <$> zip [i..] taus)
liftBy' n i (TupleConstruct taus ts)             = TupleConstruct (uncurry (liftBy' n) <$> zip [i..] taus) (liftBy' n i <$> ts)
liftBy' n i (TupleDestruct taus sigma f)         = TupleDestruct (uncurry (liftBy' n) <$> zip [i..] taus) (liftBy' n (i + 1) $ sigma) (liftBy' n i $ f)
liftBy' n i (TupleIdentity taus t)               = TupleIdentity (uncurry (liftBy' n) <$> zip [i..] taus) (liftBy' n i $ t)
liftBy' n i (CoTupleType taus)                   = CoTupleType (liftBy' n i <$> taus)
liftBy' n i (CoTupleConstruct taus j t)          = CoTupleConstruct (liftBy' n i <$> taus) j (liftBy' n i $ t)
liftBy' n i (CoTupleDestruct taus sigma fs)      = CoTupleDestruct (liftBy' n i <$> taus) (liftBy' n (i + 1) $ sigma) (liftBy' n i <$> fs)
liftBy' n i (IdentityType tau x y)               = IdentityType (liftBy' n i $ tau) (liftBy' n i $ x) (liftBy' n i $ y)
liftBy' n i (IdentityReflective tau x)           = IdentityReflective (liftBy' n i $ tau) (liftBy' n i $ x)
liftBy' n i (IdentityDestruct tau x y)           = IdentityDestruct (liftBy' n i $ tau) (liftBy' n i $ x) (liftBy' n i $ y)
liftBy' n i NatType                              = NatType
liftBy' n i NatZ                                 = NatZ
liftBy' n i NatS                                 = NatS
liftBy' n i (NatInduction tau f x)               = NatInduction (liftBy' n i $ tau) (liftBy' n i $ f) (liftBy' n i $ x)

liftBy :: Int -> Term -> Term
liftBy n = liftBy' n 0

liftListBy :: Int -> [Term] -> [Term]
liftListBy n ts = uncurry (liftBy' n) <$> zip [0..] ts

lift :: Term -> Term
lift = liftBy 1

liftList :: [Term] -> [Term]
liftList = liftListBy 1

lowerBy :: Int -> Term -> Term
lowerBy n = liftBy (-n)

lower :: Term -> Term
lower = lowerBy 1


-- List of dependencies, sorted by order of insertion (left to right)

dependencies :: Term -> [Int]
dependencies = dependencies' 0
  where
    dependencies' :: Int -> Term -> [Int]
    dependencies' i (Variable j)
      | j >= i                                           = [j - i]
      | otherwise                                        = []
    dependencies' i (Application f t)                    = unions' [dependencies' i $ f, dependencies' i $ t]
    dependencies' i SetType                              = []
    dependencies' i (Abstraction tau t)                  = unions' $ [dependencies' i $ tau, dependencies' (i + 1) $ t]
    dependencies' i (FunctionType tau sigma)             = unions' $ [dependencies' i $ tau, dependencies' (i + 1) $ sigma]
    dependencies' i (TupleType taus)                     = unions' $ (uncurry dependencies' <$> zip [i..] taus)
    dependencies' i (TupleConstruct taus ts)             = unions' $ (uncurry dependencies' <$> zip [i..] taus) ++ (dependencies' i <$> ts)
    dependencies' i (TupleDestruct taus sigma f)         = unions' $ (uncurry dependencies' <$> zip [i..] taus) ++ [dependencies' (i + 1) $ sigma, dependencies' i $ f]
    dependencies' i (TupleIdentity taus t)               = unions' $ (uncurry dependencies' <$> zip [i..] taus) ++ [dependencies' i $ t]
    dependencies' i (CoTupleType taus)                   = unions' $ (dependencies' i <$> taus)
    dependencies' i (CoTupleConstruct taus j t)          = unions' $ (dependencies' i <$> taus) ++ [dependencies' i $ t]
    dependencies' i (CoTupleDestruct taus sigma fs)      = unions' $ (dependencies' i <$> taus) ++ [dependencies' (i + 1) $ sigma] ++ (dependencies' i <$> fs)
    dependencies' i (IdentityType tau x y)               = unions' $ [dependencies' i $ tau, dependencies' i $ x, dependencies' i $ y]
    dependencies' i (IdentityReflective tau x)           = unions' $ [dependencies' i $ tau, dependencies' i $ x]
    dependencies' i (IdentityDestruct tau x y)           = unions' $ [dependencies' i $ tau, dependencies' i $ x, dependencies' i $ y]
    dependencies' i NatType                              = []
    dependencies' i NatZ                                 = []
    dependencies' i NatS                                 = []
    dependencies' i (NatInduction tau f x)               = unions' [dependencies' i $ tau, dependencies' i $ f, dependencies' i $ x]

    unions' :: [[Int]] -> [Int]
    unions'           = foldl union' []

    union' :: [Int] -> [Int] -> [Int]
    union' l []       = l
    union' l (x:xs)
      | x `elem` l    = union' l xs
      | otherwise     = union' (x:l) xs

applyPermutation :: [Int] -> Term -> Term
applyPermutation s = applyPermutation' 0
  where
    applyPermutation' i (Variable j)
      | j >= i + length s                                = Variable j
      | j >= i                                           = Variable $ i + s !! (j - i)
      | otherwise                                        = Variable j
    applyPermutation' i (Application f t)                = Application (applyPermutation' i $ f) (applyPermutation' i $ t)
    applyPermutation' i SetType                          = SetType
    applyPermutation' i (Abstraction tau t)              = Abstraction (applyPermutation' i $ tau) (applyPermutation' (i + 1) $ t)
    applyPermutation' i (FunctionType tau sigma)         = FunctionType (applyPermutation' i $ tau) (applyPermutation' (i + 1) $ sigma)
    applyPermutation' i (TupleType taus)                 = TupleType (uncurry (applyPermutation') <$> zip [i..] taus)
    applyPermutation' i (TupleConstruct taus ts)         = TupleConstruct (uncurry (applyPermutation') <$> zip [i..] taus) (applyPermutation' i <$> ts)
    applyPermutation' i (TupleDestruct taus sigma f)     = TupleDestruct (uncurry (applyPermutation') <$> zip [i..] taus) (applyPermutation' (i + 1) $ sigma) (applyPermutation' i $ f)
    applyPermutation' i (TupleIdentity taus t)           = TupleIdentity (uncurry (applyPermutation') <$> zip [i..] taus) (applyPermutation' i $ t)
    applyPermutation' i (CoTupleType taus)               = CoTupleType (applyPermutation' i <$> taus)
    applyPermutation' i (CoTupleConstruct taus j t)      = CoTupleConstruct (applyPermutation' i <$> taus) j (applyPermutation' i $ t)
    applyPermutation' i (CoTupleDestruct taus sigma fs)  = CoTupleDestruct (applyPermutation' i <$> taus) (applyPermutation' (i + 1) $ sigma) (applyPermutation' i <$> fs)
    applyPermutation' i (IdentityType tau x y)           = IdentityType (applyPermutation' i $ tau) (applyPermutation' i $ x) (applyPermutation' i $ y)
    applyPermutation' i (IdentityReflective tau x)       = IdentityReflective (applyPermutation' i $ tau) (applyPermutation' i $ x)
    applyPermutation' i (IdentityDestruct tau x y)       = IdentityDestruct (applyPermutation' i $ tau) (applyPermutation' i $ x) (applyPermutation' i $ y)
    applyPermutation' i NatType                          = NatType
    applyPermutation' i NatZ                             = NatZ
    applyPermutation' i NatS                             = NatS
    applyPermutation' i (NatInduction tau f x)           = NatInduction (applyPermutation' i $ tau) (applyPermutation' i $ f) (applyPermutation' i $ x)

-- Smart constructors and common types

applicationList :: Term -> [Term] -> Term
applicationList = foldl Application

abstractionList :: [Term] -> Term -> Term
abstractionList = flip $ foldr Abstraction

functionTypeList :: [Term] -> Term -> Term
functionTypeList = flip $ foldr FunctionType

unitType :: Term
unitType = TupleType []

unitValue :: Term
unitValue = TupleConstruct [] []

bottomType :: Term
bottomType = CoTupleType []

negate :: Term -> Term
negate t = FunctionType t bottomType

idCongType :: Term
idCongType =
  functionTypeList
  [ SetType
  , Variable 0
  , Variable 1
  , IdentityType (Variable 2) (Variable 1) (Variable 0)
  , SetType
  , FunctionType (Variable 4) (Variable 1)
  ] $ IdentityType (Variable 1) (Application (Variable 0) (Variable 4)) (Application (Variable 0) (Variable 3))

idCong :: Term
idCong = 
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

tupleProjection :: [Term] -> Int -> Term
tupleProjection taus j =
  let lt = length taus in
  TupleDestruct
    taus
    (Application (TupleDestruct (liftList taus) SetType $ abstractionList (liftList taus) $ liftBy (1+lt-j) $ taus !! j) (Variable 0))
    (abstractionList taus $ Variable (lt-1-j))

\end{code}
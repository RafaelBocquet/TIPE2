\begin{code}
module ProofSearch where

import Term
import Environment as Env
import Substitution as Subst
import Util
import Evaluation hiding (OtherError)

import Prelude hiding (lookup)
import Control.Applicative
import Control.Monad

import Data.Monoid
import Data.List as List

import Data.Sequence (Seq, ViewL (EmptyL, (:<)), (><))
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad.Trans.Either
import Control.Monad.Error.Class
import Control.Monad.Identity

import Debug.Trace

-- Error

data PCError =
    OtherError String
  | PCECError ECError

instance Show PCError where
  show (OtherError s)                          = "\n\t" ++ red "OtherError" <+> ":" <+> s
  show (PCECError s)                           = "\n\t" ++ red "Typecheck/Evaluation error" <+> ":" <+> show s

-- Monad

type PC a = EitherT PCError Identity a

runPC :: PC a -> Either PCError a
runPC = runIdentity . runEitherT

pcOfEC :: EC a -> PC a
pcOfEC = either (throwError . PCECError) return . runEC

-- ProofSearch

-- 

type ProofTerm = TypeIsomorphism

-- ProofSearch

-- ProofSearch from the original type
-- the first TypeMorphism is a type morphism from the original type type to a tuple of ProofSearchItems

data ProofSearchItem = ProofSearchItem
  { proofSearchItemEnvironment :: [ProofTerm]
  , proofSearchItemTerm :: ProofTerm }
  deriving (Show)

data ProofSearch = ProofSearch TypeIsomorphism [ProofSearchItem]
  deriving (Show)

--instance Monoid ProofSearch where
--  mempty = ProofSearch (trivialIsomorphism unitType) []
--  mappend (ProofSearch isom1 l1) (ProofSearch isom2 l2) =
--    let le1 = length l1 in
--    let le2 = length l2 in
--    flip ProofSearch (l1 ++ l2) $
--      TypeIsomorphism
--        ()
--        (TupleType $ uncurry liftBy <$> zip [0..] (l1 ++ l2))
--        ()
--        ()

makeProofSearchItem :: Environment -> Term -> ProofSearchItem
makeProofSearchItem (Environment env) t =
  let le        = length env in
  let env'      = (uncurry liftBy) <$> zip [1..] env in
  let depMap    = Map.fromList . zip [0..] $ dependencies . (env' !!) <$> [0 .. le - 1] in
  let depList   = depUnion env' [] (Seq.fromList $ dependencies t) in
  let permut    = reverse $ topoSort env' depMap depList in
  let nEnv      = applyPermutation permut <$> (env' !!) . (permut !!) <$> [0 .. le - 1] in
  let nT        = applyPermutation permut t in
  let nEnvIsom  = normalIsomorphism <$> uncurry lowerBy <$> zip [1..] nEnv in
  let nTIsom    = normalIsomorphism nT in
    -- traceShow (nEnvIsom, nTIsom)
    ProofSearchItem nEnvIsom nTIsom
    where
      depUnion :: [Term] -> [Int] -> Seq Int -> [Int]
      depUnion env l sq = case Seq.viewl sq of
        EmptyL -> l
        x :< xs -> if x `elem` l
          then depUnion env l xs
          else depUnion env (x:l) (xs >< (Seq.fromList $ dependencies $ env !! x))

      topoSort :: [Term] -> Map Int [Int] -> [Int] -> [Int]
      topoSort env depMap depList 
        | Map.null depMap               = []
        | otherwise                     =
            let next = minimum' env depList . Map.keys . Map.filter List.null $ depMap in
            next : topoSort env (List.delete next <$> Map.delete next depMap) (depUnion env depList $ Seq.singleton next)

      minimum' :: [Term] -> [Int] -> [Int] -> Int
      minimum' env depList [] = error "Should not happen"
      minimum' env depList (x:[]) = x
      minimum' env depList (x:xs) =
        let y = minimum' env depList xs in
        case compare (skeleton $ env !! x) (skeleton $ env !! y) of
          LT -> x
          EQ -> case (findIndex (== x) depList, findIndex (== y) depList) of
            (Just xI, Just yI) ->
              if xI < yI
                then x
                else y
            (Just _, Nothing) -> x
            (Nothing, Just _) -> y
            (Nothing, Nothing) -> traceShow "FIXME" $ x
          GT -> y

proofSearchItemIsomorphism :: ProofSearchItem -> TypeIsomorphism
proofSearchItemIsomorphism (ProofSearchItem env t) =
  let e = functionTypeList (isomorphismOriginalType <$> reverse env) (isomorphismOriginalType t) in
  let e' = functionTypeList (isomorphismMemberType <$> reverse env) (isomorphismMemberType t) in
  let le = length env in
  --traceShow (e, e') $ 
  --traceShow (isomorphismTo t) $
  --traceShow (isomorphismTo t) $
  --traceShow (Abstraction e $
  --      abstractionList (lift . isomorphismMemberType <$> reverse env) $
  --        Application (liftBy (le+1) $ isomorphismTo t) $
  --          applicationList (Variable le) (uncurry Application <$> zip (liftBy (le+1) . isomorphismFrom <$> env) (Variable <$> reverse [0..le-1]))) $
  --traceShow (runEC $ typecheck Env.empty e) $
  --traceShow (runEC $ typecheck Env.empty e') $
  --traceShow (uncurry liftBy <$> (zip (reverse [1..le]) $ isomorphismFrom <$> reverse env)) $
  TypeIsomorphism
    e
    e'
    ( Abstraction e $
        abstractionList (liftList $ isomorphismMemberType <$> reverse env) $
          Application (liftBy 0 $ isomorphismTo t) $
            applicationList
              (Variable le)
              (uncurry Application <$> zip (uncurry liftBy <$> (zip (reverse [1..le]) $ isomorphismFrom <$> reverse env)) (Variable <$> reverse [0..le-1]))
    )
    ( Abstraction e $
        abstractionList (liftList $ isomorphismOriginalType <$> reverse env) $
          Application (liftBy 0 $ isomorphismFrom t) $
            applicationList
              (Variable le)
              (uncurry Application <$> zip (uncurry liftBy <$> (zip (reverse [1..le]) $ isomorphismTo <$> reverse env)) (Variable <$> reverse [0..le-1]))
    )

makeProofSearch :: Environment -> Term -> ProofSearch
makeProofSearch gamma t =
  let prfItem = makeProofSearchItem gamma t in
  let prfIsom = proofSearchItemIsomorphism prfItem in
  let e = isomorphismOriginalType prfIsom in
  let e' = isomorphismMemberType prfIsom in
  --traceShow (runEC $ typecheck Env.empty e) $
  --traceShow (runEC $ typecheck Env.empty e') $
  --traceShow (runEC $ typecheck Env.empty $ isomorphismTo prfIsom) $
  --traceShow (runEC $ typecheck Env.empty $ isomorphismFrom prfIsom) $
  flip ProofSearch [prfItem] $
    TypeIsomorphism
      e
      (TupleType [e'])
      (Abstraction e $ TupleConstruct [lift e'] [Application (lift $ isomorphismTo prfIsom) (Variable 0)])
      (TupleDestruct [e'] (lift e) (lift $ isomorphismFrom prfIsom))

proofSearch :: Environment -> Term -> PC ProofSearch
proofSearch = proofSearch' 
  where
    proofSearch' gamma (FunctionType tau sigma)   =
      let gamma' = tau `Env.bind` gamma in
      proofSearch' gamma' sigma
      -- liftM mconcat $ (\(i, gamma') -> proofSearch gamma' $ liftBy i sigma) `mapM` gammas
    proofSearch' gamma e@(Application f t)        = return $ makeProofSearch gamma e
    proofSearch' gamma e@(Variable j)             = return $ makeProofSearch gamma e
    proofSearch' gamma e@SetType                  = return $ makeProofSearch gamma e
    proofSearch' gamma e@(TupleType taus)         = return $ makeProofSearch gamma e
    proofSearch' gamma e@(CoTupleType taus)       = return $ makeProofSearch gamma e
    proofSearch' gamma e@(IdentityType tau x y)   = return $ makeProofSearch gamma e
    proofSearch' gamma e@NatType                  = return $ makeProofSearch gamma e
    proofSearch' gamma _                          = throwError $ OtherError ""

    --proofSearchBind :: Term -> Environment -> [(Int, Environment)]
    --proofSearchBind t@(TupleType []) gamma        = [(0, t `Env.bind` gamma)]
    --proofSearchBind (TupleType taus) gamma        =
    --  foldr (\tau gammas ->
    --    mconcat $ (\(i, gamma') -> update1 (i+1) <$> (liftBy i tau) `proofSearchBind` gamma') <$> gammas
    --  ) [(-1, gamma)] taus
    --proofSearchBind t gamma                       =
    --  [(0, t `Env.bind` gamma)]

    --update1 :: Int -> (Int, Environment) -> (Int, Environment)
    --update1 j (i, gamma) = (i+j, gamma)

-- Isomorphisms

type TypeMorphism = Term

data TypeIsomorphism = TypeIsomorphism
  { isomorphismOriginalType :: Term
  , isomorphismMemberType :: Term
  , isomorphismTo :: TypeMorphism
  , isomorphismFrom :: TypeMorphism }
  deriving (Show)

trivialIsomorphism :: Term -> TypeIsomorphism
trivialIsomorphism tau = TypeIsomorphism tau tau (Abstraction tau $ Variable 0) (Abstraction tau $ Variable 0)

normalIsomorphism :: Term -> TypeIsomorphism
normalIsomorphism e               = trivialIsomorphism e
--normalIsomorphism gamma e@(Variable i)              = return $ trivialIsomorphism e
--normalIsomorphism gamma e@(Application f t)           = return $ trivialIsomorphism e
--  --fTy <- pcOfEC $ typecheck gamma f
--  --case fTy of
--  --  FunctionType tau sigma -> do
--  --    throwError $ OtherError "TODO"
--  --  _ -> throwError $ OtherError "Should not happen..."
--normalIsomorphism gamma e@SetType                  = return $ trivialIsomorphism e
--normalIsomorphism gamma e@(TupleType taus)         = return $ trivialIsomorphism e
--normalIsomorphism gamma e@(CoTupleType taus)       = return $ trivialIsomorphism e
--normalIsomorphism gamma e@(IdentityType tau x y)   = return $ trivialIsomorphism e
--  --TypeIsomorphism tauM tauT tauF <- normalIsomorphism gamma tau
--  ---- compare x and y, swap ?
--  --tau' <- pcOfEC $ normalise tauM
--  --x' <- pcOfEC $ normalise (Application tauT x) 
--  --y' <- pcOfEC $ normalise (Application tauT y)
--  --if skeleton x <= skeleton y
--  --  then return 
--  --  else
--  --let e' = IdentityType tauM (Application tauT x) (Application tauT y)
--  --return $ TypeIsomorphism
--  --  e'
--  --  (Abstraction e $ applicationList idCong
--  --    [ lift tau
--  --    , lift x
--  --    , lift y
--  --    , Variable 0
--  --    , lift tauM
--  --    , lift tauT
--  --    ]
--  --  )
--  --  (Abstraction e' $ applicationList idCong
--  --    [ lift tauM
--  --    , lift (Application tauT x)
--  --    , lift (Application tauT y)
--  --    , Variable 0
--  --    , lift tau
--  --    , lift tauF
--  --    ]
--  --  )
--normalIsomorphism gamma e@NatType                  = return $ trivialIsomorphism e
--normalIsomorphism gamma _                          = throwError $ OtherError ""

\end{code}
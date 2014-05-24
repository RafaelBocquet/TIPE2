module Pretty where

class PrettyLatex a where
  prettyLatex :: a -> String
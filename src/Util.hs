module Util where

import System.Console.ANSI
import Control.Applicative

red s    = setSGRCode [SetColor Foreground Vivid Red] ++ s ++ setSGRCode []
blue s   = setSGRCode [SetColor Foreground Vivid Blue] ++ s ++ setSGRCode []
yellow s = setSGRCode [SetColor Foreground Vivid Yellow] ++ s ++ setSGRCode []

subScriptInt :: Int -> String
subScriptInt i = subScriptInt' <$> show i
  where
    subScriptInt' '0' = '₀'
    subScriptInt' '1' = '₁'
    subScriptInt' '2' = '₂'
    subScriptInt' '3' = '₃'
    subScriptInt' '4' = '₄'
    subScriptInt' '5' = '₅'
    subScriptInt' '6' = '₆'
    subScriptInt' '7' = '₇'
    subScriptInt' '8' = '₈'
    subScriptInt' '9' = '₉'

(<+>) :: String -> String -> String
a <+> b = a ++ " " ++ b
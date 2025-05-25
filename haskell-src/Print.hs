module Print where

import Syntax
import Data.Text (unpack)

-- If the `Bool` is true, require parens around nontrivial `Tm`s.
ppTm :: Bool -> Tm -> String
ppTm _ (Var x) = unpack x
ppTm _ Univ = "★"
ppTm _ (Code x) = "<" ++ ppTm False x ++ ">"
ppTm _ (SbTm x τ) = ppTm True x ++ "[" ++ ppSb False τ ++ "]"
ppTm _ (Snd σ) = ppSb True σ ++ ".2"
ppTm False (Pi x μ t body) = "Π " ++ unpack x ++ " :[" ++ ppSb False μ ++ "] " ++ ppTm False t ++ " → " ++ ppTm False body
ppTm False (Lam x μ t body) = "λ " ++ unpack x ++ " :[" ++ ppSb False μ ++ "] " ++ ppTm False t ++ " → " ++ ppTm False body
ppTm False (App f x) = ppTm True f ++ " " ++ ppTm True x
ppTm True x = "(" ++ ppTm False x ++ ")"

-- If the `Bool` is true, require parens around nontrivial `Sb`s.
ppSb :: Bool -> Sb -> String
ppSb _ Id = "id"
ppSb _ Nil = ""
ppSb _ (SbSb σ τ) = ppSb True σ ++ "[" ++ ppSb False τ ++ "]"
ppSb _ (Fst σ) = ppSb True σ ++ ".1"
ppSb False (Cons σ x μ t a) = ppSb False σ ++ ", " ++ unpack x ++ " :[" ++ ppSb False μ ++ "] " ++ ppTm False t ++ " = " ++ ppTm False a
ppSb True σ = "(" ++ ppSb False σ ++ ")"


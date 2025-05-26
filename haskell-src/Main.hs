module Main (main) where

import qualified Parse
import Print
import qualified TypeSystem as Tc

import Data.Text (unpack)
import Data.Bifunctor (first)
import System.IO
import System.Exit (ExitCode(..))

data Error
  = ParseError Parse.Error
  | TypeError Tc.FullError

run :: String -> Either Error (String, String)
run src = do
  raw <- first ParseError (Parse.parse src)
  (ty,tm) <- first TypeError (Tc.tc raw)
  pure (ppTm False ty, ppTm False tm)

ppErr :: Error -> String
ppErr (ParseError Parse.WhileBracketing) = "Mismatched brackets. (Or mismatched Π, λ, or →.)\n"
ppErr (ParseError (Parse.WhileParsing Parse.EmptyTm)) = "Parsing failed: Tried to parse empty string as a term.\n"
ppErr (ParseError (Parse.WhileParsing (Parse.PiLamFailed x))) = "Parsing failed: Incorrectly structured Π or λ term.\n  " ++ x ++ "\n"
ppErr (ParseError (Parse.WhileParsing (Parse.BadSbElt x))) = "Parsing failed: Incorrectly structured substitution (after first comma).\n  " ++ x ++ "\n"
ppErr (ParseError (Parse.WhileParsing Parse.BadSbHead)) = "Parsing failed: Incorrectly structured substitution (before first comma).\n"
ppErr (ParseError (Parse.WhileParsing (Parse.UnrecognizedTerm x))) = "Parsing failed: Unrecognized term.\n  " ++ x ++ "\n"
ppErr (TypeError (Tc.FullError err when cx)) = concat
  [ case err of
      Tc.FailedToUnify t1 t2 -> "Failed to unify the following expressions:\n  " ++ ppTm False t1 ++ "\n  " ++ ppTm False t2
      Tc.NotInScope x -> "The variable `" ++ unpack x ++ "` is not in scope."
      Tc.NotAType t x -> "The term `" ++ ppTm False x ++ "` was expected to be a type, but it has type `" ++ ppTm False t ++ "`."
      Tc.NotAFunction t x -> "The term `" ++ ppTm False x ++ "` was expected to be a function, but it has type `" ++ ppTm False t ++ "`."
      Tc.CxIsEmpty -> "Tried to decompose the empty context into pieces."
  , "\n\n"
  , "When typechecking the following " ++ case when of
    Tc.WhenCheckingTm tm -> "term: \n  " ++ ppTm False tm
    Tc.WhenCheckingSb sb -> "substitution: \n  " ++ ppSb False sb
  , "\n\n"
  , "In the following context:\n"
  , concatMap (\(Tc.CxEntry x t) -> "  " ++ unpack x ++ " : " ++ ppTm False t ++ "\n") (reverse cx)
  ]

main :: IO ExitCode
main = do
  src <- hGetContents stdin
  case run src of
    Left err -> do
      hPutStr stderr (ppErr err)
      pure (ExitFailure 1)
    Right (ty,tm) -> do
      hPutStrLn stdout "Success!"
      hPutStrLn stdout ("Term: " ++ tm)
      hPutStrLn stdout ("Type: " ++ ty)
      pure ExitSuccess

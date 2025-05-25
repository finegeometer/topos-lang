{-# LANGUAGE ViewPatterns, TupleSections, LambdaCase #-}

module Parse (parse, Error(..), ParseError(..)) where

import Data.Bifunctor (first)
import Data.Char (isAlphaNum, isSpace)
import Data.List (uncons)
import Data.Text (Text, pack)
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Lazy

import Syntax

stripComment :: String -> String
stripComment ('-':'-':_) = []
stripComment (c:s) = c : stripComment s
stripComment [] = []

stripComments :: String -> String
stripComments = unlines . map stripComment . lines


data Token = Ident String | Other Char
  deriving (Show)

tokenize :: String -> [Token]
tokenize [] = []
tokenize ('Π':s) = Other 'Π' : tokenize s
tokenize ('λ':s) = Other 'λ' : tokenize s
tokenize (c:s) | isSpace c = tokenize s
tokenize s@(c:_) | isAlphaNum c = tokenize' [] s
tokenize (c:s) = Other c : tokenize s

tokenize' :: String -> String -> [Token]
tokenize' i (c:s) | isAlphaNum c = tokenize' (c : i) s
tokenize' i s = Ident (reverse i) : tokenize s



data Bracket = Round | Square | Angle | BPi | BLam
  deriving (Show)
type TokenForest = [TokenTree]
data TokenTree = Token Token | Bracket Bracket TokenForest | Suffix TokenTree Suffix
  deriving (Show)


bracket :: [Token] -> Maybe TokenForest
bracket = evalStateT (bracket'' (\_ -> True))

bracket' :: StateT [Token] Maybe TokenTree
bracket' = StateT uncons >>= \case
  Other '(' -> do x <- bracket'' (\case Other ')' -> False; _ -> True); _ <- StateT uncons; pure (Bracket Round  x)
  Other '[' -> do x <- bracket'' (\case Other ']' -> False; _ -> True); _ <- StateT uncons; pure (Bracket Square x)
  Other '<' -> do x <- bracket'' (\case Other '>' -> False; _ -> True); _ <- StateT uncons; pure (Bracket Angle  x)
  Other 'Π' -> do x <- bracket'' (\case Other '→' -> False; _ -> True); _ <- StateT uncons; pure (Bracket BPi    x)
  Other 'λ' -> do x <- bracket'' (\case Other '→' -> False; _ -> True); _ <- StateT uncons; pure (Bracket BLam   x)
  Other ')' -> lift Nothing
  Other ']' -> lift Nothing
  Other '>' -> lift Nothing
  Other '→' -> lift Nothing
  t -> pure (Token t)

bracket'' :: (Token -> Bool) -> StateT [Token] Maybe [TokenTree]
bracket'' p = get >>= \case
  x:_ | p x -> liftM2 (:) bracket' (bracket'' p)
  _ -> pure []



data Suffix = Subst TokenForest | Dot TokenTree
  deriving (Show)

suffix :: TokenForest -> TokenForest
suffix (t : Bracket Square σ : ts) = suffix (Suffix t (Subst σ) : ts)
suffix (t : Token (Other '.') : t' : ts) = suffix (Suffix t (Dot t') : ts)
suffix (t : ts) = suffix' t : suffix ts
suffix [] = []

suffix' :: TokenTree -> TokenTree
suffix' (Token t) = Token t
suffix' (Bracket b f) = Bracket b (suffix f)
suffix' (Suffix t (Subst f)) = Suffix (suffix' t) (Subst (suffix f))
suffix' (Suffix t (Dot t')) = Suffix (suffix' t) (Dot (suffix' t'))


data ParseError
  = EmptyTm
  | PiLamFailed String
  | BadSbElt String
  | BadSbHead

split :: (a -> Bool) -> [a] -> [[a]]
split p [] = [[]]
split p (x : xs) = if p x then [] : split p xs else let y:ys = split p xs in (x:y):ys

parseTm :: TokenForest -> Either ParseError Tm
parseTm (break (\case Bracket BPi _ -> True; Bracket BLam _ -> True; _ -> False) -> (ts1, ts2)) = do
  ts1 <- mapM parseTm' ts1
  foldl1 App <$> case ts2 of
    [] -> case ts1 of
      [] -> Left EmptyTm
      _ -> pure ts1
    Bracket BPi  (Token (Ident x) : Suffix (Token (Other ':')) (Subst μ) : t) : body -> fmap (\x->ts1++[x]) (liftM3 (Pi  (pack x)) (parseSb μ) (parseTm t) (parseTm body))
    Bracket BLam (Token (Ident x) : Suffix (Token (Other ':')) (Subst μ) : t) : body -> fmap (\x->ts1++[x]) (liftM3 (Lam (pack x)) (parseSb μ) (parseTm t) (parseTm body))
    forest -> Left (PiLamFailed (show forest))

parseTm' :: TokenTree -> Either ParseError Tm
parseTm' (Bracket Round a) = parseTm a
parseTm' (Bracket Angle a) = fmap Code (parseTm a)
parseTm' (Token (Ident x)) = pure (Var (pack x))
parseTm' (Token (Other '★')) = pure Univ
parseTm' (Suffix σ (Dot (Token (Ident "2")))) = fmap Snd (parseSb' σ)
parseTm' (Suffix a (Subst τ)) = liftM2 SbTm (parseTm' a) (parseSb τ)

parseSb :: TokenForest -> Either ParseError Sb
parseSb forest =
  let
    (hd,tl) = case split (\case Token (Other ',') -> True; _ -> False) forest of
      []:tl -> (pure Nil, tl)
      [σ]:tl -> (parseSb' σ, tl)
      hd:tl -> (pure Nil, hd:tl)
  in
    liftM2 (foldl (\σ (x,μ,t,a) -> Cons σ x μ t a)) hd $ forM tl $ \case
      Token (Ident x) : Suffix (Token (Other ':')) (Subst μ) : (break (\case Token (Other '=') -> True; _ -> False) -> (t, Token (Other '=') : a)) ->
        liftM3 (pack x,,,) (parseSb μ) (parseTm t) (parseTm a)
      forest -> Left (BadSbElt (show forest))

parseSb' :: TokenTree -> Either ParseError Sb
parseSb' (Bracket Round σ) = parseSb σ
parseSb' (Token (Ident "id")) = pure Id
parseSb' (Suffix σ (Dot (Token (Ident "1")))) = fmap Fst (parseSb' σ)
parseSb' (Suffix σ (Subst τ)) = liftM2 SbSb (parseSb' σ) (parseSb τ)
parseSb' _ = Left BadSbHead




data Error
  = WhileBracketing
  | WhileParsing ParseError

parse :: String -> Either Error Tm
parse (stripComments -> src) = do
  let tokens = tokenize src
  forest <- case bracket tokens of Just x -> Right x; Nothing -> Left WhileBracketing
  first WhileParsing (parseTm (suffix forest))

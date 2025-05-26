module Raw where

open import Agda.Builtin.String using (String)

data Raw : Set
data RawSb : Set

data Raw where
  var : String → Raw
  univ : Raw
  code : Raw → Raw
  _[_] : Raw → RawSb → Raw
  Π_∶_,_ : String → Raw → Raw → Raw
  lam_∶_,_ : String → Raw → Raw → Raw
  _＠_ : Raw → Raw → Raw
  π₂ : RawSb → Raw

data RawSb where
  id : RawSb
  _[_] : RawSb → RawSb → RawSb
  ε : RawSb
  _,_∶_:=_ : RawSb → String → Raw → Raw → RawSb
  π₁ : RawSb → RawSb


{-# FOREIGN GHC
  import Data.Text (Text)
  data Tm
    = Var Text
    | Univ
    | Code Tm
    | SbTm Tm Sb
    | Pi Text Tm Tm
    | Lam Text Tm Tm
    | App Tm Tm
    | Snd Sb
  data Sb
    = Id
    | SbSb Sb Sb
    | Nil
    | Cons Sb Text Tm Tm
    | Fst Sb
#-}
{-# COMPILE GHC Raw = data Tm (Var | Univ | Code | SbTm | Pi | Lam | App | Snd) #-}
{-# COMPILE GHC RawSb = data Sb (Id | SbSb | Nil | Cons | Fst) #-}

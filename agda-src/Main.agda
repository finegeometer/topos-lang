module Main where

open import Raw using (Raw; RawSb)
import Tc
open import Readback using (rb-ty; rb-val; rb-sb)

open import Agda.Builtin.Sigma using (_,_; Σ)
open import Data.Sum.Base using (inj₁; inj₂)

import Foreign.Haskell as FFI
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

{-# FOREIGN GHC import Data.Text (Text) #-}

data Error : Set where
  failed-to-unify : Raw → Raw → Error
  not-in-scope : String → Error
  -- type then value
  not-a-type : Raw → Raw → Error
  not-a-function : Raw → Raw → Error
  cx-is-empty : Error

{-# FOREIGN GHC
  data Error
    = FailedToUnify MAlonzo.Code.Raw.Tm MAlonzo.Code.Raw.Tm
    | NotInScope Text
    | NotAType MAlonzo.Code.Raw.Tm MAlonzo.Code.Raw.Tm
    | NotAFunction MAlonzo.Code.Raw.Tm MAlonzo.Code.Raw.Tm
    | CxIsEmpty
#-}
{-# COMPILE GHC Error = data Error (FailedToUnify | NotInScope | NotAType | NotAFunction | CxIsEmpty) #-}

record CxEntry : Set where
  field
    name : String
    modality : RawSb
    ty : Raw
{-# FOREIGN GHC data CxEntry = CxEntry Text MAlonzo.Code.Raw.Sb MAlonzo.Code.Raw.Tm #-}
{-# COMPILE GHC CxEntry = data CxEntry (CxEntry) #-}

record FullError : Set where
  field
    err : Error
    when-checking : Tc.WhenChecking
    in-cx : List CxEntry
{-# FOREIGN GHC data FullError = FullError Error MAlonzo.Code.Tc.WhenChecking [CxEntry] #-}
{-# COMPILE GHC FullError = data FullError (FullError) #-}

private
  mk-error : Tc.Error → Error
  mk-error (Tc.failed-to-unify A A')     = failed-to-unify (rb-ty A) (rb-ty A')
  mk-error (Tc.not-in-scope x)           = not-in-scope x
  mk-error (Tc.not-a-type {A = A} a)     = not-a-type (rb-ty A) (rb-val a)
  mk-error (Tc.not-a-function {A = A} a) = not-a-function (rb-ty A) (rb-val a)
  mk-error Tc.cx-is-empty                = cx-is-empty

  mk-cx-list : {Γ : _} → Tc.Names Γ → List CxEntry
  mk-cx-list Tc.ε = []
  mk-cx-list (Tc._,_ {μ = μ} {A = A} names x) = record { name = x ; modality = rb-sb μ ; ty = rb-ty A } ∷ mk-cx-list names

  mk-full-error : (Σ Tc.Error λ _ → Σ Tc.WhenChecking λ _ → Tc.InCx) → FullError
  mk-full-error (err , when , Tc.in-cx cx) = record { err = mk-error err ; when-checking = when ; in-cx = mk-cx-list cx }

tc : Raw → FFI.Either FullError (FFI.Pair Raw Raw)
tc a with Tc.tc-val Tc.ε a
... | inj₂ (A , a) = FFI.right (Readback.rb-ty A FFI., Readback.rb-val a)
... | inj₁ x = FFI.left (mk-full-error x)

{-# COMPILE GHC tc as tc #-}

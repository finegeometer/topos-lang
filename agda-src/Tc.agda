module Tc where

open import Raw
open import Lang
open import Unify

open import Agda.Builtin.String using (String; primStringEquality)
open import Agda.Builtin.Bool using (true; false)

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Function using (case_of_)

private variable
  Γ Δ : Cx

--------------------------------------------------------------------------------

data Names : Cx → Set where
  ε : Names ε
  _,_ : {Γ Δ : Cx} {μ : Sb Γ Δ} {A : Ty Δ} → Names Γ → String → Names (Γ ,[ μ ] A)

open import Data.Product using (_,_; _×_; ∃-syntax)

--------------------------------------------------------------------------------

data Error : Set where
  failed-to-unify : Ty Γ → Ty Γ → Error
  not-in-scope : String → Error
  not-a-type : {A : Ty Γ} → Val Γ A → Error
  not-a-function : {A : Ty Γ} → Val Γ A → Error
  cx-is-empty : Error

data WhenChecking : Set where
  when-tm : Raw → WhenChecking
  when-sb : RawSb → WhenChecking
{-# FOREIGN GHC data WhenChecking = WhenCheckingTm MAlonzo.Code.Raw.Tm | WhenCheckingSb MAlonzo.Code.Raw.Sb #-}
{-# COMPILE GHC WhenChecking = data WhenChecking (WhenCheckingTm | WhenCheckingSb) #-}

data InCx : Set where
  in-cx : Names Γ → InCx

import Effect.Monad
import Effect.Empty
import Level
import Data.Sum.Effectful.Left (Error × WhenChecking × InCx) Level.0ℓ as Sum
open Sum using (Sumₗ)
open Effect.Monad.RawMonad Sum.monad
err : {X : Set} → Error → WhenChecking → InCx → Sumₗ X
err x y z = Effect.Empty.RawEmpty.empty (Sum.empty (x , y , z))

open import Relation.Nullary.Decidable using (yes; no)

unify : (A A' : Ty Γ) → WhenChecking → InCx → Sumₗ (A ≡ A')
unify A A' y z with dec-ty A A'
... | yes pf = pure pf
... | no _ = err (failed-to-unify A A') y z

--------------------------------------------------------------------------------

sb-lookup : WhenChecking → InCx → Sb Γ Δ → Names Δ → String → Sumₗ (∃[ A ] Val Γ A)
sb-lookup wc ix ε ε x = err (not-in-scope x) wc ix
sb-lookup wc ix (σ , a) (names , y) x with primStringEquality y x
... | true = pure (_ , a)
... | false = sb-lookup wc ix σ names x

var-lookup : Names Γ → String → Sumₗ (∃[ A ] Val Γ A)
var-lookup names x = sb-lookup (when-tm (Raw.var x)) (in-cx names) Lang.id names x


tc-ty : Names Γ → Raw → Sumₗ (Ty Γ)
tc-val : Names Γ → Raw → Sumₗ (∃[ A ] Val Γ A)
tc-sb : Names Γ → RawSb → Sumₗ (∃[ Δ ] Names Δ × Sb Γ Δ)

tc-ty names A = do
  sb _ univ , A ← tc-val names A
    where _ , x → err (not-a-type x) (when-tm A) (in-cx names)
  pure (el A)


tc-val names (Raw.var x) = var-lookup names x
tc-val names univ = pure (sb Lang.id univ , sb Lang.id code sb Lang.id univ)
tc-val names (code A) = do
  A ← tc-ty names A
  pure (sb Lang.id univ , sb Lang.id code A)
tc-val names (a [ σ ]) = do
  _ , names , σ ← tc-sb names σ
  A , a ← tc-val names a
  pure (sb-ty σ A , sb-val σ a)
tc-val names (Π x :[ μ ] A , B) = do
  _ , names' , μ ← tc-sb names μ
  A ← tc-ty names' A
  B ← tc-ty (names , x) B
  pure (sb Lang.id univ , sb Lang.id code (sb Lang.id pi[ μ ] A , B))
tc-val names (lam x :[ μ ] A , body) = do
  _ , names' , μ ← tc-sb names μ
  A ← tc-ty names' A
  B , body ← tc-val (names , x) body
  pure ((sb Lang.id pi[ μ ] A , B) , sb Lang.id lam body)
tc-val names (e₁ ＠ e₂) = do
  (sb σ pi[ μ ] A , B) , f ← tc-val names e₁
    where _ , x → err (not-a-function x) (when-tm (e₁ ＠ e₂)) (in-cx names)
  A' , a ← tc-val names e₂
  refl ← unify (sb-ty (sb-sb σ μ) A) A' (when-tm (e₁ ＠ e₂)) (in-cx names)
  pure (sb-ty (σ , a) B , apply f a)
tc-val names (π₂ σ) = do
  (_ ,[ μ ] A) , _ , (σ , a) ← tc-sb names σ
    where _ → err cx-is-empty (when-tm (π₂ σ)) (in-cx names)
  pure (sb-ty (sb-sb σ μ) A , a)


tc-sb names RawSb.id = pure (_ , names , Lang.id)
tc-sb names (σ [ τ ]) = do
  _ , names , σ ← tc-sb names σ
  _ , names , τ ← tc-sb names τ
  pure (_ , names , sb-sb σ τ)
tc-sb names ε = pure (ε , ε , ε)
tc-sb names sb@(σ , x :[ μ ] A := a) = do
  _ , names' , σ ← tc-sb names σ
  _ , names'' , μ ← tc-sb names' μ
  stated-type ← tc-ty names'' A
  inferred-type , a ← tc-val names a
  refl ← unify inferred-type (sb-ty (sb-sb σ μ) stated-type) (when-sb sb) (in-cx names)
  pure ((_ ,[ μ ] stated-type) , (names' , x) , (σ , a))
tc-sb names (π₁ σ) = do
  _ , (names' , _) , (σ , _) ← tc-sb names σ
    where _ → err cx-is-empty (when-sb (π₁ σ)) (in-cx names)
  pure (_ , names' , σ)


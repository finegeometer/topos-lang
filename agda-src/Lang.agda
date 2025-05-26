{-# OPTIONS --no-termination-check --no-positivity-check #-}

module Lang where

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)

unsafeCoerce : {X : Set} (P : X → Set) (x₁ x₂ : X) → P x₁ → P x₂
unsafeCoerce P _ _ = subst P trustMe

--------------------------------------------------------------------------------

data Cx : Set
data Sb : Cx → Cx → Set

private variable
  Γ Δ Ξ : Cx
  σ τ : Sb Γ Δ

sb-sb : Sb Γ Δ → Sb Δ Ξ → Sb Γ Ξ
id : Sb Γ Γ

--------------------------------------------------------------------------------

data Ty : Cx → Set
data Val : (Γ : Cx) → Ty Γ → Set
data Neu : (Γ : Cx) → Ty Γ → Set

private variable A B Z : Ty Γ

data Cx where
  ε : Cx
  _,_ : (Γ : Cx) → Ty Γ → Cx

--------------------------------------------------------------------------------

sb-ty : Sb Γ Δ → Ty Δ → Ty Γ
sb-val : (σ : Sb Γ Δ) → Val Δ A → Val Γ (sb-ty σ A)
sb-neu : (σ : Sb Γ Δ) → Neu Δ A → Val Γ (sb-ty σ A)

data Sb where
  ε : Sb Γ ε
  _,_ : (σ : Sb Ξ Γ) → Val Ξ (sb-ty σ A) → Sb Ξ (Γ , A)

sb-sb σ ε = ε
sb-sb σ (_,_ {A = A} τ a) = sb-sb σ τ , unsafeCoerce (Val _)
  (sb-ty σ (sb-ty τ A))
  (sb-ty (sb-sb σ τ) A)
  (sb-val σ a)

--------------------------------------------------------------------------------

data _⊆_ : Cx → Cx → Set where
  refl : Γ ⊆ Γ
  step : (Γ , A) ⊆ Δ → Γ ⊆ Δ

wk : Γ ⊆ Δ → Sb Δ Γ
id = wk refl

var : (x : (Γ , A) ⊆ Δ) → Val Δ (sb-ty (wk (step x)) A)

wk {ε} _ = ε
wk {Γ , A} x = wk (step x) , var x

--------------------------------------------------------------------------------

data Ty where
  sb_pi_,_ : Sb Ξ Γ → (A : Ty Γ) → Ty (Γ , A) → Ty Ξ
  sb_univ : Sb Ξ Γ → Ty Ξ
  el' : Neu Γ (sb σ univ) → Ty Γ

data Val where
  neu : Neu Γ A → Val Γ A
  -- neu' : {t : Neu Γ (sb σ univ)} → Neu Γ (el' t) → Val Γ (el' t)
  sb_lam_ : (σ : Sb Ξ Γ) → Val (Γ , A) B → Val Ξ (sb σ pi A , B)
  sb_code_ : (σ : Sb Ξ Γ) → Ty Γ → Val Ξ (sb σ univ)

data Neu where
  var' : (x : (Γ , A) ⊆ Δ) → Z ≡ sb-ty (wk (step x)) A → Neu Δ Z
  sb_app_,_⟨_⟩ : (τ : Sb Ξ Γ) → Neu Γ (sb σ pi A , B) → (a : Val Γ (sb-ty σ A)) → Z ≡ sb-ty (sb-sb τ (σ , a)) B → Neu Ξ Z

--------------------------------------------------------------------------------

el : Val Γ (sb σ univ) → Ty Γ
el (neu t) = el' t
el (sb σ code A) = sb-ty σ A

var x = neu (var' x refl)

--------------------------------------------------------------------------------

sb-var : (σ : Sb Ξ Δ) → (x : (Γ , A) ⊆ Δ) → Val Ξ (sb-ty σ (sb-ty (wk (step x)) A))

sb-ty σ (sb τ pi A , B) = sb sb-sb σ τ pi A , B
sb-ty σ (sb τ univ) = sb sb-sb σ τ univ
sb-ty σ (el' t) = el (sb-neu σ t)
sb-val σ (neu x) = sb-neu σ x
sb-val σ (sb τ lam body) = sb sb-sb σ τ lam body
sb-val σ (sb τ code t) = sb sb-sb σ τ code t
sb-neu σ (var' x refl) = sb-var σ x
sb-neu σ (sb τ app fun , arg ⟨ refl ⟩) = neu (sb sb-sb σ τ app fun , arg ⟨ trustMe ⟩)

--------------------------------------------------------------------------------

weaken : Γ ⊆ Δ → Sb Ξ Δ → Sb Ξ Γ
weaken refl σ = σ
weaken (step x) σ with weaken x σ
... | out , _ = out

sb-var {A = A} σ x with weaken x σ
... | τ , out = unsafeCoerce (Val _)
  (sb-ty τ A)
  (sb-ty σ (sb-ty (wk (step x)) A))
  out

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

apply : Val Γ (sb σ pi A , B) → (a : Val Γ (sb-ty σ A)) → Val Γ (sb-ty (σ , a) B)
apply (neu f) a = neu sb id app f , a ⟨ trustMe ⟩
apply (sb σ lam body) a = sb-val (σ , a) body

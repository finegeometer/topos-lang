open import Lang
open import Relation.Nullary.Reflects
open import Relation.Nullary.Decidable.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst)
open import Relation.Binary.PropositionalEquality.WithK using (≡-irrelevant)
open import Agda.Builtin.Bool using (false; true)
open import Function.Base using (_∘_; _|>_)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_; Σ-syntax)

private
  -- Function order reversed for better chaining.
  bind′ : {A B : Set} → (B → A) → (A → Dec B) → Dec A → Dec B
  does (bind′ g f (false because pf)) = false
  proof (bind′ g f (false because ofⁿ ¬a)) = ofⁿ (¬a ∘ g)
  bind′ g f (true because ofʸ a) = f a

private variable
  Γ Δ Δ' : Cx
  A : Ty Γ

dec-ty : DecidableEquality (Ty Γ)
dec-val : DecidableEquality (Val Γ A)
dec-neu : DecidableEquality (Neu Γ A)
dec-sb : (σ : Sb Γ Δ) (σ' : Sb Γ Δ') → Dec (Σ[ pf ∈ Δ ≡ Δ' ] subst (Sb Γ) pf σ ≡ σ')
dec-var : (p : Δ ⊆ Γ) (p' : Δ' ⊆ Γ) → Dec (Σ[ pf ∈ Δ ≡ Δ' ] subst (λ Δ → Δ ⊆ Γ) pf p ≡ p')

dec-ty (sb σ univ) (sb σ' univ) =
  dec-sb σ σ' |> map′ (λ {(refl , refl) → refl}) (λ {refl → refl , refl})
dec-ty (el' {σ = σ} t) (el' {σ = σ'} t') =
  dec-sb σ σ' |> bind′ (λ {refl → refl , refl}) λ {(refl , refl) →
  dec-neu t t' |> map′ (λ {refl → refl}) λ {refl → refl}}
dec-ty (sb σ pi A , B) (sb σ' pi A' , B') =
  dec-sb σ σ' |> bind′ (λ {refl → refl , refl}) λ {(refl , refl) →
  dec-ty A A' |> bind′ (λ {refl → refl}) λ {refl →
  dec-ty B B' |> map′ (λ {refl → refl}) λ {refl → refl}}}

dec-ty (sb _ univ)          (el' _)              = no λ ()
dec-ty (sb _ univ)          (sb _ pi _ , _) = no λ ()
dec-ty (el' _)              (sb _ univ)          = no λ ()
dec-ty (el' _)              (sb _ pi _ , _) = no λ ()
dec-ty (sb _ pi _ , _) (sb _ univ)          = no λ ()
dec-ty (sb _ pi _ , _) (el' _)              = no λ ()

dec-val (neu a) (neu a') =
  dec-neu a a' |> map′ (λ {refl → refl}) (λ {refl → refl})
dec-val (sb σ lam a) (sb σ' lam a') =
  dec-sb σ σ' |> bind′ (λ {refl → refl , refl}) λ {(refl , refl) →
  dec-val a a' |> map′ (λ {refl → refl}) (λ {refl → refl})}
dec-val (sb σ code A) (sb σ' code A') =
  dec-sb σ σ' |> bind′ (λ {refl → refl , refl}) λ {(refl , refl) →
  dec-ty A A' |> map′ (λ {refl → refl}) (λ {refl → refl})}

dec-val (neu _) (sb _ lam _)  = no λ ()
dec-val (neu _) (sb _ code _) = no λ ()
dec-val (sb _ lam _)  (neu _) = no λ ()
dec-val (sb _ code _) (neu _) = no λ ()

dec-neu (var' x pf) (var' x' pf') =
  dec-var x x' |> bind′ (λ {refl → refl , refl}) λ {(refl , refl) →
  yes (≡-irrelevant pf pf') |> map′ (λ {refl → refl}) λ {refl → refl}}
dec-neu (sb_app_,_⟨_⟩ {σ = σ} {A = A} {B = B} τ a b pf) (sb_app_,_⟨_⟩ {σ = σ'} {A = A'} {B = B'} τ' a' b' pf') =
  dec-sb τ τ' |> bind′ (λ {refl → refl , refl}) λ {(refl , refl) →
  dec-sb σ σ' |> bind′ (λ {refl → refl , refl}) λ {(refl , refl) →
  dec-ty A A' |> bind′ (λ {refl → refl}) λ {refl →
  dec-ty B B' |> bind′ (λ {refl → refl}) λ {refl →
  dec-neu a a' |> bind′ (λ {refl → refl}) λ {refl →
  dec-val b b' |> bind′ (λ {refl → refl}) λ {refl →
  yes (≡-irrelevant pf pf') |> map′ (λ {refl → refl}) λ {refl → refl}}}}}}}

dec-neu (var' _ _) (sb _ app _ , _ ⟨ _ ⟩) = no λ ()
dec-neu (sb _ app _ , _ ⟨ _ ⟩) (var' _ _) = no λ ()

dec-sb ε ε = yes (refl , refl)
dec-sb (_,_ {A = A} σ a) (_,_ {A = A'} σ' a') =
  dec-sb σ σ' |> bind′ (λ {(refl , refl) → refl , refl}) λ {(refl , refl) →
  dec-ty A A' |> bind′ (λ {(refl , refl) → refl}) λ {refl →
  dec-val a a' |> map′ (λ {refl → refl , refl}) λ {(refl , refl) → refl}}}

dec-sb ε (_ , _) = no λ ()
dec-sb (_ , _) ε = no λ ()

-- Can easily be proven by reasoning about the lengths of contexts, but that brings in too many imports.
private postulate ext-not-⊆ : (Γ , A) ⊆ Γ → ⊥

dec-var refl refl = yes (refl , refl)
dec-var (step p) (step p') = dec-var p p' |> map′ (λ {(refl , refl) → refl , refl}) λ {(refl , refl) → refl , refl}

dec-var refl (step p') = no λ {(refl , _) → ext-not-⊆ p'}
dec-var (step p) refl = no λ {(refl , _) → ext-not-⊆ p}

module Readback where

open import Raw
open import Lang

private variable
  Γ Δ : Cx
  A : Ty Γ

rb-ty : Ty Γ → Raw
rb-val : Val Γ A → Raw
rb-neu : Neu Γ A → Raw
rb-sb : Sb Γ Δ → RawSb
rb-wk : Γ ⊆ Δ → RawSb

rb-ty (sb σ pi A , B) = (Π "_" ∶ rb-ty A , rb-ty B) [ rb-sb σ ]
rb-ty sb σ univ = univ [ rb-sb σ ]
rb-ty (el' t) = rb-neu t

rb-val (neu a) = rb-neu a
rb-val (sb_lam_ {A = A} σ body) = (lam "_" ∶ rb-ty A , rb-val body) [ rb-sb σ ]
rb-val (sb σ code A) = code (rb-ty A) [ rb-sb σ ]

rb-neu (var' x _) = π₂ (rb-wk x)
rb-neu app' f , a ⟨ _ ⟩ = rb-neu f ＠ rb-val a

rb-sb ε = ε
rb-sb {Δ = Δ , A} (_,_ σ a) = rb-sb σ , "_" ∶ rb-ty A := rb-val a

rb-wk refl = RawSb.id
rb-wk (step p) = π₁ (rb-wk p)

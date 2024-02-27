```agda
open import Cat.Prelude
open import Cat.Instances.Product
open import Cat.Monoidal.Base
open import Cat.Functor.Coherence
open import Cat.Functor.Base
open import Cat.Monoidal.Strength
open import Cat.Diagram.Monad

import Cat.Reasoning
import Cat.Functor.Reasoning

module Cat.Monoidal.Monad.Strength where

module _ {o ℓ} {C : Precategory o ℓ} (Cᵐ : Monoidal-category C) (M-monad : Monad C) where
  open Cat.Reasoning C
  open Monoidal-category Cᵐ
  open Monad M-monad
  private
    module M = Cat.Functor.Reasoning M

  record Left-monad-strength : Type (o ⊔ ℓ) where
    field
      functor-strength : Left-strength Cᵐ M

    open Left-strength functor-strength public

    field
      left-strength-η : ∀ {A B} → σ ∘ (id ⊗₁ η B) ≡ η (A ⊗ B)
      left-strength-μ : ∀ {A B} → σ ∘ (id ⊗₁ μ B) ≡ μ (A ⊗ B) ∘ M₁ σ ∘ σ

  record Right-monad-strength : Type (o ⊔ ℓ) where
    field
      functor-strength : Right-strength Cᵐ M

    open Right-strength functor-strength public

    field
      right-strength-η : ∀ {A B} → τ ∘ (η A ⊗₁ id) ≡ η (A ⊗ B)
      right-strength-μ : ∀ {A B} → τ ∘ (μ A ⊗₁ id) ≡ μ (A ⊗ B) ∘ M₁ τ ∘ τ

  record Monad-strength : Type (o ⊔ ℓ) where
    field
      strength-left : Left-monad-strength
      strength-right : Right-monad-strength

    open Left-monad-strength strength-left public
    open Right-monad-strength strength-right public

    field
      strength-α→ : ∀ {A B C}
        → M₁ (α→ A B C) ∘ τ ∘ (σ ⊗₁ id) ≡ σ ∘ (id ⊗₁ τ) ∘ α→ A (M₀ B) C

    functor-strength' : Strength Cᵐ M
    functor-strength' .Strength.strength-left = strength-left .Left-monad-strength.functor-strength
    functor-strength' .Strength.strength-right = strength-right .Right-monad-strength.functor-strength
    functor-strength' .Strength.strength-α→ = strength-α→

    left-φ right-φ : -⊗- F∘ (M F× M) => M F∘ -⊗-
    left-φ = (mult ◂ -⊗-) ∘nt nat-assoc-to (M ▸ left-strength) ∘nt τ'
      where
        unquoteDecl τ' = cohere-into τ' (-⊗- F∘ (M F× M) => M F∘ -⊗- F∘ (Id F× M)) (right-strength ◂ (Id F× M))
    right-φ = (mult ◂ -⊗-) ∘nt nat-assoc-to (M ▸ right-strength) ∘nt σ'
      where
        unquoteDecl σ' = cohere-into σ' (-⊗- F∘ (M F× M) => M F∘ -⊗- F∘ (M F× Id)) (left-strength ◂ (M F× Id))

    is-commutative-strength : Type (o ⊔ ℓ)
    is-commutative-strength = right-φ ≡ left-φ
```

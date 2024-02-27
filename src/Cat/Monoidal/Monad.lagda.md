<!--
```agda
open import Cat.Diagram.Monad
open import Cat.Monoidal.Base
open import Cat.Prelude

import Cat.Monoidal.Functor
import Cat.Reasoning
```
-->

```agda
module Cat.Monoidal.Monad {o ℓ}
  {C : Precategory o ℓ} (C-monoidal : Monoidal-category C)
  where
```

# Monoidal monads {defines="monoidal-monad"}

<!--
```agda
open Cat.Reasoning C
open Cat.Monoidal.Functor C-monoidal C-monoidal
open Monoidal-category C-monoidal
```
-->

A **monoidal monad** on a [[monoidal category]] $\cC$ is a [[monad]] on
$\cC$ whose underlying endofunctor is also equipped with the structure
of a [[lax monoidal functor]], in a way that the two structures agree.

```agda
module _ (monad : Monad C) where
  open Monad monad

  -- TODO better name
  record Monoidal-monad-on : Type (o ⊔ ℓ) where
    field
      monad-monoidal : Lax-monoidal-functor-on M

    open Lax-monoidal-functor-on monad-monoidal public

    field
      unit-ε : ε ≡ η Unit

    mult-ε : ε ≡ μ Unit ∘ M₁ ε ∘ ε
    mult-ε = insertl (ap (λ x → _ ∘ M₁ x) unit-ε ∙ left-ident)

    field
      unit-φ : ∀ {A B} → φ {A} {B} ∘ (η A ⊗₁ η B) ≡ η (A ⊗ B)
      mult-φ : ∀ {A B} → φ {A} {B} ∘ (μ A ⊗₁ μ B) ≡ μ (A ⊗ B) ∘ M₁ φ ∘ φ

Monoidal-monad : Type (o ⊔ ℓ)
Monoidal-monad = Σ (Monad C) Monoidal-monad-on
```

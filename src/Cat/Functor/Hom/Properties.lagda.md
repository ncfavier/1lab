---
description: |
  We prove various properties of hom functors and the yoneda embedding.
---
<!--
```agda
open import Cat.Functor.Properties
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Functor.Morphism
import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Hom.Properties where
```

# Properties of hom functors

This module contains a collection of useful facts about [[Hom
functors]], and the [[Yoneda embedding]].

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
  private
    module Sets = Cat.Reasoning (Sets ℓ)
    module PSh[C] = Cat.Reasoning Cat[ C ^op , Sets ℓ ]
    module CoPSh[C] = Cat.Reasoning Cat[ C , Sets ℓ ]
    module よ = Cat.Functor.Morphism (よ C)
    module よcov = Cat.Functor.Morphism (よcov C)

  private
    variable
      x y z : Ob
      f g h : Hom x y

  open _=>_
```
-->

## Monos and epis

The Yoneda embedding preserves [[monomorphisms]]. Let $f : \cC(A,B)$ be
a mono, and let $\alpha, \beta : P \to \yo(A)$ be a pair of natural
transformations such that $\yo(f) \circ \alpha = \yo(f) \circ \beta$.
Equality of [[natural transformations]] is defined componentwise, so for
every $X : \cC$ and $p_x : P(x)$, we have $f \circ \alpha_x(p_x) = f
\circ \beta_x(p_x)$. Since $f$ is a mono, we can immediately deduce that
$\alpha = \beta$.

```agda
  よ-preserves-mono : is-monic f → PSh[C].is-monic (よ₁ C f)
  よ-preserves-mono f-mono α β p = ext λ x px →
    f-mono (α .η x px) (β .η x px) (unext p x px)
```

Furthermore, the Yoneda embedding is [[fully faithful]], so it reflects
both monos and [[epis|epimorphism]].

```agda
  よ-reflects-mono : PSh[C].is-monic (よ₁ C f) → is-monic f
  よ-reflects-mono = よ.faithful→reflects-mono (よ-is-faithful C)

  よ-reflects-epi : PSh[C].is-epic (よ₁ C f) → is-epic f
  よ-reflects-epi = よ.faithful→reflects-epi (よ-is-faithful C)
```

Likewise, the covariant Yoneda embedding takes epis to monos, reflects
monos to epis, and vice versa.

```agda
  よcov-reverses-epi : is-epic f → CoPSh[C].is-monic (よcov₁ C f)
  よcov-reverses-epi {f = f} f-epic α β p = ext λ x px →
    f-epic (α .η x px) (β .η x px) (unext p x px)

  よcov-reflects-mono-to-epi : CoPSh[C].is-monic (よcov₁ C f) → is-epic f
  よcov-reflects-mono-to-epi = よcov.faithful→reflects-mono (よcov-is-faithful C)

  よcov-reflects-epi-to-mono : CoPSh[C].is-epic (よcov₁ C f) → is-monic f
  よcov-reflects-epi-to-mono = よcov.faithful→reflects-epi (よcov-is-faithful C)
```

```agda
  open import Cat.Diagram.Limit.Base
  open import Cat.Instances.Functor.Limits
  open import Cat.Functor.Kan.Unique
  open import Cat.Functor.Naturality
  open import Cat.Functor.Compose
  open import Cat.Functor.Hom.Representable
  open import Cat.Instances.Shape.Terminal

  open Functor

  よ-preserves-limits : ∀ {o' κ'} → is-continuous o' κ' (よ C)
  よ-preserves-limits {Diagram = D} {G} {eps} lim =
    is-limit→is-ran $ is-pointwise-limit→is-limit _ _ _ λ c →
      natural-isos→is-ran idni
        (iso→isoⁿ (λ _ → Sets.id-iso) λ _ → refl)
        (!const-isoⁿ Sets.id-iso)
        (ext λ j h → refl⟩∘⟨ G.eliml refl)
        (Hom-from-preserves-limits c lim)
    where module G = Cat.Functor.Reasoning G
```


```agda
open import Cat.Functor.Naturality
open import Cat.Instances.Functor.Limits
open import Cat.Diagram.Limit.Base
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Kan.Reflection
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Compose
open import Cat.Functor.Coherence

private variable
  o ℓ : Level
  D E F : Precategory o ℓ
module _ (p : Functor D E) where

  precompose-preserves-limits
    : ∀ {o' κ'} → is-continuous o' κ' (precompose p {D = F})
  precompose-preserves-limits {F = F} {Diagram = Dia} {G} {eps} lim =
    -- natural-isos→is-ran idni idni
    --   (!const-isoⁿ (Cat.Reasoning.id-iso _))
    --   (ext λ j d → F.eliml refl ∙ F.elimr (F.eliml refl))
      -- (is-pointwise-limit→is-limit (precompose p F∘ Dia) (G F∘ p)
      --   -- (NT ((precompose p ▸ eps) .η) λ x y f → ap ((eps .η y ◂ p) ∘nt_) (sym {!   !}) ∙ (precompose p ▸ eps) .is-natural x y f)
      --   _
      --   λ e → {! lim   !})
    is-limit→is-ran $ is-pointwise-limit→is-limit _ _ _ λ d →
      trivial-is-ran!
        (is-limit→is-pointwise-limit _ _ _
          (to-is-limit (unmake-limit lim))
          (p .Functor.F₀ d))
    where
      module F = Cat.Reasoning F
      -- module [D,F] = Cat.Reasoning Cat[ D , F ]
```

Hom(-, =) preserves limits in =:
  Hom(-, lim D_i)
= (λ x → Hom(x, lim D_i))
= (λ x → lim Hom(x, D_i)) -- Hom(x, -) preserves limits
= lim Hom(-, D_i) -- pointwise

- ∘ p preserves limits:
  (lim D_i) ∘ p
= λ x → (lim D_i) (p x)
= λ x → lim (D_i (p x))

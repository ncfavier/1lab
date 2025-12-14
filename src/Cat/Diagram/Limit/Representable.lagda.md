<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Functor
open import Cat.Functor.Constant
open import Cat.Functor.Kan.Base
open import Cat.Functor.Compose
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Limit.Representable where
```

## Representability of limits

Since [[limits]] are defined by universal property, we can also phrase
the definition in terms of an equivalence between $\hom$-functors.

<!--
```agda
Lift-Sets
  : ∀ {ℓ} ℓ' → Functor (Sets ℓ) (Sets (ℓ ⊔ ℓ'))
Lift-Sets ℓ' .Functor.F₀ X = el! (Lift ℓ' ⌞ X ⌟)
Lift-Sets ℓ' .Functor.F₁ f (lift x) = lift (f x)
Lift-Sets ℓ' .Functor.F-id = ext λ _ → refl
Lift-Sets ℓ' .Functor.F-∘ f g = ext λ _ → refl

module _
  {oj ℓj o ℓ}
  {J : Precategory oj ℓj} {C : Precategory o ℓ} {Dia : Functor J C}
  where
  private
    module C = Cat.Reasoning C
    open Functor
    open _=>_
    open is-ran
```
-->

Let $\mathrm{Dia} : \cJ \to \cC$ be some diagram in $\cC$. If
$\mathrm{Dia}$ has a limit $l$, then that means that maps **into**
$l$ are in bijection with a product of maps $\pi_i$, subject to some
conditions.

```agda
  Lim[C[=,F-]] : Functor (C ^op) (Sets (oj ⊔ ℓj ⊔ ℓ))
  Lim[C[=,F-]] .F₀ c = el (Const c => Dia) Nat-is-set
  Lim[C[=,F-]] .F₁ f α = α ∘nt constⁿ f
  Lim[C[=,F-]] .F-id = ext λ _ _ → C.idr _
  Lim[C[=,F-]] .F-∘ _ _ = ext λ _ _ → C.assoc _ _ _

  Hom-into-inj
    : ∀ {c : C.Ob} (eps : Const c => Dia)
    → Lift-Sets (oj ⊔ ℓj) F∘ Hom-into C c => Lim[C[=,F-]]
  Hom-into-inj eps .η x (lift f) = eps ∘nt constⁿ f
  Hom-into-inj eps .is-natural x y f = ext λ g _ →
    C.assoc _ _ _

  represents→is-limit
    : ∀ {c : C.Ob} {eps : Const c => Dia}
    → is-invertibleⁿ (Hom-into-inj eps)
    → is-limit Dia c eps
  represents→is-limit {c} {eps} nat-inv = lim where
    module nat-inv = is-invertibleⁿ nat-inv

    lim : is-limit Dia c eps
    lim .σ {M} α =
      !constⁿ (nat-inv.inv .η _ (to-coneⁿ α) .lower)
    lim .σ-comm {M} {α} = ext λ j → unext nat-inv.invl _ _ j
    lim .σ-uniq {M} {α} {σ'} q = ext λ j →
      nat-inv.inv .η _ (to-coneⁿ ⌜ α ⌝) .lower                    ≡⟨ ap! q ⟩
      nat-inv.inv .η _ ⌜ to-coneⁿ (eps ∘nt (σ' ◂ !F)) ⌝ .lower    ≡⟨ ap! (ext λ _ → refl) ⟩
      nat-inv.inv .η _ (eps ∘nt (!constⁿ (σ' .η tt) ◂ !F)) .lower ≡⟨ unext nat-inv.invr _ _ ⟩
      σ' .η tt                                                    ∎
```

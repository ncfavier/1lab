<!--
```agda
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Initial
open import Cat.Prelude

import Cat.Reasoning

open Coproduct
```
-->

```agda
module Cat.Diagram.Cosubterminal where
```

# Cosubterminal objects {defines="cosubterminal-object cosubterminal"}

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
```
-->

An object $P$ of a category $\cC$ is **cosubterminal** if there is at most
one map from $P$ into every other object. This is the dual notion to a
[[subterminal object]]: see there for more motivation.

::: terminology
There does not seem to be an established name for these, but see
[MSE.1092122](https://math.stackexchange.com/questions/1092122) for some
discussion.
:::

```agda
  is-cosubterminal : Ob → Type _
  is-cosubterminal A = ∀ X → is-prop (Hom A X)

  initial→cosubterminal : ∀ {T} → is-initial C T → is-cosubterminal T
  initial→cosubterminal init X = is-contr→is-prop (init X)
```

An object $A$ is cosubterminal if and only if the unique map from the
[[initial object]] to $A$ is an [[epimorphism]].

```agda
  module _ (init : Initial C) where
    open Initial init

    is-quotient-initial : Ob → Type _
    is-quotient-initial A = is-epic (¡ {x = A})

    cosubterminal≃quotient-initial
      : ∀ A → is-cosubterminal A ≃ is-quotient-initial A
    cosubterminal≃quotient-initial A = prop-ext!
      (λ h f g _ → h _ f g)
      (λ h X x y → h x y (¡-unique₂ _ _))
```

Cosubterminal objects also have various equivalent characterisations in
terms of [[coproducts]], dually to subterminal objects. We only repeat
the first one: an object $A$ is cosubterminal if and only if the
following diagram is a [[coproduct]] diagram:

~~~{.quiver}
\[\begin{tikzcd}
  A & A & A
  \arrow["{\mathrm{id}}"', from=1-1, to=1-2]
  \arrow["{\mathrm{id}}", from=1-3, to=1-2]
\end{tikzcd}\]
~~~

```agda
  is-cosubterminal₁ : Ob → Type _
  is-cosubterminal₁ A = is-coproduct C (id {x = A}) (id {x = A})

  is-cosubterminal₂ : Ob → Type _
  is-cosubterminal₂ A = ∃[ c ∈ Coproduct C A A ] c .ι₁ ≡ c .ι₂

  is-cosubterminal₃ : Ob → Type _
  is-cosubterminal₃ A = ∃[ c ∈ Coproduct C A A ] is-invertible (c .[_,_] id id)
```

<details>
<summary>Proving these equivalences is a succession of elementary
exercises, so we leave them hidden in this `<details>` tag.</summary>

```agda
  module _ (A : Ob) where
    is-cosubterminal₀→₁ : is-cosubterminal A → is-cosubterminal₁ A
    is-cosubterminal₀→₁ h .is-coproduct.[_,_] f g = f
    is-cosubterminal₀→₁ h .is-coproduct.[]∘ι₁ = idr _
    is-cosubterminal₀→₁ h .is-coproduct.[]∘ι₂ = idr _ ∙ h _ _ _
    is-cosubterminal₀→₁ h .is-coproduct.unique a b = sym (idr _) ∙ a

    is-cosubterminal₁→₀ : is-cosubterminal₁ A → is-cosubterminal A
    is-cosubterminal₁→₀ h X f g = sym (h .is-coproduct.[]∘ι₁) ∙ h .is-coproduct.[]∘ι₂

    is-cosubterminal₁→₂ : is-cosubterminal₁ A → is-cosubterminal₂ A
    is-cosubterminal₁→₂ h = inc (c , refl)
      where
        c : Coproduct C A A
        c .coapex = A
        c .ι₁ = id
        c .ι₂ = id
        c .has-is-coproduct = h

    is-cosubterminal₂→₀ : is-cosubterminal₂ A → is-cosubterminal A
    is-cosubterminal₂→₀ = rec! λ p h X f g →
      sym (p .[]∘ι₁) ∙∙ cdr h ∙∙ p .[]∘ι₂

    is-cosubterminal₁→₃ : is-cosubterminal₁ A → is-cosubterminal₃ A
    is-cosubterminal₁→₃ h = inc (c , subst is-invertible eq id-invertible)
      where
        c : Coproduct C A A
        c .coapex = A
        c .ι₁ = id
        c .ι₂ = id
        c .has-is-coproduct = h

        eq : id ≡ h .is-coproduct.[_,_] id id
        eq = h .is-coproduct.unique (idl _) (idl _)

    is-cosubterminal₃→₁ : is-cosubterminal₃ A → is-cosubterminal₁ A
    is-cosubterminal₃→₁ = rec! λ p h →
      is-coproduct-iso-coapex h (p .[]∘ι₁) (p .[]∘ι₂) (p .has-is-coproduct)
```
</details>

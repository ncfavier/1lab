<!--
```agda
open import Cat.Functor.Equivalence
open import Cat.Instances.Product
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning

open Precategory
open Functor
open _=>_
```
-->

```agda
module Cat.Functor.Closed where
```

<!--
```agda
private variable
  o h o₁ h₁ o₂ h₂ : Level
  B C D E : Precategory o h
  F G : Functor C D
```
-->

When taken as a [(bi)category][cat], the collection of (pre)categories
is, in a suitably weak sense, [[Cartesian closed]]: there is an
[equivalence] between the [functor categories] $[\cC \times \cD, \cE]$
and $[\cC, [\cD, \cE]]$.

[cat]: Cat.Bi.Base.html#the-bicategory-of-categories
[equivalence]: Cat.Functor.Equivalence.html
[functor categories]: Cat.Functor.Base.html

The two conversion functions `Curry`{.Agda} and `Uncurry`{.Agda} act on
functors essentially in the same way as currying and uncurrying behave
on funct*ions*: the difference is that we must properly stage the action
on morphisms. Currying a functor $F : \cC \times \cD \to \cE$ fixes a
morphism $f : x \to y \in \cC$, and we must show that $g \mapsto F(f,g)$
is natural in $g$. It follows from a bit of calculation using the
functoriality of $F$.

<!--
```agda
module _ {C : Precategory o h} {D : Precategory o₁ h₁} {E : Precategory o₂ h₂} where
  import Cat.Reasoning C as C
  import Cat.Reasoning D as D
  import Cat.Reasoning E as E
```
-->

```agda
  Curry : Functor (C ×ᶜ D) E → Functor C Cat[ D , E ]
  Curry F = curried where
    open import Cat.Functor.Bifunctor {C = C} {D = D} {E = E} F

    curried : Functor C Cat[ D , E ]
    curried .F₀ = Right
    curried .F₁ x→y = NT (λ f → first x→y) λ x y f →
        sym (F .F-∘ _ _)
      ∙∙ ap (F .F₁) (Σ-pathp (C .idr _ ∙ sym (C .idl _)) (D .idl _ ∙ sym (D .idr _)))
      ∙∙ F .F-∘ _ _
    curried .F-id = ext λ x → F .F-id
    curried .F-∘ f g = ext λ x →
      ap (λ x → F .F₁ (_ , x)) (sym (D .idl _)) ∙ F .F-∘ _ _

  Uncurry : Functor C Cat[ D , E ] → Functor (C ×ᶜ D) E
  Uncurry F = uncurried where
    module F = Functor F

    uncurried : Functor (C ×ᶜ D) E
    uncurried .F₀ (c , d) = F.₀ c .F₀ d
    uncurried .F₁ (f , g) = F.₁ f .η _ E.∘ F.₀ _ .F₁ g
```

The other direction must do slightly more calculation: Given a functor
into functor-categories, and a pair of arguments, we must apply it
twice: but at the level of morphisms, this involves composition in the
codomain category, which throws a fair bit of complication into the
functoriality constraints.

```agda
    uncurried .F-id {x = x , y} = path where abstract
      path : E ._∘_ (F.₁ (C .id) .η y) (F.₀ x .F₁ (D .id)) ≡ E .id
      path =
        F.₁ C.id .η y E.∘ F.₀ x .F₁ D.id ≡⟨ E.elimr (F.₀ x .F-id) ⟩
        F.₁ C.id .η y                    ≡⟨ (λ i → F.F-id i .η y) ⟩
        E.id                             ∎

    uncurried .F-∘ (f , g) (f' , g') = path where abstract
      path : uncurried .F₁ (f C.∘ f' , g D.∘ g')
           ≡ uncurried .F₁ (f , g) E.∘ uncurried .F₁ (f' , g')
      path =
        F.₁ (f C.∘ f') .η _ E.∘ F.₀ _ .F₁ (g D.∘ g')                      ≡˘⟨ E.pulll (λ i → F.F-∘ f f' (~ i) .η _) ⟩
        F.₁ f .η _ E.∘ F.₁ f' .η _ E.∘ ⌜ F.₀ _ .F₁ (g D.∘ g') ⌝           ≡⟨ ap! (F.₀ _ .F-∘ _ _) ⟩
        F.₁ f .η _ E.∘ F.₁ f' .η _ E.∘ F.₀ _ .F₁ g E.∘ F.₀ _ .F₁ g'       ≡⟨ cat! E ⟩
        F.₁ f .η _ E.∘ ⌜ F.₁ f' .η _ E.∘ F.₀ _ .F₁ g ⌝ E.∘ F.₀ _ .F₁ g'   ≡⟨ ap! (F.₁ f' .is-natural _ _ _) ⟩
        F.₁ f .η _ E.∘ (F.₀ _ .F₁ g E.∘ F.₁ f' .η _) E.∘ F.₀ _ .F₁ g'     ≡⟨ cat! E ⟩
        ((F.₁ f .η _ E.∘ F.₀ _ .F₁ g) E.∘ (F.₁ f' .η _ E.∘ F.₀ _ .F₁ g')) ∎
```

`Curry`{.Agda} also has an action on natural transformations, so we
can promote it to a functor between functor categories.

```agda
  curry-nt
    : {F G : Functor (C ×ᶜ D) E}
    → F => G
    → Curry F => Curry G
  curry-nt α .η c .η d = α .η (c , d)
  curry-nt α .η c .is-natural x y f = α .is-natural _ _ (C.id , f)
  curry-nt α .is-natural x y f = ext λ _ → α .is-natural _ _ (f , D.id)

  CurryF : Functor Cat[ C ×ᶜ D , E ] Cat[ C , Cat[ D , E ] ]
  CurryF .F₀ = Curry
  CurryF .F₁ = curry-nt
  CurryF .F-id = ext λ _ _ → refl
  CurryF .F-∘ _ _ = ext λ _ _ → refl
```

We show that `CurryF`{.Agda} is an [[isomorphism of precategories]],
hence an [[equivalence of categories]].

```agda
  Curry≃ : Functor (C ×ᶜ D) E ≃ Functor C Cat[ D , E ]
  Curry≃ = Iso→Equiv $ Curry , iso Uncurry
    (λ F → Functor-path
      (λ c → Functor-path (λ _ → refl) (λ f → E.eliml (F .F-id ηₚ _)))
      (λ f → Nat-pathp _ _ λ d → E.elimr (F .F₀ _ .F-id)))
    (λ F → Functor-path
      (λ (c , d) → refl)
      (λ f → sym (F .F-∘ _ _) ∙ ap (F .F₁) (C.idr _ ,ₚ D.idl _)))

  curry-nt-is-equiv : ∀ {F G} → is-equiv (curry-nt {F} {G})
  curry-nt-is-equiv {F = F} {G = G} = is-iso→is-equiv λ where
    .is-iso.from α .η (c , d) → α .η c .η d
    .is-iso.from α .is-natural (x , x') (y , y') (f , g) →
      α .η y .η y' E.∘ F.₁ (f , g) ≡˘⟨ (E.refl⟩∘⟨ F.collapse (C.idr _ ,ₚ D.idl _)) ⟩
      α .η y .η y' E.∘ F.₁ (f , D.id) E.∘ F.₁ (C.id , g) ≡⟨ E.extendl (α .is-natural x y f ηₚ y') ⟩
      G.₁ (f , D.id) E.∘ α .η x .η y' E.∘ F.₁ (C.id , g) ≡⟨ (E.refl⟩∘⟨ α .η x .is-natural x' y' g) ⟩
      G.₁ (f , D.id) E.∘ G.₁ (C.id , g) E.∘ α .η x .η x' ≡⟨ E.pulll (G.collapse (C.idr _ ,ₚ D.idl _)) ⟩
      G.₁ (f , g) E.∘ α .η x .η x' ∎
    .is-iso.rinv α → ext λ _ _ → refl
    .is-iso.linv α → ext λ _ → refl
      where
        module F = Cat.Functor.Reasoning F
        module G = Cat.Functor.Reasoning G

  Curry-is-iso : is-precat-iso CurryF
  Curry-is-iso .is-precat-iso.has-is-ff = curry-nt-is-equiv
  Curry-is-iso .is-precat-iso.has-is-iso = Curry≃ .snd

  Curry-is-equiv : is-equivalence CurryF
  Curry-is-equiv = is-precat-iso→is-equivalence Curry-is-iso
```

<!--
This follows from the equivalence above, but results in unnecessary
transports of identity morphisms.

```agda
  module _ {F G : Functor C Cat[ D , E ]} where
    private
      module F = Cat.Functor.Reasoning F
      module G = Cat.Functor.Reasoning G

    uncurry-nt : F => G → Uncurry F => Uncurry G
    uncurry-nt α .η (c , d) = α .η c .η d
    uncurry-nt α .is-natural (x , x') (y , y') (f , g) =
      α .η y .η y' E.∘ F.₁ f .η y' E.∘ F.₀ x .F₁ g   ≡⟨ E.extendl (α .is-natural x y f ηₚ y') ⟩
      G.₁ f .η y' E.∘ α .η x .η y' E.∘ F.₀ x .F₁ g   ≡⟨ E.pushr (α .η x .is-natural x' y' g) ⟩
      (G.₁ f .η y' E.∘ G.₀ x .F₁ g) E.∘ α .η x .η x' ∎

    uncurry-nt⁻¹ : Uncurry F => Uncurry G → F => G
    uncurry-nt⁻¹ α .η c .η d = α .η (c , d)
    uncurry-nt⁻¹ α .η c .is-natural x y f =
      (E.refl⟩∘⟨ E.introl (F.F-id ηₚ y)) ∙∙ α .is-natural _ _ (C.id , f) ∙∙ (E.eliml (G .F-id ηₚ y) E.⟩∘⟨refl)
    uncurry-nt⁻¹ α .is-natural x y f = ext λ d →
      (E.refl⟩∘⟨ E.intror (F.₀ x .F-id)) ∙∙ α .is-natural _ _ (f , D.id) ∙∙ (E.elimr (G.₀ x .F-id) E.⟩∘⟨refl)

    uncurry-nt≃ : (F => G) ≃ (Uncurry F => Uncurry G)
    uncurry-nt≃ = Iso→Equiv (uncurry-nt , iso uncurry-nt⁻¹ (λ α → ext λ _ → refl) λ α → ext λ _ _ → refl)
```
-->

## Evaluation functors

The [[counit]] of the 2-categorical adjunction between product
categories and functor categories is a bifunctor $[C, D] \times C \to
D$. Its action on an object $c : C$ is a functor $[C, D] \to D$ called
**evaluation at $c$**.

```agda
Eval : Functor (Cat[ C , D ] ×ᶜ C) D
Eval = Uncurry Id

Eval-at : ⌞ C ⌟ → Functor Cat[ C , D ] D
Eval-at = Eval.Left where
  import Cat.Functor.Bifunctor Eval as Eval
```

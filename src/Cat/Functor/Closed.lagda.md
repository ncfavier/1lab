<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Instances.Product
open import Cat.Functor.Base
open import Cat.Prelude

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
and $[\cC, [\cD, \cE]]$. We do not define the full equivalence here,
leaving the natural isomorphisms aside and focusing on the inverse
functors themselves: `Curry`{.Agda} and `Uncurry`{.Agda}.

[cat]: Cat.Bi.Base.html#the-bicategory-of-categories
[equivalence]: Cat.Functor.Equivalence.html
[functor categories]: Cat.Functor.Base.html

The two conversion functions act on objects essentially in the same way
as currying and uncurrying behave on funct*ions*: the difference is that
we must properly stage the action on morphisms. Currying a functor $F :
\cC \times \cD \to \cE$ fixes a morphism $f : x \to y \in \cC$, and we
must show that $g \mapsto F(f,g)$ is natural in $g$. It follows from a
bit of calculation using the functoriality of $F$.

```agda
module _ {C : Precategory o h} {D : Precategory o₁ h₁} {E : Precategory o₂ h₂} where
  import Cat.Reasoning C as C
  import Cat.Reasoning D as D
  import Cat.Reasoning E as E

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

  Curry≃ : Functor (C ×ᶜ D) E ≃ Functor C Cat[ D , E ]
  Curry≃ = Iso→Equiv $ Curry , iso Uncurry
    (λ F → Functor-path
      (λ c → Functor-path (λ _ → refl) (λ f → E.eliml (F .F-id ηₚ _)))
      (λ f → Nat-pathp _ _ λ d → E.elimr (F .F₀ _ .F-id)))
    (λ F → Functor-path
      (λ (c , d) → refl)
      (λ f → sym (F .F-∘ _ _) ∙ ap (F .F₁) (C.idr _ ,ₚ D.idl _)))

  curry-nt
    : {F G : Functor (C ×ᶜ D) E}
    → F => G
    → Curry F => Curry G
  curry-nt α .η c .η d = α .η (c , d)
  curry-nt α .η c .is-natural x y f = α .is-natural _ _ (C.id , f)
  curry-nt α .is-natural x y f = ext λ _ → α .is-natural _ _ (f , D.id)

  curry-uncurry
    : {F : Functor C Cat[ D , E ]}
    → Curry (Uncurry F) ≅ⁿ F
  curry-uncurry {F} = iso→isoⁿ
    (λ c → iso→isoⁿ (λ d → E.id-iso) λ {x} {y} f →
      E.id-comm ∙ (E.refl⟩∘⟨ E.introl (F.F-id ηₚ y)))
    λ {x} {y} f → ext λ d → E.id-comm ∙ (E.refl⟩∘⟨ E.intror (F.₀ x .F-id))
    where
      import Cat.Functor.Reasoning F as F

  ununcurry-nt
    : {F G : Functor C Cat[ D , E ]}
    → Uncurry F => Uncurry G
    → F => G
  ununcurry-nt α .η c .η d = α .η (c , d)
  ununcurry-nt {F = F} {G} α .η c .is-natural x y f = (E.refl⟩∘⟨ E.introl (F.F-id ηₚ y)) ∙∙ α .is-natural _ _ (C.id , f) ∙∙ (E.eliml (G .F-id ηₚ y) E.⟩∘⟨refl)
    where
      import Cat.Functor.Reasoning F as F
      import Cat.Functor.Reasoning G as G
  ununcurry-nt {F = F} {G} α .is-natural x y f = ext λ d → (E.refl⟩∘⟨ E.intror (F.₀ x .F-id)) ∙∙ α .is-natural _ _ (f , D.id) ∙∙ (E.elimr (G.₀ x .F-id) E.⟩∘⟨refl)
    where
      import Cat.Functor.Reasoning F as F
      import Cat.Functor.Reasoning G as G

  uncurry-nt
    : {F G : Functor C Cat[ D , E ]}
    → F => G
    → Uncurry F => Uncurry G
  uncurry-nt α .η (c , d) = α .η c .η d
  uncurry-nt {F = F} {G} α .is-natural (x , x') (y , y') (f , g) =
    α .η y .η y' E.∘ F.₁ f .η y' E.∘ F.₀ x .F₁ g   ≡⟨ E.extendl (α .is-natural x y f ηₚ y') ⟩
    G.₁ f .η y' E.∘ α .η x .η y' E.∘ F.₀ x .F₁ g   ≡⟨ E.pushr (α .η x .is-natural x' y' g) ⟩
    (G.₁ f .η y' E.∘ G.₀ x .F₁ g) E.∘ α .η x .η x' ∎
    where
      import Cat.Functor.Reasoning F as F
      import Cat.Functor.Reasoning G as G

  uncurry-nt≃
    : {F G : Functor C Cat[ D , E ]}
    → (F => G) ≃ (Uncurry F => Uncurry G)
  uncurry-nt≃ = Iso→Equiv (uncurry-nt , iso ununcurry-nt (λ α → ext λ _ → refl) λ α → ext λ _ _ → refl)
```

```agda
Eval : Ob C → Functor Cat[ C , D ] D
Eval c .F₀ F = F .F₀ c
Eval c .F₁ n = n .η c
Eval c .F-id {F} = refl
Eval c .F-∘ f g = refl
```

```agda
open _=>_
evF : Functor (Cat[ C , D ] ×ᶜ C) D
evF {C = C} {D = D} = eval'd where
  import Cat.Reasoning C as C
  import Cat.Reasoning D as D
  eval'd : Functor (Cat[ C , D ] ×ᶜ C) D
  eval'd .F₀ (F , x) = F .F₀ x
  eval'd .F₁ {F , x} {G , y} (nt , f) = G .F₁ f D.∘ nt .η x
  eval'd .F-id {F , _} = D.eliml $ F .F-id
  eval'd .F-∘ {F , x} {G , y} {H , z} (nt₁ , f) (nt₂ , g) =
    H .F₁ (f C.∘ g) D.∘ nt₁ .η x D.∘ nt₂ .η x
      ≡⟨ H .F-∘ _ _ D.⟩∘⟨refl ⟩
    (H .F₁ f D.∘ H .F₁ g) D.∘ nt₁ .η x D.∘ nt₂ .η x
      ≡˘⟨ D.pull-inner (nt₁ .is-natural _ _ _) ∙ D.push-inner refl ⟩
    (H .F₁ f D.∘ nt₁ .η y) D.∘ G .F₁ g D.∘ nt₂ .η x
      ∎

eval-at : ⌞ C ⌟ → Functor Cat[ C , D ] D
eval-at {C = C} {D = D} = evF.Left where
  import Cat.Functor.Bifunctor (evF {C = C} {D = D}) as evF
```

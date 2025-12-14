<!--
```agda
open import Cat.Functor.Hom.Representable
open import Cat.Functor.Kan.Representable
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Naturality
open import Cat.Instances.Product
open import Cat.Functor.Constant
open import Cat.Functor.Kan.Base
open import Cat.Functor.Compose
open import Cat.Functor.Closed
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Functor.Kan where
```

## Kan extensions in functor categories

This module characterises Kan extensions in functor categories.

<!--
```agda
module _
  {oc ℓc oc' ℓc' od ℓd oe ℓe}
  {C : Precategory oc ℓc} {C' : Precategory oc' ℓc'} {D : Precategory od ℓd} {E : Precategory oe ℓe}
  {p : Functor C C'} {F : Functor C Cat[ D , E ]} {G : Functor C' Cat[ D , E ]}
  where
  private
    module E = Cat.Reasoning E
    module [C×D,E] = Cat.Reasoning Cat[ C ×ᶜ D , E ]
```
-->

```agda
  coh : ∀ {H : Functor C' Cat[ D , E ]} → Uncurry (H F∘ p) ≅ⁿ Uncurry H F∘ (p F× Id)
  coh = iso→isoⁿ (λ _ → E.id-iso) (λ f → E.id-comm)

  square→equiv≃equiv
    : ∀ {a b c d} {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    → {f : A → B} {g : C → D}
    → (e : A ≃ C) (h : B ≃ D)
    → h .fst ⊙ f ≡ g ⊙ e .fst
    → is-equiv f ≃ is-equiv g
  square→equiv≃equiv e h p = {!   !}

  uncurry-eta≃ : ∀ {H} → (F => H F∘ p) ≃ (Uncurry F => Uncurry H F∘ (p F× Id))
  uncurry-eta≃ = uncurry-nt≃ ∙e [C×D,E].cod-iso→hom-equiv coh

  is-lan≃uncurry-lan
    : {eta : F => G F∘ p}
    → is-lan p F G eta ≃ is-lan (p F× Id) (Uncurry F) (Uncurry G) (uncurry-eta≃ · eta)
  is-lan≃uncurry-lan {eta} =
    is-lan p F G eta                                           ≃⟨ is-lan≃represents ⟩
    (∀ H → is-equiv (Hom-from-precompose eta H))               ≃⟨ Π-ap (Curry≃ e⁻¹) (λ H → square→equiv≃equiv uncurry-nt≃ uncurry-eta≃ (ext λ α _ → E.extendl E.id-comm-sym)) ⟩
    (∀ H → is-equiv (Hom-from-precompose (uncurry-eta≃ · eta) H)) ≃˘⟨ is-lan≃represents ⟩
    is-lan (p F× Id) (Uncurry F) (Uncurry G) (uncurry-eta≃ · eta) ≃∎

module _
  {oc ℓc od ℓd oe ℓe}
  {C : Precategory oc ℓc} {D : Precategory od ℓd} {E : Precategory oe ℓe}
  {F : Functor C Cat[ D , E ]} {G : Functor D E}
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module E = Cat.Reasoning E
    module [C,D] = Cat.Reasoning Cat[ C , D ]
    module [C×D,E] = Cat.Reasoning Cat[ C ×ᶜ D , E ]
    open Functor
    open _=>_
    open is-lan
    open Corepresentation
    open Isoⁿ

  is-colimit≃uncurry-lan
    : {eta : F => Const G}
    → is-colimit F G eta ≃ is-lan Snd (Uncurry F) G {!    !}
  is-colimit≃uncurry-lan = is-lan≃uncurry-lan ∙e {!   !}
```

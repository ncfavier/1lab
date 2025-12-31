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
open import Cat.Instances.Sets
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Reasoning

open _=>_
```
-->

```agda
module Cat.Instances.Functor.Kan where
```

## Kan extensions in functor categories

<!--
```agda
module _
  {oc ℓc od ℓd oe ℓe}
  {C : Precategory oc ℓc} {C' : Precategory oc ℓc} {D : Precategory od ℓd} {E : Precategory oe ℓe}
  {p : Functor C C'} {F : Functor C Cat[ D , E ]} {G : Functor C' Cat[ D , E ]}
  where
  private
    module E = Cat.Reasoning E
    module [C×D,E] = Cat.Reasoning Cat[ C ×ᶜ D , E ]
```
-->

```agda
  uncurry-eta≃ : ∀ {H} → (F => H F∘ p) ≃ (Uncurry F => Uncurry H F∘ (p F× Id))
  uncurry-eta≃ = uncurry-nt≃ ∙e [C×D,E].cod-iso→hom-equiv
    (iso→isoⁿ (λ _ → E.id-iso) (λ _ → E.id-comm))

  is-lan≃uncurry-lan
    : {eta : F => G F∘ p}
    → is-lan p F G eta
    ≃ is-lan (p F× Id) (Uncurry F) (Uncurry G) (uncurry-eta≃ · eta)
  is-lan≃uncurry-lan {eta} =
    is-lan p F G eta                         ≃⟨ is-lan≃represents ⟩
    is-invertibleⁿ (Hom-from-precompose eta) ≃⟨ is-invertibleⁿ≃is-invertible ⟩
    (∀ H → Sets.is-invertible _)             ≃⟨ Π-ap (Curry≃ e⁻¹) (λ H → is-invertible≃is-equiv ∙e square→equiv≃equiv uncurry-nt≃ uncurry-eta≃ (ext λ α _ → E.extendl E.id-comm-sym) ∙e is-invertible≃is-equiv e⁻¹) ⟩
    (∀ H → Sets.is-invertible _)             ≃˘⟨ is-invertibleⁿ≃is-invertible ⟩
    is-invertibleⁿ (Hom-from-precompose _)   ≃˘⟨ is-lan≃represents ⟩
    is-lan _ _ _ _                           ≃∎
    where
      import Cat.Reasoning (Sets _) as Sets
```

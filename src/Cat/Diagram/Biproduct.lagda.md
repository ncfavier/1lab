<!--
```agda
open import Cat.Monoidal.Instances.Cartesian
open import Cat.Monoidal.Diagonals
open import Cat.Functor.Naturality
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Product
open import Cat.Monoidal.Base
open import Cat.Diagram.Zero
open import Cat.Prelude

import Cat.Reasoning

open _=>_
```
-->

```agda
module Cat.Diagram.Biproduct where
```

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
```
-->

# Biproducts

```agda
  record is-biproduct {A B P} (π₁ : Hom P A) (π₂ : Hom P B) (ι₁ : Hom A P) (ι₂ : Hom B P) : Type (o ⊔ ℓ) where
    field
      has-is-product   : is-product C π₁ π₂
      has-is-coproduct : is-coproduct C ι₁ ι₂
      πι₁ : π₁ ∘ ι₁ ≡ id
      πι₂ : π₂ ∘ ι₂ ≡ id
      ιπ-comm : ι₁ ∘ π₁ ∘ ι₂ ∘ π₂ ≡ ι₂ ∘ π₂ ∘ ι₁ ∘ π₁

  record Biproduct (A B : Ob) : Type (o ⊔ ℓ) where
    field
      biapex : Ob
      π₁ : Hom biapex A
      π₂ : Hom biapex B
      ι₁ : Hom A biapex
      ι₂ : Hom B biapex
      has-is-biproduct : is-biproduct π₁ π₂ ι₁ ι₂

    open is-biproduct has-is-biproduct public

    product : Product C A B
    product = record { apex = biapex ; π₁ = π₁ ; π₂ = π₂ ; has-is-product = has-is-product }

    coproduct : Coproduct C A B
    coproduct = record { coapex = biapex ; in₀ = ι₁ ; in₁ = ι₂ ; has-is-coproduct = has-is-coproduct }

    open Product product public hiding (π₁; π₂; unique₂)
    open Coproduct coproduct public hiding (in₀; in₁; unique₂)

  record Semiadditive : Type (o ⊔ ℓ) where
    field
      has-zero : Zero C
      has-biproducts : ∀ {A B} → Biproduct A B

    open Zero has-zero
    module biproduct {A B} = Biproduct (has-biproducts {A} {B})

    open biproduct using (π₁; π₂; ι₁; ι₂)

    open Binary-products C (λ _ _ → biproduct.product) hiding (π₁; π₂)
    open Binary-coproducts C (λ _ _ → biproduct.coproduct)

    open Monoidal-category (Cartesian-monoidal (λ _ _ → biproduct.product) terminal) using (associator; module ⊗)
    open Diagonals (Cartesian-diagonal (λ _ _ → biproduct.product) terminal) hiding (δ)

    _+→_ : ∀ {x y} → Hom x y → Hom x y → Hom x y
    f +→ g = ∇ ∘ (f ⊗₁ g) ∘ δ

    π₁-ι₂ : ∀ {a b} → π₁ {a} {b} ∘ ι₂ ≡ zero→
    π₁-ι₂ = zero-unique λ f g →
      let h = ⟨ π₁ ∘ ι₂ ∘ g , f ⟩ in
      (π₁ ∘ ι₂) ∘ f ≡⟨ insertl biproduct.πι₁ ⟩
      π₁ ∘ ι₁ ∘ (π₁ ∘ ι₂) ∘ f ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc _ _ _ ∙ (refl⟩∘⟨ π₂∘⟨⟩) ⟩
      π₁ ∘ ι₁ ∘ π₁ ∘ ι₂ ∘ π₂ ∘ h ≡⟨ refl⟩∘⟨ pulll4 biproduct.ιπ-comm ⟩
      π₁ ∘ (ι₂ ∘ π₂ ∘ ι₁ ∘ π₁) ∘ h ≡⟨ refl⟩∘⟨ pullr (pullr (pullr π₁∘⟨⟩)) ⟩
      π₁ ∘ ι₂ ∘ π₂ ∘ ι₁ ∘ π₁ ∘ ι₂ ∘ g ≡˘⟨ refl⟩∘⟨ extendl4 biproduct.ιπ-comm ⟩
      π₁ ∘ ι₁ ∘ π₁ ∘ ι₂ ∘ π₂ ∘ ι₂ ∘ g ≡⟨ cancell biproduct.πι₁ ⟩
      π₁ ∘ ι₂ ∘ π₂ ∘ ι₂ ∘ g ≡⟨ pushr (refl⟩∘⟨ cancell biproduct.πι₂) ⟩
      (π₁ ∘ ι₂) ∘ g ∎

    π₂-ι₁ : ∀ {a b} → π₂ {a} {b} ∘ ι₁ ≡ zero→
    π₂-ι₁ = zero-unique λ f g →
      let h = ⟨ f , π₂ ∘ ι₁ ∘ g ⟩ in
      (π₂ ∘ ι₁) ∘ f ≡⟨ insertl biproduct.πι₂ ⟩
      π₂ ∘ ι₂ ∘ (π₂ ∘ ι₁) ∘ f ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc _ _ _ ∙ (refl⟩∘⟨ π₁∘⟨⟩) ⟩
      π₂ ∘ ι₂ ∘ π₂ ∘ ι₁ ∘ π₁ ∘ h ≡˘⟨ refl⟩∘⟨ pushl4 biproduct.ιπ-comm ⟩
      π₂ ∘ (ι₁ ∘ π₁ ∘ ι₂ ∘ π₂) ∘ h ≡⟨ refl⟩∘⟨ pullr (pullr (pullr π₂∘⟨⟩)) ⟩
      π₂ ∘ ι₁ ∘ π₁ ∘ ι₂ ∘ π₂ ∘ ι₁ ∘ g ≡⟨ refl⟩∘⟨ extendl4 biproduct.ιπ-comm ⟩
      π₂ ∘ ι₂ ∘ π₂ ∘ ι₁ ∘ π₁ ∘ ι₁ ∘ g ≡⟨ cancell biproduct.πι₂ ⟩
      π₂ ∘ ι₁ ∘ π₁ ∘ ι₁ ∘ g ≡⟨ pushr (refl⟩∘⟨ cancell biproduct.πι₁) ⟩
      (π₂ ∘ ι₁) ∘ g ∎

    unique-matrix
      : ∀ {a b c d} {f g : Hom (a ⊕₀ b) (c ⊕₀ d)}
      → (π₁ ∘ f ∘ ι₁ ≡ π₁ ∘ g ∘ ι₁)
      → (π₂ ∘ f ∘ ι₁ ≡ π₂ ∘ g ∘ ι₁)
      → (π₁ ∘ f ∘ ι₂ ≡ π₁ ∘ g ∘ ι₂)
      → (π₂ ∘ f ∘ ι₂ ≡ π₂ ∘ g ∘ ι₂)
      → f ≡ g
    unique-matrix p₁₁ p₂₁ p₁₂ p₂₂ = Coproduct.unique₂ biproduct.coproduct _
      (Product.unique₂ biproduct.product p₁₁ p₂₁ refl refl)
      (Product.unique₂ biproduct.product p₁₂ p₂₂ refl refl)
      _ refl refl

    ⊕₁≡⊗₁ : ∀ {a b c d} {f : Hom a b} {g : Hom c d} → f ⊕₁ g ≡ f ⊗₁ g
    ⊕₁≡⊗₁ = unique-matrix
      ((refl⟩∘⟨ in₀∘[]) ∙ cancell biproduct.πι₁ ∙ sym (pulll π₁∘⟨⟩ ∙ cancelr biproduct.πι₁))
      ((refl⟩∘⟨ in₀∘[]) ∙ pulll π₂-ι₁ ∙ zero-∘r _ ∙ sym (pulll π₂∘⟨⟩ ∙ pullr π₂-ι₁ ∙ zero-∘l _))
      ((refl⟩∘⟨ in₁∘[]) ∙ pulll π₁-ι₂ ∙ zero-∘r _ ∙ sym (pulll π₁∘⟨⟩ ∙ pullr π₁-ι₂ ∙ zero-∘l _))
      ((refl⟩∘⟨ in₁∘[]) ∙ cancell biproduct.πι₂ ∙ sym (pulll π₂∘⟨⟩ ∙ cancelr biproduct.πι₂))

    ∇-assoc : ∀ {a} → ∇ {a} ∘ (∇ {a} ⊕₁ id) ∘ ⊕-assoc ≡ ∇ ∘ (id ⊕₁ ∇)
    ∇-assoc = Coproduct.unique₂ biproduct.coproduct
      _
      (pullr (pullr in₀∘[]) ∙ (refl⟩∘⟨ pulll in₀∘[]) ∙ pulll (pulll in₀∘[]) ∙ pullr in₀∘[])
      (pullr (pullr in₁∘[]) ∙ []-unique _
        (pullr (pullr in₀∘[]) ∙ extend-inner in₀∘[] ∙ cancell in₀∘[] ∙ in₁∘[])
        (pullr (pullr in₁∘[]) ∙ (refl⟩∘⟨ in₁∘[]) ∙ pulll in₁∘[] ∙ idl _))
      _
      (pullr in₀∘[] ∙ pulll in₀∘[])
      (pullr in₁∘[] ∙ pulll in₁∘[] ∙ idl _)

    assoc-δ : ∀ {a} → ×-assoc ∘ (id ⊗₁ δ {a}) ∘ δ {a} ≡ (δ ⊗₁ id) ∘ δ
    assoc-δ = Product.unique₂ biproduct.product
      (pulll π₁∘⟨⟩ ∙ Product.unique₂ biproduct.product
        (pulll π₁∘⟨⟩ ∙ pulll π₁∘⟨⟩ ∙ pullr π₁∘⟨⟩)
        (pulll π₂∘⟨⟩ ∙ pullr (pulll π₂∘⟨⟩) ∙ pulll (pulll π₁∘⟨⟩) ∙ pullr π₂∘⟨⟩)
        (pulll (pulll π₁∘⟨⟩) ∙ pullr π₁∘⟨⟩)
        (pulll (pulll π₂∘⟨⟩) ∙ pullr π₁∘⟨⟩)
      ∙ pushl (sym π₁∘⟨⟩))
      (pulll π₂∘⟨⟩ ∙ pullr (pulll π₂∘⟨⟩) ∙ pulll (pulll π₂∘⟨⟩) ∙ pullr π₂∘⟨⟩)
      refl
      (pulll π₂∘⟨⟩ ∙ pullr π₂∘⟨⟩)

    coassoc≡assoc : ∀ {a b c} → ⊕-assoc {a} {b} {c} ≡ ×-assoc
    coassoc≡assoc = unique-matrix
      ((refl⟩∘⟨ in₀∘[]) ∙ cancell biproduct.πι₁ ∙ sym (pulll π₁∘⟨⟩ ∙ Product.unique₂ biproduct.product (pulll π₁∘⟨⟩ ∙ biproduct.πι₁) (pulll π₂∘⟨⟩ ∙ pullr π₂-ι₁ ∙ zero-∘l _) biproduct.πι₁ π₂-ι₁))
      ((refl⟩∘⟨ in₀∘[]) ∙ pulll π₂-ι₁ ∙ zero-∘r _ ∙ sym (pulll π₂∘⟨⟩ ∙ pullr π₂-ι₁ ∙ zero-∘l _))
      ((refl⟩∘⟨ in₁∘[]) ∙ unique-matrix
        ((refl⟩∘⟨ pullr in₀∘[] ∙ cancell biproduct.πι₁) ∙ π₁-ι₂ ∙ sym (pulll (pulll π₁∘⟨⟩) ∙ (π₁-ι₂ ⟩∘⟨refl) ∙ zero-∘r _))
        ((refl⟩∘⟨ pullr in₀∘[] ∙ cancell biproduct.πι₁) ∙ biproduct.πι₂ ∙ sym (pulll (pulll π₂∘⟨⟩) ∙ (cancelr biproduct.πι₂ ⟩∘⟨refl) ∙ biproduct.πι₁))
        ((refl⟩∘⟨ pullr in₁∘[] ∙ π₁-ι₂) ∙ zero-∘l _ ∙ sym (pulll (pulll π₁∘⟨⟩) ∙ (π₁-ι₂ ⟩∘⟨refl) ∙ zero-∘r _))
        ((refl⟩∘⟨ pullr in₁∘[] ∙ π₁-ι₂) ∙ zero-∘l _ ∙ sym (pulll (pulll π₂∘⟨⟩) ∙ (cancelr biproduct.πι₂ ⟩∘⟨refl) ∙ π₁-ι₂))
      ∙ sym (pulll π₁∘⟨⟩))
      ((refl⟩∘⟨ in₁∘[]) ∙ Coproduct.unique₂ biproduct.coproduct _ (pullr in₀∘[] ∙ pulll π₂-ι₁ ∙ zero-∘r _) (pullr in₁∘[] ∙ biproduct.πι₂) _ ((cancelr biproduct.πι₂ ⟩∘⟨refl) ∙ π₂-ι₁) ((cancelr biproduct.πι₂ ⟩∘⟨refl) ∙ biproduct.πι₂) ∙ sym (pulll π₂∘⟨⟩))

    +-assoc : ∀ {x y} {f g h : Hom x y} → f +→ (g +→ h) ≡ (f +→ g) +→ h
    +-assoc {f = f} {g} {h} =
      ∇ ∘ (f ⊗₁ (∇ ∘ (g ⊗₁ h) ∘ δ)) ∘ δ                           ≡˘⟨ refl⟩∘⟨ ⊗.pulll3 (idl _ ∙ idr _ ,ₚ refl) ⟩
      ∇ ∘ (id ⊗₁ ∇) ∘ (f ⊗₁ (g ⊗₁ h)) ∘ (id ⊗₁ δ) ∘ δ             ≡˘⟨ refl⟩∘⟨ ⊕₁≡⊗₁ ⟩∘⟨refl ⟩
      ∇ ∘ (id ⊕₁ ∇) ∘ (f ⊗₁ (g ⊗₁ h)) ∘ (id ⊗₁ δ) ∘ δ             ≡˘⟨ pushl ∇-assoc ⟩
      (∇ ∘ (∇ ⊕₁ id) ∘ ⊕-assoc) ∘ (f ⊗₁ (g ⊗₁ h)) ∘ (id ⊗₁ δ) ∘ δ ≡⟨ (refl⟩∘⟨ ⊕₁≡⊗₁ ⟩∘⟨refl) ⟩∘⟨refl ⟩
      (∇ ∘ (∇ ⊗₁ id) ∘ ⊕-assoc) ∘ (f ⊗₁ (g ⊗₁ h)) ∘ (id ⊗₁ δ) ∘ δ ≡⟨ pullr (pullr (coassoc≡assoc ⟩∘⟨refl)) ⟩
      ∇ ∘ (∇ ⊗₁ id) ∘ ×-assoc ∘ (f ⊗₁ (g ⊗₁ h)) ∘ (id ⊗₁ δ) ∘ δ   ≡⟨ refl⟩∘⟨ refl⟩∘⟨ extendl (associator .Isoⁿ.from .is-natural _ _ _) ⟩
      ∇ ∘ (∇ ⊗₁ id) ∘ ((f ⊗₁ g) ⊗₁ h) ∘ ×-assoc ∘ (id ⊗₁ δ) ∘ δ   ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-δ ⟩
      ∇ ∘ (∇ ⊗₁ id) ∘ ((f ⊗₁ g) ⊗₁ h) ∘ (δ ⊗₁ id) ∘ δ             ≡⟨ refl⟩∘⟨ ⊗.pulll3 (refl ,ₚ idl _ ∙ idr _) ⟩
      ∇ ∘ ((∇ ∘ (f ⊗₁ g) ∘ δ) ⊗₁ h) ∘ δ                           ∎

    coswap≡swap : ∀ {a b} → coswap {a} {b} ≡ swap
    coswap≡swap = ⟨⟩-unique _
      (Coproduct.unique₂ biproduct.coproduct _ (pullr in₀∘[] ∙ π₁-ι₂) (pullr in₁∘[] ∙ biproduct.πι₁) _ π₂-ι₁ biproduct.πι₂)
      (Coproduct.unique₂ biproduct.coproduct _ (pullr in₀∘[] ∙ biproduct.πι₂) (pullr in₁∘[] ∙ π₂-ι₁) _ biproduct.πι₁ π₁-ι₂)

    +-comm : ∀ {x y} {f g : Hom x y} → f +→ g ≡ g +→ f
    +-comm {f = f} {g} =
      ∇ ∘ (f ⊗₁ g) ∘ δ          ≡˘⟨ pulll ∇-coswap ⟩
      ∇ ∘ coswap ∘ (f ⊗₁ g) ∘ δ ≡⟨ refl⟩∘⟨ coswap≡swap ⟩∘⟨refl ⟩
      ∇ ∘ swap ∘ (f ⊗₁ g) ∘ δ   ≡˘⟨ refl⟩∘⟨ extendl (swap-natural _) ⟩
      ∇ ∘ (g ⊗₁ f) ∘ swap ∘ δ   ≡⟨ refl⟩∘⟨ refl⟩∘⟨ swap-δ ⟩
      ∇ ∘ (g ⊗₁ f) ∘ δ          ∎

    ∇-¡l : ∀ {a} → ∇ {a} ∘ (¡ ⊕₁ id) ≡ π₂
    ∇-¡l = Coproduct.unique₂ biproduct.coproduct
      _ (¡-unique₂ _ _) (pullr in₁∘[] ∙ cancell in₁∘[])
      _ refl biproduct.πι₂

    ∇-¡r : ∀ {a} → ∇ {a} ∘ (id ⊕₁ ¡) ≡ π₁
    ∇-¡r = Coproduct.unique₂ biproduct.coproduct
      _ (pullr in₀∘[] ∙ cancell in₀∘[]) (¡-unique₂ _ _)
      _ biproduct.πι₁ refl

    +-idl : ∀ {x y} {f : Hom x y} → zero→ +→ f ≡ f
    +-idl {f = f} =
      ∇ ∘ (zero→ ⊗₁ f) ∘ δ         ≡⟨ refl⟩∘⟨ ⊗.pushl (refl ,ₚ sym (idl _)) ⟩
      ∇ ∘ (¡ ⊗₁ id) ∘ (! ⊗₁ f) ∘ δ ≡˘⟨ refl⟩∘⟨ ⊕₁≡⊗₁ ⟩∘⟨refl ⟩
      ∇ ∘ (¡ ⊕₁ id) ∘ (! ⊗₁ f) ∘ δ ≡⟨ pulll ∇-¡l ⟩
      π₂ ∘ (! ⊗₁ f) ∘ δ            ≡⟨ pulll π₂∘⟨⟩ ⟩
      (f ∘ π₂) ∘ δ                 ≡⟨ cancelr π₂∘⟨⟩ ⟩
      f                            ∎

    +-idr : ∀ {x y} {f : Hom x y} → f +→ zero→ ≡ f
    +-idr {f = f} =
      ∇ ∘ (f ⊗₁ zero→) ∘ δ         ≡⟨ refl⟩∘⟨ ⊗.pushl (sym (idl _) ,ₚ refl) ⟩
      ∇ ∘ (id ⊗₁ ¡) ∘ (f ⊗₁ !) ∘ δ ≡˘⟨ refl⟩∘⟨ ⊕₁≡⊗₁ ⟩∘⟨refl ⟩
      ∇ ∘ (id ⊕₁ ¡) ∘ (f ⊗₁ !) ∘ δ ≡⟨ pulll ∇-¡r ⟩
      π₁ ∘ (f ⊗₁ !) ∘ δ            ≡⟨ pulll π₁∘⟨⟩ ⟩
      (f ∘ π₁) ∘ δ                 ≡⟨ cancelr π₁∘⟨⟩ ⟩
      f                            ∎

    ∘-linear-l
      : ∀ {a b c} (f g : Hom b c) (h : Hom a b)
      → f ∘ h +→ g ∘ h ≡ (f +→ g) ∘ h
    ∘-linear-l f g h =
      ∇ ∘ ((f ∘ h) ⊗₁ (g ∘ h)) ∘ δ ≡⟨ refl⟩∘⟨ ⊗.pushl refl ⟩
      ∇ ∘ (f ⊗₁ g) ∘ (h ⊗₁ h) ∘ δ  ≡˘⟨ pullr (pullr (diagonals .is-natural _ _ _)) ⟩
      (∇ ∘ (f ⊗₁ g) ∘ δ) ∘ h       ∎

    ∘-linear-r
      : ∀ {a b c} (f g : Hom a b) (h : Hom b c)
      → h ∘ f +→ h ∘ g ≡ h ∘ (f +→ g)
    ∘-linear-r f g h =
      ∇ ∘ ((h ∘ f) ⊗₁ (h ∘ g)) ∘ δ ≡⟨ refl⟩∘⟨ ⊗.pushl refl ⟩
      ∇ ∘ (h ⊗₁ h) ∘ (f ⊗₁ g) ∘ δ  ≡˘⟨ refl⟩∘⟨ ⊕₁≡⊗₁ ⟩∘⟨refl ⟩
      ∇ ∘ (h ⊕₁ h) ∘ (f ⊗₁ g) ∘ δ  ≡⟨ extendl (∇-natural _ _ _) ⟩
      h ∘ ∇ ∘ (f ⊗₁ g) ∘ δ         ∎
```

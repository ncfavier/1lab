```agda
open import Cat.Monoidal.Functor
open import Cat.Instances.Product
open import Cat.Monoidal.Base
open import Cat.Bi.Base
open import Cat.Functor.Base
open import Cat.Functor.Naturality
open import Cat.Prelude

import Cat.Reasoning

module Cat.Bi.Instances.Monoidal where

open Functor
open _=>_
open is-monoidal-transformation
open Lax-monoidal-functor-on

private variable
  o o' o'' ℓ ℓ' ℓ'' : Level

module _ {C : Precategory o ℓ} {D : Precategory o' ℓ'} (Cᵐ : Monoidal-category C) (Dᵐ : Monoidal-category D) where
  open Cat.Reasoning D
  open Monoidal-category Dᵐ
  MonCat[_,_] : Precategory (o ⊔ ℓ ⊔ o' ⊔ ℓ') (o ⊔ ℓ ⊔ ℓ')
  MonCat[_,_] .Precategory.Ob = Lax-monoidal-functor Cᵐ Dᵐ
  MonCat[_,_] .Precategory.Hom (F , Fᵐ) (G , Gᵐ) = Σ (F => G)
    (is-monoidal-transformation (F , Fᵐ) (G , Gᵐ))
  MonCat[_,_] .Precategory.Hom-set _ _ = hlevel 2
  MonCat[_,_] .Precategory.id .fst = idnt
  MonCat[_,_] .Precategory.id .snd .nat-ε = eliml refl
  MonCat[_,_] .Precategory.id .snd .nat-φ = eliml refl ∙ ⊗.intror refl
  MonCat[_,_] .Precategory._∘_ (α , αᵐ) (β , βᵐ) .fst = α ∘nt β
  MonCat[_,_] .Precategory._∘_ (α , αᵐ) (β , βᵐ) .snd .nat-ε = pullr (βᵐ .nat-ε) ∙ αᵐ .nat-ε
  MonCat[_,_] .Precategory._∘_ (α , αᵐ) (β , βᵐ) .snd .nat-φ = {!   !}
  MonCat[_,_] .Precategory.idr (α , αᵐ) = Σ-prop-path! (ext λ _ → idr _)
  MonCat[_,_] .Precategory.idl (α , αᵐ) = Σ-prop-path! (ext λ _ → idl _)
  MonCat[_,_] .Precategory.assoc = {!   !}

module _ {C : Precategory o ℓ} (Cᵐ : Monoidal-category C) where
  open Cat.Reasoning C
  open Monoidal-category Cᵐ
  Idᵐ : Lax-monoidal-functor-on Cᵐ Cᵐ Id
  Idᵐ .ε = id
  Idᵐ .F-mult .η _ = id
  Idᵐ .F-mult .is-natural _ _ _ = id-comm-sym
  Idᵐ .F-α→ = elimr (⊗.elimr refl) ∙ insertl (⊗.elimr refl)
  Idᵐ .F-λ← = elimr (⊗.elimr refl)
  Idᵐ .F-ρ← = elimr (⊗.elimr refl)

module _ {A : Precategory o ℓ} {B : Precategory o' ℓ'} {C : Precategory o'' ℓ''} (Aᵐ : Monoidal-category A) (Bᵐ : Monoidal-category B) (Cᵐ : Monoidal-category C) where
  M∘-functor : Functor (MonCat[ Bᵐ , Cᵐ ] ×ᶜ MonCat[ Aᵐ , Bᵐ ]) MonCat[ Aᵐ , Cᵐ ]
  M∘-functor .F₀ ((F , Fᵐ) , G , Gᵐ) .fst = F F∘ G
  M∘-functor .F₀ ((F , Fᵐ) , G , Gᵐ) .snd .ε = {!   !}
  M∘-functor .F₀ ((F , Fᵐ) , G , Gᵐ) .snd .F-mult = {!   !}
  M∘-functor .F₀ ((F , Fᵐ) , G , Gᵐ) .snd .F-α→ = {!   !}
  M∘-functor .F₀ ((F , Fᵐ) , G , Gᵐ) .snd .F-λ← = {!   !}
  M∘-functor .F₀ ((F , Fᵐ) , G , Gᵐ) .snd .F-ρ← = {!   !}
  M∘-functor .F₁ = {!   !}
  M∘-functor .F-id = {!   !}
  M∘-functor .F-∘ = {!   !}

open Prebicategory
MonCat : ∀ o ℓ → Prebicategory (lsuc o ⊔ lsuc ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
MonCat o ℓ .Ob = Σ (Precategory o ℓ) Monoidal-category
MonCat o ℓ .Hom (C , Cᵐ) (D , Dᵐ) = MonCat[ Cᵐ , Dᵐ ]
MonCat o ℓ .id = Id , Idᵐ _
MonCat o ℓ .compose = M∘-functor _ _ _
MonCat o ℓ .unitor-l = {!   !}
MonCat o ℓ .unitor-r = {!   !}
MonCat o ℓ .associator = {!   !}
MonCat o ℓ .triangle = {!   !}
MonCat o ℓ .pentagon = {!   !}
```

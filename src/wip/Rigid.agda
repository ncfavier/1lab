open import Cat.Functor.Hom.Representable
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.Naturality
open import Cat.Functor.Properties
open import Cat.Functor.Bifunctor as Bifunctor
open import Cat.Instances.Product
open import Cat.Monoidal.Braided
open import Cat.Monoidal.Functor
open import Cat.Morphism.Duality
open import Cat.Functor.Adjoint
open import Cat.Instances.Sets
open import Cat.Monoidal.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Bi.Diagram.Adjunction as Biadjunction
import Cat.Functor.Hom
import Cat.Reasoning

open _=>_

module wip.Rigid where

module _ {o ℓ}
  {C : Precategory o ℓ}
  (Cᵐ : Monoidal-category C)
  where
  open Cat.Reasoning C
  open Monoidal-category Cᵐ

  private variable
    A B : Ob

  record is-internal-hom ([A,B] : Ob) (ev : Hom ([A,B] ⊗ A) B) : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      ƛ        : ∀ {Γ} (m : Hom (Γ ⊗ A) B) → Hom Γ [A,B]
      commutes : ∀ {Γ} (m : Hom (Γ ⊗ A) B) → ev ∘ (ƛ m ⊗₁ id) ≡ m
      unique   : ∀ {Γ} {m : Hom (Γ ⊗ _) _} m'
               → ev ∘ (m' ⊗₁ id) ≡ m
               → m' ≡ ƛ m

    unique₂ : ∀ {C} {m : Hom (C ⊗ _) _} m₁ m₂
            → ev ∘ (m₁ ⊗₁ id) ≡ m
            → ev ∘ (m₂ ⊗₁ id) ≡ m
            → m₁ ≡ m₂
    unique₂ _ _ p q = unique _ p ∙ sym (unique _ q)

  open is-internal-hom

  internal-hom-unique
    : ∀ {A B [A,B] [A',B]} {ev : Hom ([A,B] ⊗ A) B} {ev' : Hom ([A',B] ⊗ A) B}
    → is-internal-hom [A,B] ev
    → is-internal-hom [A',B] ev'
    → [A,B] ≅ [A',B]
  internal-hom-unique {ev = ev} {ev'} exp1 exp2 =
    make-iso (exp2 .ƛ ev) (exp1 .ƛ ev')
      (unique₂ exp2 (exp2 .ƛ ev ∘ exp1 .ƛ ev') id
        (  ap (ev' ∘_) (ap₂ _⊗₁_ refl (sym (idl id)) ∙ -⊗- .F-∘ _ _)
        ·· pulll (exp2 .commutes _)
        ·· exp1 .commutes _)
        (elimr (-⊗- .F-id)))
      (unique₂ exp1 (exp1 .ƛ ev' ∘ exp2 .ƛ ev) id
        (  ap (ev ∘_) (ap₂ _⊗₁_ refl (sym (idl id)) ∙ -⊗- .F-∘ _ _)
        ·· pulll (exp1 .commutes _)
        ·· exp2 .commutes _)
        (elimr (-⊗- .F-id)))

module _ {o ℓ}
  {C : Precategory o ℓ}
  (Cᵐ : Monoidal-category C)
  (Cˢ : Symmetric-monoidal Cᵐ)
  where
  open Functor
  open Cat.Functor.Hom C

  record Rigid-category : Type (o ⊔ ℓ) where
    open Cat.Reasoning C public
    open Monoidal-category Cᵐ public
    open Symmetric-monoidal Cˢ public

    exchange : ∀ {A B C D} → Hom ((A ⊗ B) ⊗ (C ⊗ D)) ((A ⊗ C) ⊗ (B ⊗ D))
    exchange = α→ _ _ _ ∘ (α← _ _ _ ∘ (id ⊗₁ β→) ∘ α→ _ _ _ ⊗₁ id) ∘ α← _ _ _

    switch : ∀ {A B C} → Hom ((A ⊗ B) ⊗ C) ((A ⊗ C) ⊗ B)
    switch = α← _ _ _ ∘ (id ⊗₁ β→) ∘ α→ _ _ _

    field
      Hom[] : Functor (C ^op ×ᶜ C) C
      Tensor-Hom : ∀ {X} → Left -⊗- X ⊣ Right Hom[] X

    module Tensor-Hom {X} = _⊣_ (Tensor-Hom {X})

    hom : Ob → Ob → Ob
    hom X Y = Hom[] .F₀ (X , Y)

    infix 30 _ⱽ
    _ⱽ : Ob → Ob
    X ⱽ = hom X Unit

    ev : ∀ {A B} → Hom (hom A B ⊗ A) B
    ev = Tensor-Hom.ε _

    coev : ∀ {A B} → Hom B (hom A (B ⊗ A))
    coev = Tensor-Hom.η _

    zip-Hom : ∀ {X₁ Y₁ X₂ Y₂} → Hom (hom X₁ Y₁ ⊗ hom X₂ Y₂) (hom (X₁ ⊗ X₂) (Y₁ ⊗ Y₂))
    zip-Hom = L-adjunct Tensor-Hom ((ev ⊗₁ ev) ∘ exchange)

    field
      rigid : ∀ {X₁ Y₁ X₂ Y₂} → is-invertible (zip-Hom {X₁} {Y₁} {X₂} {Y₂})

    dualise : ∀ {X} → Hom X (X ⱽ ⱽ)
    dualise = L-adjunct Tensor-Hom (ev ∘ β→)

    field
      reflexive : ∀ {X} → is-invertible (dualise {X})

    λʰ→ : ∀ {X} → Hom X (hom Unit X)
    λʰ→ = L-adjunct Tensor-Hom ρ←

    λʰ : ∀ {X} → X ≅ hom Unit X
    -- λʰ = make-iso λʰ→ (ev ∘ ρ→) {!   !} {!   !}
    λʰ = is-ff→essentially-injective {F = よ} よ-is-fully-faithful (iso→isoⁿ
      (λ A → equiv→iso (dom-iso→hom-equiv (isoⁿ→iso unitor-r A) ∙e adjunct-hom-equiv Tensor-Hom))
      λ f → {!   !})

    hom≃dual⊗ : ∀ {X Y} → hom X Y ≅ X ⱽ ⊗ Y
    hom≃dual⊗ =
      F-map-iso Hom[] (iso→co-iso C (isoⁿ→iso unitor-r _ Iso⁻¹) ,iso isoⁿ→iso unitor-l _)
      ∘Iso (invertible→iso _ rigid Iso⁻¹)
      ∘Iso ▶.F-map-iso (λʰ Iso⁻¹)

    h← : ∀ {X Y} → Hom (X ⱽ ⊗ Y) (hom X Y)
    -- h← = Hom[] .F₁ (ρ→ , λ←) ∘ zip-Hom ∘ (id ⊗₁ λʰ→)
    h← = hom≃dual⊗ .from

    h→ : ∀ {X Y} → Hom (hom X Y) (X ⱽ ⊗ Y)
    h→ = hom≃dual⊗ .to

    coev' : ∀ {A} → Hom Unit (A ⊗ A ⱽ)
    -- coev' = β→ ∘ (id ⊗₁ λ←) ∘ h→ ∘ coev
    coev' = ((ρ← ∘ λʰ .from) ⊗₁ id) ∘ β→ ∘ rigid .is-invertible.inv ∘ coev

    -- has-duals : ∀ {X} → Biadjunction._⊣_ (Deloop Cᵐ) (X ⱽ) X
    -- has-duals .Biadjunction._⊣_.η = coev'
    -- has-duals .Biadjunction._⊣_.ε = ev
    -- has-duals .Biadjunction._⊣_.zig = {!   !}
    -- has-duals .Biadjunction._⊣_.zag = {!   !}

    open is-internal-hom
    has-hom : ∀ {X Y} → is-internal-hom Cᵐ (hom X Y) ev
    has-hom .ƛ = L-adjunct Tensor-Hom
    has-hom .commutes = R-L-adjunct Tensor-Hom
    has-hom .unique _ = R-adjunct.adjunctl Tensor-Hom

    -- has-repr : ∀ {X Y} → Representation {C = C} (Hom-into Y F∘ Functor.op (Left -⊗- X))
    -- has-repr {X} {Y} .Representation.rep = hom X Y
    -- has-repr .Representation.represents = adjunct-hom-iso-into Tensor-Hom _

    has-homⱽ : ∀ {X Y} → is-internal-hom Cᵐ (X ⱽ ⊗ Y) (λ← ∘ (ev ⊗₁ id) ∘ switch)
    has-homⱽ .ƛ f = β→ ∘ (f ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ coev') ∘ ρ→
    has-homⱽ .commutes m = {!   !}
    has-homⱽ .unique m' = {!   !}

module _ {o ℓ} {o' ℓ'}
  {C : Precategory o ℓ} {D : Precategory o' ℓ'}
  (Cᵐ : Monoidal-category C)
  (Cˢ : Symmetric-monoidal Cᵐ)
  (Cʳ : Rigid-category Cᵐ Cˢ)
  (Dᵐ : Monoidal-category D)
  (Dˢ : Symmetric-monoidal Dᵐ)
  (Dʳ : Rigid-category Dᵐ Dˢ)
  (F : Functor C D)
  (Fᵐ : Monoidal-functor-on Cᵐ Dᵐ F)
  (Fˢ : is-symmetric-functor Cᵐ Dᵐ Cˢ Dˢ (_ , Fᵐ .Monoidal-functor-on.lax))
  where
  module C = Rigid-category Cʳ
  module D = Rigid-category Dʳ
  module F = Monoidal-functor-on Fᵐ

  F-dual : ∀ {X} → F.₀ (X C.ⱽ) D.≅ F.₀ X D.ⱽ
  F-dual = D.make-iso
    (L-adjunct D.Tensor-Hom (F.ε← D.∘ F.₁ C.ev D.∘ F.φ→))
    (D.λ← D.∘ (D.ev D.⊗₁ D.id) D.∘ D.α← _ _ _ D.∘ (D.id D.⊗₁ F.φ← D.∘ F.₁ C.coev' D.∘ F.ε→) D.∘ D.ρ→)
    {!   !} {!   !}

  -- F-hom← : ∀ {X Y} → D.Hom (D.hom (F.₀ X) (F.₀ Y)) (F.₀ (C.hom X Y))
  -- F-hom← = F.₁ C.h← D.∘ F.φ→ D.∘ (D.id D.⊗₁ D.ev) D.∘ {!  C.coev !}

  -- F-hom' : ∀ {X Y} → F.₀ (C.hom X Y) D.≅ D.hom (F.₀ X) (F.₀ Y)
  -- F-hom' = ((F.F-map-iso C.hom≃dual⊗ D.∘Iso F.φ D.Iso⁻¹) D.∘Iso D.◀.F-map-iso F-dual) D.∘Iso D.hom≃dual⊗ D.Iso⁻¹

  -- F-hom≡F-hom' : ∀ {X Y} → F-hom {X} {Y} ≡ F-hom' {X} {Y} .D.to
  -- F-hom≡F-hom' =
  --   L-adjunct D.Tensor-Hom (F.₁ C.ev D.∘ F.φ→) ≡⟨ {!   !} ⟩
  --   D.h← D.∘ D.◀.₁ (F-dual .D.to) D.∘ F.φ← D.∘ F.₁ C.h→ ∎

  -- F-hom-invertible : ∀ {X Y} → D.is-invertible (F-hom {X} {Y})
  -- F-hom-invertible = subst D.is-invertible (sym F-hom≡F-hom') (D.iso→invertible F-hom')

  F-hom : ∀ {X Y} → D.Hom (F.₀ (C.hom X Y)) (D.hom (F.₀ X) (F.₀ Y))
  F-hom = L-adjunct D.Tensor-Hom (F.₁ C.ev D.∘ F.φ→)

  open is-internal-hom
  F-hom' : ∀ {X Y} → is-internal-hom Dᵐ (F.₀ (C.hom X Y)) (F.₁ C.ev D.∘ F.φ→)
  F-hom' .ƛ f = F.₁ C.h← D.∘ F.φ→ D.∘ D.β→ D.∘ (f D.⊗₁ F-dual .D.from) D.∘ D.α← _ _ _ D.∘ (D.id D.⊗₁ D.coev') D.∘ D.ρ→
  F-hom' .commutes m =
    (F.₁ C.ev D.∘ F.φ→) D.∘ ((F.₁ C.h← D.∘ F.φ→ D.∘ D.β→ D.∘ (m D.⊗₁ F-dual .D.from) D.∘ D.α← _ _ _ D.∘ (D.id D.⊗₁ D.coev') D.∘ D.ρ→) D.⊗₁ D.id) ≡⟨ {!   !} ⟩
      m ∎
  F-hom' .unique = {!   !}

  -- has-repr : ∀ {X Y} → Representation {C = C} (Hom-into Y F∘ Functor.op (Left -⊗- X))

  hom-unique : ∀ {X Y} → F.₀ (C.hom X Y) D.≅ D.hom (F.₀ X) (F.₀ Y)
  hom-unique = internal-hom-unique Dᵐ F-hom' D.has-hom

  F-hom-invertible : ∀ {X Y} → D.is-invertible (F-hom {X} {Y})
  F-hom-invertible = D.iso→invertible hom-unique

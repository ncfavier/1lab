module TT.SOGATExamples where

open import 1Lab.Prelude hiding (id ; _∘_)

open import TT.SOGAT

module _ where
  open ToS⁺

  asU : Tm Γ (U [ σ ]T) → Tm Γ U
  asU = subst (Tm _) U[]

  vzU : Tm (Γ ▹ U) U
  vzU = asU vz

  vsU : Tm Γ U → Tm (Γ ▹ A) U
  vsU a = asU (a [ wk ]t)

  asU⁺ : Tm Γ (U⁺ [ σ ]T) → Tm Γ U⁺
  asU⁺ = subst (Tm _) U⁺[]

  vzU⁺ : Tm (Γ ▹ U⁺) U⁺
  vzU⁺ = asU⁺ vz

  vsU⁺ : Tm Γ U⁺ → Tm (Γ ▹ A) U⁺
  vsU⁺ a = asU⁺ (a [ wk ]t)

  El⁺[] : (a : Tm Γ U⁺) → El⁺ a [ σ ]T ≡ El⁺ (asU⁺ (a [ σ ]t))
  El⁺[] a = El[] _ (inc[] (transport-filler _ _))

  -- untyped λ-calculus
  Λ : SOGAT
  Λ = []
    ▹ U⁺ -- tm
    ▹ inc vzU⁺ ⇒ (inc vzU⁺ ⇒ El⁺ vzU⁺) -- app : tm Γ → tm Γ → tm Γ
    -- ▹ inc vzU⁺ ⇒ El (π⁺ vzU⁺ (inc (vsU⁺ vzU⁺))) -- λ⁻¹ : tm Γ → tm (Γ ▹)
    -- ▹ El (π⁺ vzU⁺ (π⁺ (vsU⁺ vzU⁺) (inc (vsU⁺ (vsU⁺ vzU⁺))))) -- ? : tm (Γ ▹ ▹)
    ▹ π⁺ (vsU⁺ vzU⁺) (inc (vsU⁺ (vsU⁺ vzU⁺))) ⇒ El⁺ (vsU⁺ vzU⁺) -- λ : tm (Γ ▹) → tm Γ
    ▹ Π (inc (vsU⁺ (vsU⁺ vzU⁺))) {!  !} -- β
    -- ...

  -- basic dependent type theory
  DTT : SOGAT
  DTT
    = []
    ▹ U -- ty
    ▹ Π vzU U⁺ -- tm

  -- interval theory
  Int : SOGAT
  Int
    = []
    ▹ U⁺ -- I
    ▹ El⁺ vzU⁺ -- i0 : I
    ▹ El⁺ (vsU⁺ vzU⁺) -- i1 : I

  module _ (T : SOGAT) where
    -- ToS⁺ is the theory of SOGATs
    --   = initial model of DTT⁺[DTT⁺]
    --   = walking model of DTT⁺
    -- ToS⁺/T is the theory of SOGAT extensions of T
    --   = initial model of DTT⁺[DTT⁺[T]]
    -- restricting that to representables (U-contexts) yields the walking model of T
    --   = initial model of DTT⁺[T]
    -- restricting *that* to representables (U⁺-contexts) yields the initial model of T

    mutual -- small IR
      data TCon : Type where
        [] : TCon
        _▹_ : (Γ⁺ : TCon) → Tm (T+ Γ⁺) U⁺ → TCon

      T+ : TCon → Con
      T+ [] = T
      T+ (Γ⁺ ▹ a) = T+ Γ⁺ ▹ El (inc a)

    private variable
      Γ⁺ Δ⁺ : TCon

    T↓ : (Γ⁺ : TCon) → Sub (T+ Γ⁺) T
    T↓ [] = id
    T↓ (Γ⁺ ▹ a) = T↓ Γ⁺ ∘ wk

    mutual -- small IR
      data TSub : TCon → TCon → Type where
        [] : TSub Γ⁺ []
        _▹_
          : (σ⁺ : TSub Γ⁺ Δ⁺)
          → Tm (T+ Γ⁺) (El⁺ (asU⁺ (a [ T+Sub σ⁺ ]t)))
          → TSub Γ⁺ (Δ⁺ ▹ a)

      T+Sub : TSub Γ⁺ Δ⁺ → Sub (T+ Γ⁺) (T+ Δ⁺)
      T+Sub {Γ⁺} [] = T↓ Γ⁺
      T+Sub (σ⁺ ▹ t) = T+Sub σ⁺ ▹ subst (Tm _) (sym (El⁺[] _)) t

  -- direct semantics: interpretation of ToS⁺ in PSh(PSh(C))

  open import Cat.Prelude
  open import Cat.Functor.Base
  open import Cat.Cartesian
  open import Cat.Instances.Presheaf.Limits
  open import TT.PresheafCwF
  open Functor
  module Direct {o ℓ} (C : Precategory o ℓ) where
    κ = o ⊔ ℓ
    C^ = PSh κ C
    C^^ = PSh (lsuc κ) C^
    module C^ = Precategory C^
    module C^^ = Precategory C^^
    module C-cwf = PShGCwF C
    module C^-cwf = PShGCwF C^
    module C^-cart = Cartesian-category (PSh-cartesian κ C)
    module C^^-cart = Cartesian-category (PSh-cartesian (lsuc κ) C^)

    -- Con/Ty → [[C, Set], Grpd]
    -- U ↦ P ↦ Ty(P)
    ⟦_⟧𞁞 : Con → C^^.Ob
    ⟦_⟧ₜ : Ty Γ → C^-cwf.Ty.Ob ⟦ Γ ⟧𞁞
    ⟦ [] ⟧𞁞 = C^^-cart.top
    ⟦ Γ ▹ A ⟧𞁞 = ⟦ Γ ⟧𞁞 C^-cwf.▶ ⟦ A ⟧ₜ
    ⟦ A [ x ]T ⟧ₜ = {!   !}
    ⟦ [id]T i ⟧ₜ = {!   !}
    ⟦ [∘]T i ⟧ₜ = {!   !}
    ⟦ U ⟧ₜ = {!   !}
    ⟦ U[] i ⟧ₜ = {!   !}
    ⟦ U⁺ ⟧ₜ = {!   !}
    ⟦ U⁺[] i ⟧ₜ = {!   !}
    ⟦ El x ⟧ₜ = {!   !}
    ⟦ El[] σ p i ⟧ₜ = {!   !}
    ⟦ Π a A ⟧ₜ = {!   !}
    ⟦ Π[] p p' i ⟧ₜ = {!   !}
    ⟦ 𝟙 ⟧ₜ = ⊤PSh _ _
    ⟦ 𝟙[] i ⟧ₜ = {!   !}
    ⟦ Eq A a b ⟧ₜ = {!   !}
    ⟦ Eq[] i ⟧ₜ = {!   !}
    ⟦ squash A A₁ x y x₁ y₁ i i₁ i₂ ⟧ₜ = {!   !}

    interp : SOGAT → Type (lsuc κ)
    interp T = ⌞ ⟦ T ⟧𞁞 .F₀ C^-cart.top ⌟

    _ = {! interp DTT  !}

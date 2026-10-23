{-# OPTIONS --allow-unsolved-metas #-}
open import Cat.Prelude
open import Cat.Functor.Base
open import Cat.Instances.Presheaf.Limits
open import Cat.Instances.Presheaf.Exponentials
open import Cat.Instances.Elements
open import Cat.Instances.Slice
open import Cat.Instances.Slice.Presheaf
open import Cat.Diagram.Exponential

open /-Obj
open Functor

module TT.PresheafCwF where

-- Presheaves on C have the structure of a (groupoid) category with families.
module PShGCwF {o ℓ} (C : Precategory o ℓ) where
  κ = o ⊔ ℓ
  C^ = PSh κ C
  module C^ = Precategory C^

  Ty : C^.Ob → Precategory _ _
  Ty P = PSh κ (∫ _ P)

  module Ty P = Precategory (Ty P)

  infixl 40 _▶_
  _▶_ : ∀ P → Ty.Ob P → C^.Ob
  P ▶ A = presheaf→slice-ob A .dom

  Σ' : ∀ {P} (A : Ty.Ob P) (B : Ty.Ob (P ▶ A)) → Ty.Ob P
  Σ' A B = presheaf→slice-ob (B F∘ Functor.op (∫-assoc A)) .dom

  Σπ : ∀ {P} (A : Ty.Ob P) (B : Ty.Ob (P ▶ A)) → Ty.Hom P (Σ' A B) A
  Σπ A B = presheaf→slice-ob (B F∘ Functor.op (∫-assoc A)) .map

  Π : ∀ {P} → (A : Ty.Ob P) (B : Ty.Ob (P ▶ A)) → Ty.Ob P
  Π {P} A B = exponentiable→product (Ty P)
    (PSh-cartesian κ _)
    A
    (λ B → PSh-closed (∫ C P) .Cartesian-closed.has-exp A B)
    (PSh-pullbacks κ _)
    .F₀ (cut (Σπ A B))

-- module _ {ℓ} (C : Precategory ℓ ℓ) where
--   C^ = PSh ℓ C
--   module C^ = Precategory C^
  C^^ = PSh (lsuc κ) C^
  module C^^ = Precategory C^^

  Ty^ : C^^.Ob -- groupoid-valued presheaf
  Ty^ .F₀ Γ = el (Ty Γ .Precategory.Ob) {!   !}
  Ty^ .F₁ {P} {Q} σ = {!   !}
  Ty^ .F-id = {!   !}
  Ty^ .F-∘ = {!   !}

  π : ∀ {P} (A : Ty.Ob P) (B : Ty.Ob (P ▶ A)) → Ty.Ob P
  π A B .F₀ (Γ , x) = el! ((a : ∣ A .Functor.F₀ (Γ , x) ∣) → ∣ B .Functor.F₀ (Γ , x , a) ∣)
  π A B .F₁ = {!   !}
  π A B .F-id = {!   !}
  π A B .F-∘ = {!   !}

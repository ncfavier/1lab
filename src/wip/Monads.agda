open import Cat.Functor.Naturality
open import Cat.Monoidal.Diagonals
open import Cat.Functor.Bifunctor
open import Cat.Functor.Coherence
open import Cat.Instances.Product
open import Cat.Monoidal.Braided
open import Cat.Monoidal.Functor
open import Cat.Monoidal.Strength
open import Cat.Functor.Compose
open import Cat.Diagram.Monad
open import Cat.Monoidal.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Monoidal.Monad
import Cat.Reasoning

module wip.Monads where

module _ {o ℓ} {C : Precategory o ℓ} (C-monoidal : Monoidal-category C) (M-monad : Monad C) where
  open Cat.Reasoning C
  open Monoidal-category C-monoidal
  open Monad M-monad
  open Cat.Monoidal.Monad C-monoidal
  private
    module M = Cat.Functor.Reasoning M

  record Left-monad-strength : Type (o ⊔ ℓ) where
    field
      functor-strength : Left-strength C-monoidal M

    open Left-strength functor-strength public

    field
      left-strength-η : ∀ {A B} → σ ∘ (id ⊗₁ η B) ≡ η (A ⊗ B)
      left-strength-μ : ∀ {A B} → σ ∘ (id ⊗₁ μ B) ≡ μ (A ⊗ B) ∘ M₁ σ ∘ σ

  record Right-monad-strength : Type (o ⊔ ℓ) where
    field
      functor-strength : Right-strength C-monoidal M

    open Right-strength functor-strength public

    field
      right-strength-η : ∀ {A B} → τ ∘ (η A ⊗₁ id) ≡ η (A ⊗ B)
      right-strength-μ : ∀ {A B} → τ ∘ (μ A ⊗₁ id) ≡ μ (A ⊗ B) ∘ M₁ τ ∘ τ

  record Monad-strength : Type (o ⊔ ℓ) where
    field
      strength-left : Left-monad-strength
      strength-right : Right-monad-strength

    open Left-monad-strength strength-left public
    open Right-monad-strength strength-right public

    field
      strength-α→ : ∀ {A B C}
        → M₁ (α→ A B C) ∘ τ ∘ (σ ⊗₁ id) ≡ σ ∘ (id ⊗₁ τ) ∘ α→ A (M₀ B) C

    functor-strength' : Strength C-monoidal M
    functor-strength' .Strength.strength-left = strength-left .Left-monad-strength.functor-strength
    functor-strength' .Strength.strength-right = strength-right .Right-monad-strength.functor-strength
    functor-strength' .Strength.strength-α→ = strength-α→

    left-φ right-φ : -⊗- F∘ (M F× M) => M F∘ -⊗-
    left-φ = (mult ◂ -⊗-) ∘nt nat-assoc-to (M ▸ left-strength) ∘nt τ'
      where
        unquoteDecl τ' = cohere-into τ' (-⊗- F∘ (M F× M) => M F∘ -⊗- F∘ (Id F× M)) (right-strength ◂ (Id F× M))
    right-φ = (mult ◂ -⊗-) ∘nt nat-assoc-to (M ▸ right-strength) ∘nt σ'
      where
        unquoteDecl σ' = cohere-into σ' (-⊗- F∘ (M F× M) => M F∘ -⊗- F∘ (M F× Id)) (left-strength ◂ (M F× Id))

    is-commutative-strength : Type (o ⊔ ℓ)
    is-commutative-strength = right-φ ≡ left-φ

  is-idempotent-monad : Type (o ⊔ ℓ)
  is-idempotent-monad = is-invertibleⁿ mult

  idempotent-monad→η≡Mη : is-idempotent-monad → ∀ A → η (M₀ A) ≡ M₁ (η A)
  idempotent-monad→η≡Mη idem A = invertible→monic
    (is-invertibleⁿ→is-invertible idem A) _ _
    (right-ident ∙ sym left-ident)

  idempotent→commutative : is-idempotent-monad → ∀ s → Monad-strength.is-commutative-strength s
  idempotent→commutative idem s = ext λ (A , B) →
    -- https://ncatlab.org/nlab/show/idempotent+monad#idempotent_strong_monads_are_commutative
    μ _ ∘ M₁ τ ∘ σ ≡⟨ insertl right-ident ⟩
    μ _ ∘ η _ ∘ μ _ ∘ M₁ τ ∘ σ ≡⟨ refl⟩∘⟨ unit.is-natural _ _ _ ⟩
    μ _ ∘ M₁ (μ _ ∘ M₁ τ ∘ σ) ∘ η _ ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ right-strength-η ⟩
    μ _ ∘ M₁ (μ _ ∘ M₁ τ ∘ σ) ∘ τ ∘ (⌜ η _ ⌝ ⊗₁ id) ≡⟨ ap! (idempotent-monad→η≡Mη idem _) ⟩
    μ _ ∘ M₁ (μ _ ∘ M₁ τ ∘ σ) ∘ τ ∘ (M₁ (η _) ⊗₁ id) ≡⟨ refl⟩∘⟨ refl⟩∘⟨ τ.is-natural _ _ _ ⟩
    μ _ ∘ M₁ (μ _ ∘ M₁ τ ∘ σ) ∘ M₁ (η _ ⊗₁ ⌜ id ⌝) ∘ τ ≡⟨ ap! (sym M.F-id) ⟩
    μ _ ∘ M₁ (μ _ ∘ M₁ τ ∘ σ) ∘ M₁ (η _ ⊗₁ M₁ id) ∘ τ ≡⟨ refl⟩∘⟨ M.popr (M.popr (extendl (M.weave (σ.is-natural _ _ _)))) ⟩
    μ _ ∘ M₁ (μ _) ∘ M₁ (M₁ τ) ∘ M₁ (M₁ (η _ ⊗₁ id)) ∘ M₁ σ ∘ τ ≡⟨ refl⟩∘⟨ refl⟩∘⟨ M.pulll (M.collapse right-strength-η) ⟩
    μ _ ∘ M₁ (μ _) ∘ M₁ (M₁ (η _)) ∘ M₁ σ ∘ τ ≡⟨ refl⟩∘⟨ M.cancell left-ident ⟩
    μ _ ∘ M₁ σ ∘ τ ∎
    where open Monad-strength s

  _nt×_ : ∀ {o ℓ o' ℓ'} {C C' : Precategory o ℓ} {D D' : Precategory o' ℓ'} {F : Functor C C'} {G : Functor C C'} {H : Functor D D'} {K : Functor D D'} → F => G → H => K → (F F× H) => (G F× K)
  _nt×_ α β ._=>_.η (c , d) = α ._=>_.η c , β ._=>_.η d
  _nt×_ α β ._=>_.is-natural (c , d) (c' , d') (f , g) = Σ-pathp (α ._=>_.is-natural c c' f) (β ._=>_.is-natural d d' g)

  module L {A} = Cat.Functor.Reasoning (Left -⊗- A)
  module R {A} = Cat.Functor.Reasoning (Right -⊗- A)

  monoidal≃commutative : Monoidal-monad-on M-monad ≃ Σ _ Monad-strength.is-commutative-strength
  monoidal≃commutative = Iso→Equiv is where
    open is-iso
    is : Iso _ _
    is .fst m = s , sc where
      open Monoidal-monad-on m
      open Monad-strength
      open Left-strength
      open Right-strength
      open Left-monad-strength
      open Right-monad-strength
      s : Monad-strength
      s .strength-left .functor-strength .left-strength = F-mult ∘nt (-⊗- ▸ (unit nt× idnt))
      s .strength-left .functor-strength .left-strength-λ← =
        M₁ λ← ∘ φ ∘ (η _ ⊗₁ id) ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ ap (_⊗₁ id) unit-ε ⟩
        M₁ λ← ∘ φ ∘ (ε ⊗₁ id) ≡⟨ F-λ← ⟩
        λ← ∎
      s .strength-left .functor-strength .left-strength-α→ =
        -- https://q.uiver.app/#q=WzAsMTAsWzAsMCwiKEFcXG90aW1lcyBCKVxcb3RpbWVzIE1DIl0sWzAsMywiQVxcb3RpbWVzIChCXFxvdGltZXMgTUMpIl0sWzEsMywiQVxcb3RpbWVzIChNQlxcb3RpbWVzIE1DKSJdLFsyLDMsIkFcXG90aW1lcyBNKEJcXG90aW1lcyBDKSJdLFszLDMsIk1BXFxvdGltZXMgTShCXFxvdGltZXMgQykiXSxbNCwzLCJNKEFcXG90aW1lcyAoQlxcb3RpbWVzIEMpKSJdLFsyLDAsIk0oQVxcb3RpbWVzIEIpXFxvdGltZXMgTUMiXSxbNCwwLCJNKChBXFxvdGltZXMgQilcXG90aW1lcyBDKSJdLFsyLDIsIk1BXFxvdGltZXMgKE1CXFxvdGltZXMgTUMpIl0sWzIsMSwiKE1BXFxvdGltZXMgTUIpXFxvdGltZXMgTUMiXSxbMCwxXSxbMSwyXSxbMiwzXSxbMyw0XSxbNCw1XSxbMCw2XSxbNiw3XSxbNyw1XSxbOCw0XSxbOSw4XSxbOSw2XSxbMiw4XSxbMCw5XSxbMSw4XV0=
        M₁ (α→ _ _ _) ∘ φ ∘ (η _ ⊗₁ id) ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ L.collapse unit-φ ⟩
        M₁ (α→ _ _ _) ∘ φ ∘ (φ ⊗₁ id) ∘ ((η _ ⊗₁ η _) ⊗₁ id) ≡⟨ extendl3 F-α→ ⟩
        φ ∘ (id ⊗₁ φ) ∘ α→ _ _ _ ∘ ((η _ ⊗₁ η _) ⊗₁ id) ≡⟨ refl⟩∘⟨ refl⟩∘⟨ associator .Isoⁿ.to ._=>_.is-natural _ _ _ ⟩
        φ ∘ (id ⊗₁ φ) ∘ (η _ ⊗₁ (η _ ⊗₁ id)) ∘ α→ _ _ _ ≡⟨ refl⟩∘⟨ ⊗.pulll (Σ-pathp (idl _) refl) ⟩
        φ ∘ (η _ ⊗₁ (φ ∘ (η _ ⊗₁ id))) ∘ α→ _ _ _ ≡⟨ pushr (⊗.pushl (Σ-pathp (sym (idr _)) (sym (idl _)))) ⟩
        (φ ∘ (η _ ⊗₁ id)) ∘ (id ⊗₁ (φ ∘ (η _ ⊗₁ id))) ∘ α→ _ _ _ ∎
      s .strength-left .left-strength-η =
        (φ ∘ (η _ ⊗₁ id)) ∘ (id ⊗₁ η _) ≡⟨ pullr (⊗.collapse (Σ-pathp (idr _) (idl _))) ⟩
        φ ∘ (η _ ⊗₁ η _) ≡⟨ unit-φ ⟩
        η _ ∎
      s .strength-left .left-strength-μ =
        -- https://q.uiver.app/#q=WzAsOSxbMCwwLCJBXFxvdGltZXMgTU1CIl0sWzAsMiwiQSBcXG90aW1lcyBNQiJdLFsyLDAsIk0oQVxcb3RpbWVzIE1CKSJdLFs0LDAsIk1eMihBXFxvdGltZXMgQikiXSxbNCwyLCJNKEFcXG90aW1lcyBCKSJdLFsxLDIsIk1BXFxvdGltZXMgTUIiXSxbMSwwLCJNQVxcb3RpbWVzIE1NQiJdLFszLDAsIk0oTUFcXG90aW1lcyBNQikiXSxbMiwxLCJNTUFcXG90aW1lcyBNTUIiXSxbMCwxXSxbMyw0XSxbMSw1XSxbNSw0XSxbMCw2XSxbNiwyXSxbMiw3XSxbNywzXSxbNiw4XSxbOCw1XSxbOCw3XSxbNiw1XV0=
        (φ ∘ (η _ ⊗₁ id)) ∘ (id ⊗₁ μ _) ≡⟨ pullr (⊗.collapse (Σ-pathp (idr _) (idl _))) ⟩
        φ ∘ (η _ ⊗₁ μ _) ≡˘⟨ (refl⟩∘⟨ ⊗.collapse3 (Σ-pathp (cancell left-ident) (elimr (eliml M.F-id)))) ⟩
        φ ∘ (μ _ ⊗₁ μ _) ∘ (M₁ (η _) ⊗₁ M₁ id) ∘ (η _ ⊗₁ id) ≡⟨ pulll mult-φ ⟩
        (μ _ ∘ M₁ φ ∘ φ) ∘ (M₁ (η _) ⊗₁ M₁ id) ∘ (η _ ⊗₁ id) ≡⟨ pullr (pullr (extendl (φ.is-natural _ _ _))) ⟩
        μ _ ∘ M₁ φ ∘ M₁ (η _ ⊗₁ id) ∘ φ ∘ (η _ ⊗₁ id) ≡⟨ refl⟩∘⟨ M.pulll refl ⟩
        μ _ ∘ M₁ (φ ∘ (η _ ⊗₁ id)) ∘ φ ∘ (η _ ⊗₁ id) ∎
      -- s .strength-right .functor-strength .right-strength = F-mult ∘nt (-⊗- ▸ (idnt nt× unit))
      s .strength-right .functor-strength = {! left≃right C-monoidal M C-braided  !}
      s .strength-right .right-strength-η = {!   !}
      s .strength-right .right-strength-μ = {!   !}
      s .strength-α→ =
        -- https://q.uiver.app/#q=WzAsMTIsWzAsMCwiKEFcXG90aW1lcyBNQilcXG90aW1lcyBDIl0sWzIsMCwiQVxcb3RpbWVzIChNQlxcb3RpbWVzIEMpIl0sWzAsMiwiTShBXFxvdGltZXMgQilcXG90aW1lcyBDIl0sWzIsMiwiQVxcb3RpbWVzIE0oQlxcb3RpbWVzIEMpIl0sWzAsNCwiTSgoQVxcb3RpbWVzIEIpXFxvdGltZXMgQykiXSxbMiw0LCJNKEFcXG90aW1lcyAoQlxcb3RpbWVzIEMpKSJdLFswLDEsIihNQVxcb3RpbWVzIE1CKVxcb3RpbWVzIEMiXSxbMiwxLCJBXFxvdGltZXMgKE1CXFxvdGltZXMgTUMpIl0sWzAsMywiTShBXFxvdGltZXMgQilcXG90aW1lcyBNQyJdLFsyLDMsIk1BXFxvdGltZXMgTShCXFxvdGltZXMgQykiXSxbMSwxLCIoTUFcXG90aW1lcyBNQilcXG90aW1lcyBNQyJdLFsxLDMsIk1BXFxvdGltZXMgKE1CXFxvdGltZXMgTUMpIl0sWzAsMV0sWzQsNV0sWzAsNl0sWzYsMl0sWzEsN10sWzcsM10sWzIsOF0sWzgsNF0sWzMsOV0sWzksNV0sWzYsMTBdLFsxMCwxMV0sWzExLDldLFs3LDExXSxbMTAsOF1d
        M₁ (α→ _ _ _) ∘ (φ ∘ (id ⊗₁ η _)) ∘ ((φ ∘ (η _ ⊗₁ id)) ⊗₁ id) ≡⟨ refl⟩∘⟨ {!   !} ⟩
        M₁ (α→ _ _ _) ∘ φ ∘ (φ ⊗₁ id) ∘ ((η _ ⊗₁ id) ⊗₁ η _) ≡⟨ extendl3 F-α→ ⟩
        φ ∘ (id ⊗₁ φ) ∘ α→ _ _ _ ∘ ((η _ ⊗₁ id) ⊗₁ η _) ≡⟨ refl⟩∘⟨ refl⟩∘⟨ associator .Isoⁿ.to ._=>_.is-natural _ _ _ ⟩
        φ ∘ (id ⊗₁ φ) ∘ (η _ ⊗₁ (id ⊗₁ η _)) ∘ α→ _ _ _ ≡⟨ pushr (extendl {!   !}) ⟩
        (φ ∘ (η _ ⊗₁ id)) ∘ (id ⊗₁ (φ ∘ (id ⊗₁ η _))) ∘ α→ _ _ _ ∎
      sc : is-commutative-strength s
      sc = ext λ (A , B) →
        -- https://q.uiver.app/#q=WzAsOSxbMSwwLCJNQVxcb3RpbWVzIE1CIl0sWzIsMSwiTU1BXFxvdGltZXMgTUIiXSxbMiwyLCJNKE1BXFxvdGltZXMgQikiXSxbMSw1LCJNKEFcXG90aW1lcyBCKSJdLFswLDEsIk1BXFxvdGltZXMgTU1CIl0sWzAsMiwiTShBXFxvdGltZXMgTUIpIl0sWzEsNCwiTV4yKEFcXG90aW1lcyBCKSJdLFsxLDMsIk0oTUFcXG90aW1lcyBNQikiXSxbMSwyLCJNTUFcXG90aW1lcyBNTUIiXSxbMCwxXSxbMSwyXSxbMCw0XSxbNCw1XSxbNiwzXSxbNSw3XSxbMiw3XSxbNyw2XSxbNCw4XSxbMSw4XSxbOCw3XV0=
        μ _ ∘ M₁ (φ ∘ (id ⊗₁ η _)) ∘ φ ∘ (η _ ⊗₁ id) ≡⟨ refl⟩∘⟨ {!   !} ⟩
        μ _ ∘ M₁ φ ∘ φ ∘ (M₁ id ⊗₁ M₁ (η _)) ∘ (η _ ⊗₁ id) ≡⟨ {!   !} ⟩
        (μ _ ∘ M₁ φ ∘ φ) ∘ (η _ ⊗₁ M₁ (η _)) ≡˘⟨ pulll mult-φ ⟩
        φ ∘ (μ _ ⊗₁ μ _) ∘ (η _ ⊗₁ M₁ (η _)) ≡⟨ {!   !} ⟩
        φ ∘ (μ _ ⊗₁ μ _) ∘ (M₁ (η _) ⊗₁ η _) ≡⟨ pulll mult-φ ⟩
        (μ _ ∘ M₁ φ ∘ φ) ∘ (M₁ (η _) ⊗₁ η _) ≡⟨ {!   !} ⟩
        μ _ ∘ M₁ φ ∘ φ ∘ (M₁ (η _) ⊗₁ M₁ id) ∘ (id ⊗₁ η _) ≡⟨ {!   !} ⟩
        μ _ ∘ M₁ (φ ∘ (η _ ⊗₁ id)) ∘ φ ∘ (id ⊗₁ η _) ∎
  {-
    is .snd .inv (s , sc) = m where
      open Monad-strength s
      open Monoidal-monad-on
      open Lax-monoidal-functor-on
      m : Monoidal-monad-on M-monad
      m .monad-monoidal .ε = η Unit
      m .monad-monoidal .F-mult = left-φ
      m .monad-monoidal .F-α→ =
        -- https://q.uiver.app/#q=WzAsMjUsWzAsMCwiKE1BXFxvdGltZXMgTUIpXFxvdGltZXMgTUMiXSxbNCwwLCJNQVxcb3RpbWVzKE1CXFxvdGltZXMgTUMpIl0sWzAsMSwiTShBXFxvdGltZXMgTUIpXFxvdGltZXMgTUMiXSxbMCwyLCJNXjIoQVxcb3RpbWVzIEIpXFxvdGltZXMgTUMiXSxbMCwzLCJNKEFcXG90aW1lcyBCKVxcb3RpbWVzIE1DIl0sWzAsNCwiTSgoQVxcb3RpbWVzIEIpXFxvdGltZXMgTUMpIl0sWzAsNiwiTV4yKChBXFxvdGltZXMgQilcXG90aW1lcyBDKSJdLFswLDcsIk0oKEFcXG90aW1lcyBCKVxcb3RpbWVzIEMpIl0sWzQsNywiTShBXFxvdGltZXMgKEJcXG90aW1lcyBDKSkiXSxbNCwxLCJNQVxcb3RpbWVzIE0oQlxcb3RpbWVzIE1DKSJdLFs0LDIsIk1BXFxvdGltZXMgTV4yKEJcXG90aW1lcyBDKSJdLFs0LDMsIk1BXFxvdGltZXMgTShCXFxvdGltZXMgQykiXSxbNCw0LCJNKEFcXG90aW1lcyBNKEJcXG90aW1lcyBDKSkiXSxbNCw2LCJNXjIoQVxcb3RpbWVzIChCXFxvdGltZXMgQykpIl0sWzEsMSwiTSgoQVxcb3RpbWVzIE1CKVxcb3RpbWVzIE1DKSJdLFsyLDEsIk0oQVxcb3RpbWVzIChNQlxcb3RpbWVzIE1DKSkiXSxbMiwyLCJNKEFcXG90aW1lcyBNKEJcXG90aW1lcyBNQykpIl0sWzMsMiwiTShBXFxvdGltZXMgTV4yKEJcXG90aW1lcyBDKSkiXSxbMSwyLCJNKE0oQVxcb3RpbWVzIEIpXFxvdGltZXMgTUMpIl0sWzIsMywiTV4yKEFcXG90aW1lcyhCXFxvdGltZXMgTUMpKSJdLFsxLDMsIk1eMigoQVxcb3RpbWVzIEIpXFxvdGltZXMgTUMpIl0sWzIsNCwiTShBXFxvdGltZXMgKEJcXG90aW1lcyBNQykpIl0sWzMsMywiTV4yKEFcXG90aW1lcyBNKEJcXG90aW1lcyBDKSkiXSxbMiw1LCJNKEFcXG90aW1lcyBNKEJcXG90aW1lcyBDKSkiXSxbMyw0LCJNXjMoQVxcb3RpbWVzIChCXFxvdGltZXMgQykpIl0sWzAsMV0sWzAsMl0sWzIsM10sWzMsNF0sWzQsNV0sWzUsNl0sWzYsN10sWzcsOF0sWzEsOV0sWzksMTBdLFsxMCwxMV0sWzExLDEyXSxbMTIsMTNdLFsxMyw4XSxbMiwxNF0sWzEsMTVdLFsxNCwxNV0sWzksMTZdLFsxNSwxNl0sWzEwLDE3XSxbMTYsMTddLFsxNywxMl0sWzE0LDE4XSxbMywxOF0sWzE2LDE5XSxbMTgsMjBdLFsyMCwxOV0sWzIwLDVdLFs1LDIxXSxbMTksMjFdLFs2LDEzXSxbMTksMjJdLFsxNywyMl0sWzIxLDIzXSxbMjMsMTNdLFsyMiwyNF0sWzI0LDEzLCJcXG11IiwyLHsiY3VydmUiOjF9XSxbMjIsMjNdLFsyNCwxMywiTVxcbXUiLDAseyJjdXJ2ZSI6LTF9XV0=
        M₁ (α→ _ _ _) ∘ (μ _ ∘ M₁ σ ∘ τ) ∘ ((μ _ ∘ M₁ σ ∘ τ) ⊗₁ id) ≡⟨ pulll (extendl (sym (mult.is-natural _ _ _))) ⟩
        (μ _ ∘ M₁ (M₁ (α→ _ _ _)) ∘ M₁ σ ∘ τ) ∘ ((μ _ ∘ M₁ σ ∘ τ) ⊗₁ id) ≡⟨ pullr (pullr (pullr refl)) ⟩
        μ _ ∘ M₁ (M₁ (α→ _ _ _)) ∘ M₁ σ ∘ τ ∘ ((μ _ ∘ M₁ σ ∘ τ) ⊗₁ id) ≡⟨ refl⟩∘⟨ M.pulll left-strength-α→ ⟩
        μ _ ∘ M₁ (σ ∘ (id ⊗₁ σ) ∘ α→ _ _ _) ∘ τ ∘ ((μ _ ∘ M₁ σ ∘ τ) ⊗₁ id) ≡⟨ refl⟩∘⟨ refl⟩∘⟨ L.popl right-strength-μ ⟩
        μ _ ∘ M₁ (σ ∘ (id ⊗₁ σ) ∘ α→ _ _ _) ∘ (μ _ ∘ M₁ τ ∘ τ) ∘ ((M₁ σ ∘ τ) ⊗₁ id) ≡⟨ refl⟩∘⟨ refl⟩∘⟨ pullr (pullr (L.popl (τ.is-natural _ _ _))) ⟩
        μ _ ∘ M₁ (σ ∘ (id ⊗₁ σ) ∘ α→ _ _ _) ∘ μ _ ∘ M₁ τ ∘ (M₁ (σ ⊗₁ id) ∘ τ) ∘ (τ ⊗₁ id) ≡⟨ refl⟩∘⟨ M.popr (M.popr (pulll (sym (mult.is-natural _ _ _)))) ⟩
        μ _ ∘ M₁ σ ∘ M₁ (id ⊗₁ σ) ∘ (μ _ ∘ M₁ (M₁ (α→ _ _ _))) ∘ M₁ τ ∘ (M₁ (σ ⊗₁ id) ∘ τ) ∘ (τ ⊗₁ id) ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullr (refl⟩∘⟨ refl⟩∘⟨ pullr refl) ⟩
        μ _ ∘ M₁ σ ∘ M₁ (id ⊗₁ σ) ∘ μ _ ∘ M₁ (M₁ (α→ _ _ _)) ∘ M₁ τ ∘ M₁ (σ ⊗₁ id) ∘ τ ∘ (τ ⊗₁ id) ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ M.pulll3 strength-α→ ⟩
        μ _ ∘ M₁ σ ∘ M₁ (id ⊗₁ σ) ∘ μ _ ∘ M₁ (σ ∘ (id ⊗₁ τ) ∘ α→ _ _ _) ∘ τ ∘ (τ ⊗₁ id) ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ M.popr (M.popr (sym right-strength-α→)) ⟩
        μ _ ∘ M₁ σ ∘ M₁ (id ⊗₁ σ) ∘ μ _ ∘ M₁ σ ∘ M₁ (id ⊗₁ τ) ∘ τ ∘ α→ _ _ _ ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendl (τ.is-natural _ _ _) ⟩
        μ _ ∘ M₁ σ ∘ M₁ (id ⊗₁ σ) ∘ μ _ ∘ M₁ σ ∘ τ ∘ (M₁ id ⊗₁ τ) ∘ α→ _ _ _ ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ extendl (mult.is-natural _ _ _) ⟩
        μ _ ∘ M₁ σ ∘ μ _ ∘ M₁ (M₁ (id ⊗₁ σ)) ∘ M₁ σ ∘ τ ∘ (M₁ id ⊗₁ τ) ∘ α→ _ _ _ ≡˘⟨ refl⟩∘⟨ extendl (mult.is-natural _ _ _) ⟩
        μ _ ∘ μ _ ∘ M₁ (M₁ σ) ∘ M₁ (M₁ (id ⊗₁ σ)) ∘ M₁ σ ∘ τ ∘ (M₁ id ⊗₁ τ) ∘ α→ _ _ _ ≡˘⟨ extendl mult-assoc ⟩
        μ _ ∘ M₁ (μ _) ∘ M₁ (M₁ σ) ∘ M₁ (M₁ (id ⊗₁ σ)) ∘ M₁ σ ∘ τ ∘ (M₁ id ⊗₁ τ) ∘ α→ _ _ _ ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ M.extendl (σ.is-natural _ _ _) ⟩
        μ _ ∘ M₁ (μ _) ∘ M₁ (M₁ σ) ∘ M₁ σ ∘ M₁ (id ⊗₁ M₁ σ) ∘ τ ∘ (M₁ id ⊗₁ τ) ∘ α→ _ _ _ ≡⟨ refl⟩∘⟨ M.pulll3 (sym left-strength-μ) ⟩
        μ _ ∘ M₁ (σ ∘ (id ⊗₁ μ _)) ∘ M₁ (id ⊗₁ M₁ σ) ∘ τ ∘ (M₁ id ⊗₁ τ) ∘ α→ _ _ _ ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ extendl (τ.is-natural _ _ _) ⟩
        μ _ ∘ M₁ (σ ∘ (id ⊗₁ μ _)) ∘ τ ∘ (M₁ id ⊗₁ M₁ σ) ∘ (M₁ id ⊗₁ τ) ∘ α→ _ _ _ ≡⟨ refl⟩∘⟨ M.popr (extendl (sym (τ.is-natural _ _ _))) ⟩
        μ _ ∘ M₁ σ ∘ τ ∘ (M₁ id ⊗₁ μ _) ∘ (M₁ id ⊗₁ M₁ σ) ∘ (M₁ id ⊗₁ τ) ∘ α→ _ _ _ ≡⟨ pushr (pushr (refl⟩∘⟨ {! R.pulll3  !})) ⟩
        (μ _ ∘ M₁ σ ∘ τ) ∘ (⌜ M₁ id ⌝ ⊗₁ (μ _ ∘ M₁ σ ∘ τ)) ∘ α→ _ _ _ ≡⟨ ap! {!   !} ⟩
        (μ _ ∘ M₁ σ ∘ τ) ∘ (id ⊗₁ (μ _ ∘ M₁ σ ∘ τ)) ∘ α→ _ _ _ ∎
      m .monad-monoidal .F-λ← =
        M₁ λ← ∘ (μ _ ∘ M₁ σ ∘ τ) ∘ (η _ ⊗₁ id) ≡⟨ refl⟩∘⟨ pullr (pullr right-strength-η) ⟩
        M₁ λ← ∘ μ _ ∘ M₁ σ ∘ η _ ≡˘⟨ refl⟩∘⟨ refl⟩∘⟨ unit.is-natural _ _ _ ⟩
        M₁ λ← ∘ μ _ ∘ η _ ∘ σ ≡⟨ (refl⟩∘⟨ cancell right-ident) ⟩
        M₁ λ← ∘ σ ≡⟨ left-strength-λ← ⟩
        λ← ∎
      m .monad-monoidal .F-ρ← =
        M₁ ρ← ∘ (μ _ ∘ M₁ σ ∘ τ) ∘ (⌜ id ⌝ ⊗₁ η _) ≡⟨ ap! (sym M-id) ⟩
        M₁ ρ← ∘ (μ _ ∘ M₁ σ ∘ τ) ∘ (M₁ id ⊗₁ η _) ≡⟨ refl⟩∘⟨ pullr (pullr (τ.is-natural _ _ _)) ⟩
        M₁ ρ← ∘ μ _ ∘ M₁ σ ∘ M₁ (id ⊗₁ η _) ∘ τ ≡⟨ refl⟩∘⟨ refl⟩∘⟨ M.pulll left-strength-η ⟩
        M₁ ρ← ∘ μ _ ∘ M₁ (η _) ∘ τ ≡⟨ refl⟩∘⟨ cancell left-ident ⟩
        M₁ ρ← ∘ τ ≡⟨ right-strength-ρ← ⟩
        ρ← ∎
      m .unit-ε = refl
      m .unit-φ =
        -- https://q.uiver.app/#q=WzAsNixbMSwwLCJBXFxvdGltZXMgQiJdLFswLDIsIk1BXFxvdGltZXMgTUIiXSxbMSwyLCJNKEFcXG90aW1lcyBNQikiXSxbMiwyLCJNwrIoQVxcb3RpbWVzIEIpIl0sWzIsMSwiTShBXFxvdGltZXMgQikiXSxbMSwxLCJBXFxvdGltZXMgTUIiXSxbMCwxXSxbMSwyXSxbMiwzXSxbMyw0LCIiLDAseyJjdXJ2ZSI6MX1dLFswLDRdLFswLDVdLFs1LDJdLFs1LDRdLFs0LDMsIiIsMSx7ImN1cnZlIjoxfV1d
        (μ _ ∘ M₁ σ ∘ τ) ∘ (η _ ⊗₁ η _) ≡⟨ {!   !} ⟩
        μ _ ∘ M₁ σ ∘ τ ∘ (η _ ⊗₁ id) ∘ (id ⊗₁ η _) ≡⟨ refl⟩∘⟨ refl⟩∘⟨ pulll right-strength-η ⟩
        μ _ ∘ M₁ σ ∘ η _ ∘ (id ⊗₁ η _) ≡˘⟨ refl⟩∘⟨ extendl (unit.is-natural _ _ _) ⟩
        μ _ ∘ η _ ∘ σ ∘ (id ⊗₁ η _) ≡⟨ cancell right-ident ⟩
        σ ∘ (id ⊗₁ η _) ≡⟨ left-strength-η ⟩
        η _ ∎
      m .mult-φ =
        -- https://q.uiver.app/#q=WzAsMTgsWzAsMCwiTU1BXFxvdGltZXMgTU1CIl0sWzMsMCwiTUFcXG90aW1lcyBNQiJdLFswLDEsIk0oTUFcXG90aW1lcyBNTUIpIl0sWzAsMiwiTV4yKE1BXFxvdGltZXMgTUIpIl0sWzAsMywiTShNQVxcb3RpbWVzIE1CKSJdLFswLDQsIk1eMihBXFxvdGltZXMgTUIpIl0sWzAsNSwiTV4zKEFcXG90aW1lcyBCKSJdLFszLDYsIk0oQVxcb3RpbWVzIEIpIl0sWzMsNCwiTShBXFxvdGltZXMgTUIpIl0sWzMsNSwiTV4yKEFcXG90aW1lcyBCKSJdLFsxLDMsIk1eMyhBXFxvdGltZXMgTUIpIl0sWzEsMiwiTV4yKEFcXG90aW1lcyBNTUIpIl0sWzEsNCwiTV40KEFcXG90aW1lcyBCKSJdLFsyLDMsIk1eMihBXFxvdGltZXMgTUIpIl0sWzIsNCwiTV4zKEFcXG90aW1lcyBCKSJdLFswLDYsIk1eMihBXFxvdGltZXMgQikiXSxbMiwyLCJNKEFcXG90aW1lcyBNTUIpIl0sWzEsMSwiTUFcXG90aW1lcyBNTUIiXSxbMCwxLCJcXG11XFxvdGltZXMgXFxtdSJdLFswLDIsIlxcdGF1IiwyXSxbMiwzLCJNXFxzaWdtYSIsMl0sWzMsNCwiXFxtdSIsMl0sWzQsNSwiTVxcdGF1IiwyXSxbNSw2LCJNXjJcXHNpZ21hIiwyXSxbMSw4LCJcXHRhdSJdLFs4LDksIk1cXHNpZ21hIl0sWzksNywiXFxtdSJdLFszLDEwLCJNXjJcXHRhdSIsMl0sWzEwLDUsIlxcbXUiLDJdLFsyLDExLCJNXFx0YXUiLDJdLFsxMSwxMCwiTV4yXFxzaWdtYSIsMl0sWzEwLDEyLCJNXjNcXHNpZ21hIiwyXSxbMTIsNiwiXFxtdSIsMl0sWzExLDEzLCJNXjIoQVxcb3RpbWVzIFxcbXUpIiwxXSxbMTIsMTQsIk1eMlxcbXUiLDJdLFsxMywxNCwiTV4yXFxzaWdtYSIsMl0sWzE0LDksIlxcbXUiLDJdLFs2LDE1LCJNXFxtdSIsMl0sWzE1LDcsIlxcbXUiLDJdLFsxMyw4LCJcXG11IiwyXSxbMTEsMTYsIlxcbXUiLDJdLFsxNiw4LCJNKEFcXG90aW1lcyBcXG11KSJdLFswLDE3LCJcXG11XFxvdGltZXMgTUIiXSxbMTcsMTYsIlxcdGF1Il0sWzE3LDEsIk1BXFxvdGltZXMgXFxtdSIsMl1d
        (μ _ ∘ M₁ σ ∘ τ) ∘ (μ _ ⊗₁ μ _) ≡⟨ {!   !} ⟩
        (μ _ ∘ M₁ σ ∘ τ) ∘ (id ⊗₁ μ _) ∘ (μ _ ⊗₁ id) ≡⟨ {!   !} ⟩
        μ _ ∘ M₁ σ ∘ M₁ (id ⊗₁ μ _) ∘ τ ∘ (μ _ ⊗₁ id) ≡⟨ {!   !} ⟩
        μ _ ∘ M₁ σ ∘ M₁ (id ⊗₁ μ _) ∘ μ _ ∘ M₁ τ ∘ τ ≡⟨ {!   !} ⟩
        μ _ ∘ M₁ σ ∘ μ _ ∘ M₁ (M₁ (id ⊗₁ μ _)) ∘ M₁ τ ∘ τ ≡⟨ {!   !} ⟩
        μ _ ∘ μ _ ∘ M₁ (M₁ σ) ∘ M₁ (M₁ (id ⊗₁ μ _)) ∘ M₁ τ ∘ τ ≡⟨ {!   !} ⟩
        μ _ ∘ μ _ ∘ M₁ (M₁ (μ _)) ∘ M₁ (M₁ (M₁ σ)) ∘ M₁ (M₁ σ) ∘ M₁ τ ∘ τ ≡⟨ {!   !} ⟩
        μ _ ∘ M₁ (μ _) ∘ μ _ ∘ M₁ (M₁ (M₁ σ)) ∘ M₁ (M₁ σ) ∘ M₁ τ ∘ τ ≡⟨ {!   !} ⟩
        μ _ ∘ M₁ (μ _) ∘ M₁ (M₁ σ) ∘ μ _ ∘ M₁ (M₁ σ) ∘ M₁ τ ∘ τ ≡⟨ {! sc  !} ⟩
        μ _ ∘ M₁ (μ _) ∘ M₁ (M₁ σ) ∘ μ _ ∘ M₁ (M₁ τ) ∘ M₁ σ ∘ τ ≡⟨ {!   !} ⟩
        μ _ ∘ M₁ (μ _) ∘ M₁ (M₁ σ) ∘ M₁ τ ∘ μ _ ∘ M₁ σ ∘ τ ≡⟨ {!   !} ⟩
        μ _ ∘ M₁ (μ _ ∘ M₁ σ ∘ τ) ∘ μ _ ∘ M₁ σ ∘ τ ∎
    is .snd .rinv (s , sc) = Σ-prop-path {!   !} {!  Strength-path pσ pτ !} where
      open Monad-strength s
      pσ : left-strength ≡ is .fst (is .snd .inv (s , sc)) .fst .Monad-strength.left-strength
      pσ = ext λ (A , B) →
        -- https://q.uiver.app/#q=WzAsNSxbMCwwLCJBXFxvdGltZXMgTUIiXSxbMCwyLCJNKEFcXG90aW1lcyBCKSJdLFsxLDAsIk1BXFxvdGltZXMgTUIiXSxbMSwxLCJNKEFcXG90aW1lcyBNQikiXSxbMSwyLCJNXjIoQVxcb3RpbWVzIEIpIl0sWzAsMV0sWzAsMl0sWzIsM10sWzMsNF0sWzQsMSwiIiwyLHsiY3VydmUiOjF9XSxbMCwzXSxbMSw0LCIiLDEseyJjdXJ2ZSI6MX1dXQ==
        σ ≡⟨ insertl right-ident ⟩
        μ _ ∘ η _ ∘ σ ≡⟨ refl⟩∘⟨ unit.is-natural _ _ _ ⟩
        μ _ ∘ M₁ σ ∘ η _ ≡˘⟨ pullr (pullr right-strength-η) ⟩
        (μ _ ∘ M₁ σ ∘ τ) ∘ (η _ ⊗₁ id) ∎
      pτ : right-strength ≡ is .fst (is .snd .inv (s , sc)) .fst .Monad-strength.right-strength
      pτ = ext λ (A , B) →
        -- https://q.uiver.app/#q=WzAsNSxbMCwwLCJNQVxcb3RpbWVzIEIiXSxbMSwwLCJNQVxcb3RpbWVzIE1CIl0sWzAsMiwiTShBXFxvdGltZXMgQikiXSxbMSwxLCJNKEFcXG90aW1lcyBNQikiXSxbMSwyLCJNXjIoQVxcb3RpbWVzIEIpIl0sWzAsMV0sWzAsMl0sWzEsM10sWzMsNF0sWzQsMiwiIiwwLHsiY3VydmUiOi0xfV0sWzIsM10sWzIsNCwiIiwwLHsiY3VydmUiOi0xfV1d
        τ ≡⟨ insertl left-ident ⟩
        μ _ ∘ M₁ (η _) ∘ τ ≡˘⟨ refl⟩∘⟨ M.pulll left-strength-η ⟩
        μ _ ∘ M₁ σ ∘ M₁ (id ⊗₁ η _) ∘ τ ≡˘⟨ pullr (pullr (τ.is-natural _ _ _)) ⟩
        (μ _ ∘ M₁ σ ∘ τ) ∘ (⌜ M₁ id ⌝ ⊗₁ η _) ≡⟨ ap! M-id ⟩
        (μ _ ∘ M₁ σ ∘ τ) ∘ (id ⊗₁ η _) ∎
    is .snd .linv m = {! Monoidal-monad-path (Monoidal-functor-path pε pmult)  !} where
      open Monoidal-monad-on m
      pε : ε ≡ is .snd .inv (is .fst m) .Monoidal-monad-on.ε
      pε = unit-ε
      pmult : F-mult ≡ is .snd .inv (is .fst m) .Monoidal-monad-on.F-mult
      pmult = ext λ (A , B) →
        -- https://ncatlab.org/nlab/show/monoidal+monad#from_monoidal_to_commutative_strong_monads
        φ ≡⟨ {!   !} ⟩
        φ ∘ (μ _ ⊗₁ μ _) ∘ (M₁ (η _) ⊗₁ M₁ id) ∘ (id ⊗₁ η _) ≡⟨ pulll mult-φ ⟩
        (μ _ ∘ M₁ φ ∘ φ) ∘ (M₁ (η _) ⊗₁ M₁ id) ∘ (id ⊗₁ η _) ≡⟨ pullr (pullr (extendl (φ.is-natural _ _ _))) ⟩
        μ _ ∘ M₁ φ ∘ M₁ (η _ ⊗₁ id) ∘ φ ∘ (id ⊗₁ η _) ≡⟨ refl⟩∘⟨ M.pulll refl ⟩
        μ _ ∘ M₁ (φ ∘ (η _ ⊗₁ id)) ∘ φ ∘ (id ⊗₁ η _) ∎

  module _ (C-diagonal : Diagonals C-monoidal) (idem : is-idempotent-monad) where
    open Diagonals C-diagonal

    idempotent-monad→diagonal
      : ∀ s
      → is-diagonal-functor
        _ _ C-diagonal C-diagonal
        (_ , Equiv.from monoidal≃commutative (s , idempotent→commutative idem s) .Monoidal-monad-on.monad-monoidal)
    idempotent-monad→diagonal s =
      -- https://q.uiver.app/#q=WzAsMTAsWzMsMCwiVEFcXHRpbWVzIFRBIl0sWzQsMCwiVChBXFx0aW1lcyBUQSkiXSxbMSw1LCJUXjIoQSBcXHRpbWVzIEEpIl0sWzAsNCwiVChBXFx0aW1lcyBBKSJdLFswLDAsIlRBIl0sWzEsMSwiVFRBIl0sWzIsMiwiVChUQVxcdGltZXMgVEEpIl0sWzMsMiwiVF4yKEFcXHRpbWVzIFRBKSJdLFsyLDQsIlQoQVxcdGltZXMgVEEpIl0sWzQsNCwiVChBIFxcdGltZXMgVEEpIl0sWzIsMywiXFxtdSIsMCx7ImN1cnZlIjotMX1dLFs0LDMsIlRcXGRlbHRhIiwyXSxbNCw1LCJUXFxldGEiLDIseyJjdXJ2ZSI6MX1dLFs1LDYsIlRcXGRlbHRhIl0sWzYsNywiVHQiXSxbMCw2LCJcXGV0YSJdLFszLDIsIlRcXGV0YSIsMCx7ImxhYmVsX3Bvc2l0aW9uIjo4MCwiY3VydmUiOi0xfV0sWzMsNiwiVChcXGV0YVxcdGltZXNcXGV0YSkiXSxbMyw4LCJUKEFcXHRpbWVzIFxcZXRhKSJdLFs4LDYsIlQoXFxldGFcXHRpbWVzIFRBKSJdLFs4LDcsIlxcZXRhIiwyXSxbMCwxLCJ0Il0sWzQsMCwiXFxkZWx0YSJdLFs0LDUsIlxcZXRhIiwwLHsiY3VydmUiOi0xfV0sWzgsMiwiVHMiXSxbMSw3LCJcXGV0YSJdLFs3LDksIlxcbXUiXSxbMSw5LCIiLDEseyJsZXZlbCI6Miwic3R5bGUiOnsiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dLFs5LDgsIiIsMSx7ImxldmVsIjoyLCJzdHlsZSI6eyJoZWFkIjp7Im5hbWUiOiJub25lIn19fV1d
      (μ _ ∘ M₁ σ ∘ τ) ∘ δ ≡⟨ pullr (pullr (insertl right-ident)) ⟩
      μ _ ∘ M₁ σ ∘ μ _ ∘ η _ ∘ τ ∘ δ ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ unit.is-natural _ _ _ ⟩
      μ _ ∘ M₁ σ ∘ μ _ ∘ M₁ (τ ∘ δ) ∘ η _ ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ idempotent-monad→η≡Mη idem _ ⟩
      μ _ ∘ M₁ σ ∘ μ _ ∘ M₁ (τ ∘ δ) ∘ M₁ (η _) ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ M.pushl refl ⟩
      μ _ ∘ M₁ σ ∘ μ _ ∘ M₁ τ ∘ M₁ δ ∘ M₁ (η _) ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ M.weave (δ.is-natural _ _ _) ⟩
      μ _ ∘ M₁ σ ∘ μ _ ∘ M₁ τ ∘ M₁ (η _ ⊗₁ η _) ∘ M₁ δ ≡⟨ {!   !} ⟩
      μ _ ∘ M₁ σ ∘ μ _ ∘ M₁ τ ∘ M₁ (η _ ⊗₁ id) ∘ M₁ (id ⊗₁ η _) ∘ M₁ δ ≡⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ M.pulll right-strength-η ⟩
      μ _ ∘ M₁ σ ∘ μ _ ∘ M₁ (η _) ∘ M₁ (id ⊗₁ η _) ∘ M₁ δ ≡⟨ refl⟩∘⟨ refl⟩∘⟨ cancell left-ident ⟩
      μ _ ∘ M₁ σ ∘ M₁ (id ⊗₁ η _) ∘ M₁ δ ≡⟨ refl⟩∘⟨ M.pulll left-strength-η ⟩
      μ _ ∘ M₁ (η _) ∘ M₁ δ ≡⟨ cancell left-ident ⟩
      M₁ δ ∎
      where open Monad-strength s

  module _ (C-symmetric : Symmetric-monoidal C-monoidal) where
    open Symmetric-monoidal C-symmetric

    is-symmetric-monad-strength : Monad-strength → Type (o ⊔ ℓ)
    is-symmetric-monad-strength s = ∀ {A B} → τ {A} {B} ∘ β→ ≡ M₁ β→ ∘ σ
      where open Monad-strength s

    is-symmetric-monoidal-monad : Monoidal-monad-on M-monad → Type (o ⊔ ℓ)
    is-symmetric-monoidal-monad m = is-symmetric-functor _ _ C-symmetric C-symmetric (_ , m .Monoidal-monad-on.monad-monoidal)

    module _ (m : Monoidal-monad-on M-monad) where
      open Monoidal-monad-on m

      symmetric-monoidal→symmetric-strength
        : is-symmetric-monoidal-monad m → is-symmetric-monad-strength (monoidal≃commutative .fst m .fst)
      symmetric-monoidal→symmetric-strength sy =
        (φ ∘ (id ⊗₁ η _)) ∘ β→ ≡⟨ pullr (sym (β→.is-natural _ _ _)) ⟩
        φ ∘ β→ ∘ (η _ ⊗₁ id) ≡⟨ extendl sy ⟩
        M₁ β→ ∘ φ ∘ (η _ ⊗₁ id) ∎

    module _ (s : Monad-strength) (sc : Monad-strength.is-commutative-strength s) where
      open Monad-strength s

      symmetric-strength→symmetric-monoidal
        : is-symmetric-monad-strength s → is-symmetric-monoidal-monad (Equiv.from monoidal≃commutative (s , sc))
      symmetric-strength→symmetric-monoidal sy =
        -- Monads on Symmetric Monoidal Closed Categories, 3.3
        (μ _ ∘ M₁ σ ∘ τ) ∘ β→ ≡⟨ pullr (pullr sy) ⟩
        μ _ ∘ M₁ σ ∘ M₁ β→ ∘ σ ≡˘⟨ refl⟩∘⟨ M.extendl (swizzle sy has-is-symmetric (M.annihilate has-is-symmetric)) ⟩
        μ _ ∘ M₁ (M₁ β→) ∘ M₁ τ ∘ σ ≡⟨ extendl (mult.is-natural _ _ _) ⟩
        M₁ β→ ∘ μ _ ∘ M₁ τ ∘ σ ≡⟨ refl⟩∘⟨ sc ηₚ _ ⟩
        M₁ β→ ∘ μ _ ∘ M₁ σ ∘ τ ∎
-}

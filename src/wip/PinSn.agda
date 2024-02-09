open import 1Lab.Prelude

open import Algebra.Group.Homotopy

open import Data.Set.Truncation

open import Homotopy.Space.Sphere
open import Homotopy.Space.Suspension
open import Homotopy.Truncation
open import Homotopy.Base

module wip.PinSn where

n-Tr-map : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} n → (A → B) → n-Tr A (suc n) → n-Tr B (suc n)
n-Tr-map n f = n-Tr-rec hlevel! (λ a → inc (f a))

n-Tr∙ : ∀ {ℓ} (A : Type∙ ℓ) n → Type∙ ℓ
n-Tr∙ (A , a) n = n-Tr A n , inc a

2-Tr≃∥∥₀ : ∀ {ℓ} {A : Type ℓ} → n-Tr A 2 ≃ ∥ A ∥₀
2-Tr≃∥∥₀ = Iso→Equiv ((n-Tr-rec (hlevel 2) inc) , iso (∥-∥₀-rec (n-Tr-is-hlevel 1) inc) (∥-∥₀-elim hlevel! λ _ → refl) (n-Tr-elim _ hlevel! λ _ → refl))

Ωⁿ-defn' : ∀ {ℓ} (A : Type∙ ℓ) n → Ωⁿ (suc n) A ≡ Ωⁿ n (Ω∙ A)
Ωⁿ-defn' A zero = refl
Ωⁿ-defn' A (suc n) = ap Ω∙ (Ωⁿ-defn' A n)

Ω-Tr : ∀ {ℓ} (A : Type∙ ℓ) n → ⌞ Ω∙ (n-Tr∙ A (2 + n)) ⌟ ≃ ⌞ n-Tr∙ (Ω∙ A) (suc n) ⌟
Ω-Tr (A , a) n = n-Tr-path-equiv
-- Ω-Tr≡ : ∀ {ℓ} (A : Type∙ ℓ) n → Ω∙ (n-Tr∙ A (2 + n)) ≡ n-Tr∙ (Ω∙ A) (suc n)
-- Ω-Tr≡ (A , a) n = Σ-pathp (ua n-Tr-path-equiv) (to-pathp λ i → {! inc (transp (λ _ → a ≡ a)  !})

Ωⁿ-Tr : ∀ {ℓ} (A : Type∙ ℓ) n {m} → ⌞ Ωⁿ n (n-Tr∙ A (n + suc m)) ⌟ ≃ ⌞ n-Tr∙ (Ωⁿ n A) (suc m) ⌟
Ωⁿ-Tr A zero = id≃
-- Ωⁿ-Tr A (suc n) = {!   !} ∙e Ωⁿ-Tr (Ω∙ A) n ∙e {! Ωⁿ-defn' ? (suc n)  !}
Ωⁿ-Tr A (suc n) {m} = {!? ∙e Ωⁿ-Tr _ n   !} ∙e Ω-Tr (Ωⁿ n A) m

main : ∀ n → ⌞ n-Tr∙ (Sⁿ (suc n)) (3 + n) ⌟ ≃ ⌞ n-Tr∙ (Ω∙ (Sⁿ (2 + n))) (3 + n) ⌟
main n = decode' , {!   !} where
  promote : Sⁿ (suc n) →∙ Ω∙ (Sⁿ (2 + n))
  promote = Σ-map∙≃map∙-Ω .fst id∙
  decode' : ⌞ n-Tr∙ (Sⁿ (suc n)) (3 + n) ⌟ → ⌞ n-Tr∙ (Ω∙ (Sⁿ (2 + n))) (3 + n) ⌟
  decode' = n-Tr-map (2 + n) (promote .fst)
  Codes : ⌞ Sⁿ (2 + n) ⌟ → Type
  Codes N = ⌞ n-Tr∙ (Sⁿ (suc n)) (3 + n) ⌟
  Codes S = {!   !}
  Codes (merid x i) = {!   !}
  encode' : ⌞ n-Tr∙ (Ω∙ (Sⁿ (2 + n))) (3 + n) ⌟ → ⌞ n-Tr∙ (Sⁿ (suc n)) (3 + n) ⌟
  encode' = n-Tr-rec hlevel! λ p → subst Codes p (inc N)

Ωⁿ⁺¹Sⁿ⁺¹ : ∀ n → ∥ ⌞ Ωⁿ (2 + n) (Sⁿ (2 + n)) ⌟ ∥₀ ≃ ∥ ⌞ Ωⁿ (suc n) (Sⁿ (suc n)) ⌟ ∥₀
Ωⁿ⁺¹Sⁿ⁺¹ n =
  ∥ ⌞ Ωⁿ (2 + n) (Sⁿ (2 + n)) ⌟ ∥₀ ≃⟨ path→equiv (ap (λ x → ∥ x .fst ∥₀) (Ωⁿ-defn' _ (suc n))) ⟩
  ∥ ⌞ Ωⁿ (suc n) (Ω∙ (Sⁿ (2 + n))) ⌟ ∥₀ ≃⟨ 2-Tr≃∥∥₀ e⁻¹ ⟩
  n-Tr ⌞ Ωⁿ (suc n) (Ω∙ (Sⁿ (2 + n))) ⌟ 2 ≃⟨ Ωⁿ-Tr _ (suc n) e⁻¹ ⟩
  ⌞ Ωⁿ (suc n) (n-Tr∙ (Ω∙ (Sⁿ (2 + n))) (suc n + 2)) ⌟ ≃⟨ {! main lemma !} ⟩
  ⌞ Ωⁿ (suc n) (n-Tr∙ (Sⁿ (suc n)) (suc n + 2)) ⌟ ≃⟨ Ωⁿ-Tr _ (suc n) ⟩
  n-Tr ⌞ Ωⁿ (suc n) (Sⁿ (suc n)) ⌟ 2 ≃⟨ 2-Tr≃∥∥₀ ⟩
  ∥ ⌞ Ωⁿ (suc n) (Sⁿ (suc n)) ⌟ ∥₀ ≃∎

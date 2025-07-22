<!--
```agda
open import Algebra.Group.Instances.Integers
open import Algebra.Group.Cat.Base
open import Algebra.Group.Concrete
open import Algebra.Group.Homotopy

open import Cat.Functor.Base
open import Cat.Prelude

open import Data.Nat.Properties
open import Data.Set.Truncation
open import Data.Nat.Order
open import Data.Int.Base
open import Data.Nat.Base

open import Homotopy.Space.Suspension.Freudenthal
open import Homotopy.Space.Suspension.Properties
open import Homotopy.Space.Circle.Properties
open import Homotopy.Space.Suspension
open import Homotopy.Space.Circle
open import Homotopy.Space.Sphere
open import Homotopy.Conjugation
open import Homotopy.Truncation
open import Homotopy.Loopspace
open import Homotopy.HSpace

import Cat.Reasoning

import Homotopy.Space.Suspension.Pi2
```
-->

```agda
module Homotopy.Space.Sphere.Properties where
```

# Properties of higher spheres

We can put together what we know about [$\pi_2$ of a suspension] and
about the [[fundamental group]] $\pi_1(S^1)$ of the [[circle]] to show
that $\pi_2(S^2) \cong \bZ$.

[$\pi_2$ of a suspension]: Homotopy.Space.Suspension.Pi2.html

```agda
open Homotopy.Space.Suspension.Pi2 S¹-concrete HSpace-S¹

opaque
  π₂S²≅ℤ : πₙ₊₁ 1 (Sⁿ 2) Groups.≅ ℤ
  π₂S²≅ℤ = π₁S¹≅ℤ
    Groups.∘Iso π₂ΣG≅ΩG
    Groups.∘Iso πₙ₊₁-ap 1 (Susp-ap SuspS⁰≃∙S¹)

open import Homotopy.Base

-- TODO define this via suspend∙ instead?
suspend-loop∙ : ∀ {ℓ} k (A : Type∙ ℓ) → Ωⁿ k A →∙ Ωⁿ (suc k) (Σ¹ A)
suspend-loop∙ k A = Equiv∙.to∙ (Ωⁿ≃∙Sⁿ-map (suc k)) ∘∙ Susp-Maps∙ ∘∙ Equiv∙.from∙ (Ωⁿ≃∙Sⁿ-map k)

suspend-loop∙-natural
  : ∀ {ℓa ℓb} k (A : Type∙ ℓa) (B : Type∙ ℓb) (f : A →∙ B)
  → Ωⁿ-map (suc k) (Susp-map∙ f) ∘∙ suspend-loop∙ k A
  ≡ suspend-loop∙ k B ∘∙ Ωⁿ-map k f
suspend-loop∙-natural k A B f = homogeneous-funext∙ λ l →
  Ωⁿ-map (suc k) (Susp-map∙ f) .fst (Ωⁿ≃∙Sⁿ-map (suc k) · Susp-map∙ (Equiv.from (Ωⁿ≃Sⁿ-map k) l))
    ≡⟨ Ωⁿ≃Sⁿ-map-natural (suc k) _ _ ⟩
  (Ωⁿ≃∙Sⁿ-map (suc k) · (Susp-map∙ f ∘∙ Susp-map∙ (Equiv.from (Ωⁿ≃Sⁿ-map k) l)))
    ≡˘⟨ ap (Ωⁿ≃Sⁿ-map (suc k) .fst) (Susp-map∙-∘ f (Equiv.from (Ωⁿ≃Sⁿ-map k) l)) ⟩
  (Ωⁿ≃∙Sⁿ-map (suc k) · (Susp-map∙ (f ∘∙ Equiv.from (Ωⁿ≃Sⁿ-map k) l)))
    ≡⟨ ap (Ωⁿ≃Sⁿ-map (suc k) .fst ⊙ Susp-map∙) (Ωⁿ≃Sⁿ-map-inv-natural k f l) ⟩
  Ωⁿ≃∙Sⁿ-map (suc k) · Susp-map∙ (Equiv.from (Ωⁿ≃Sⁿ-map k) (Ωⁿ-map k f .fst l)) ∎

suspend-loop : ∀ {ℓ} k (A : Type∙ ℓ) → ⌞ Ωⁿ k A ⌟ → ⌞ Ωⁿ (suc k) (Σ¹ A) ⌟
suspend-loop k A l = suspend-loop∙ k A · l
```

The inverse to this equivalence, turning integers into 2-loops on the
sphere, is constructed purely abstractly and thus too horrible to
compute with. However, the *forward* map, giving the winding numbers of
2-loops, is more tractable. We can write down an explicit generator for
$\pi_2(S^2)$ and assert that the equivalence above takes it to the
number $1$ by computation.

```agda
private opaque
  unfolding conj conj-refl π₂S²≅ℤ n-Tr-Ω¹ ΩΣG≃G Ω¹-ap

  gen : Path (Path ⌞ Sⁿ 2 ⌟ north north) refl refl
  gen i j = hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) → merid (suspend (Sⁿ 0) south (~ j)) i
    k (i = i0) → north
    k (i = i1) → merid north (~ k)
    k (j = i0) → merid north (~ k ∧ i)
    k (j = i1) → merid north (~ k ∧ i)

  π₂S²≅ℤ-computes : Groups.to π₂S²≅ℤ · inc gen ≡ 1
  π₂S²≅ℤ-computes = refl
```

<!--
```agda
  {-
  Checking Homotopy.Space.Sphere.Properties (…).
  Total                                            6,655ms
  Homotopy.Space.Sphere.Properties.π₂S²≅ℤ-computes 1,073ms
  -}
```
-->

## Stability for spheres

The [[Freudenthal suspension theorem]] implies that, if $k \le 2(n - 1)$
the $k$-truncation of $\Omega S^{2+n}$ agrees with that of $S^{1 + n}$.

```agda
opaque
  Sⁿ-stability-worker
    : ∀ n k (p : suc k ≤ (suc n + suc n))
    → n-Tr∙ (Sⁿ (1 + n)) (suc k) ≃∙ n-Tr∙ (Ωⁿ 1 (Sⁿ (2 + n))) (suc k)
  Sⁿ-stability-worker n k p =
    n-Tr∙ (Sⁿ (1 + n)) (suc k)
      ≃∙˘⟨ n-Tr-Tr (≤-peel p) , refl ⟩
    n-Tr∙ (n-Tr∙ (Sⁿ (1 + n)) (suc n + suc n)) (suc k)
      ≃∙⟨ (let e , p = freudenthal-equivalence {A∙ = Sⁿ (suc n)} n (Sⁿ⁻¹-is-connected (2 + n)) in n-Tr-ap {n = k} e , ap n-Tr.inc p) ⟩
    n-Tr∙ (n-Tr∙ (Ωⁿ 1 (Σ¹ (Sⁿ (1 + n)))) (suc n + suc n)) (suc k)
      ≃∙⟨⟩
    n-Tr∙ (n-Tr∙ (Ωⁿ 1 (Sⁿ (2 + n))) (suc n + suc n)) (suc k)
      ≃∙⟨ n-Tr-Tr (≤-peel p) , refl ⟩
    n-Tr∙ (Ωⁿ 1 (Sⁿ (2 + n))) (suc k)
      ≃∙∎

  Sⁿ-stability-worker-inc
    : ∀ n k (p : suc k ≤ (suc n + suc n))
    → Equiv∙.to∙ (Sⁿ-stability-worker n k p) ∘∙ inc∙ ≡ inc∙ ∘∙ suspend∙ (Sⁿ (1 + n))
  Sⁿ-stability-worker-inc n k p = homogeneous-funext∙ λ _ → refl
```

As a corollary, $\pi_n(S^n) \simeq \bZ$.

```agda
opaque
  unfolding Ωⁿ≃∙Sⁿ-map

  lemma4
    : ∀ {ℓ} (A : Type∙ ℓ) k (l : ⌞ Ωⁿ k A ⌟)
    → Equiv.from (Ωⁿ-suc (Σ¹ A) k .fst) (Ωⁿ-map k (suspend∙ A) .fst l)
    ≡ suspend-loop k A l
  lemma4 A k l =
    Equiv.from (Ωⁿ-suc (Σ¹ A) k .fst) ⌜ Ωⁿ-map k (suspend∙ A) .fst l ⌝
      ≡⟨ ap (Equiv.from (Ωⁿ-suc _ k .fst) ⊙ Ωⁿ-map k (suspend∙ _) .fst) (sym (Equiv.ε (Ωⁿ≃Sⁿ-map k) l)) ⟩
    Equiv.from (Ωⁿ-suc (Σ¹ A) k .fst) ⌜ Ωⁿ-map k (suspend∙ A) .fst (Equiv.to (Ωⁿ≃Sⁿ-map k) (Equiv.from (Ωⁿ≃Sⁿ-map k) l)) ⌝
      ≡⟨ ap (Equiv.from (Ωⁿ-suc _ k .fst)) (Ωⁿ≃Sⁿ-map-natural k (suspend∙ _) (Equiv.from (Ωⁿ≃Sⁿ-map k) l)) ⟩
    Equiv.from (Ωⁿ-suc _ k .fst) (Equiv.to (Ωⁿ≃Sⁿ-map k) (suspend∙ _ ∘∙ Equiv.from (Ωⁿ≃Sⁿ-map k) l))
      ≡˘⟨ ap (Equiv.from (Ωⁿ-suc (Σ¹ A) k .fst) ⊙ Equiv.to (Ωⁿ≃Sⁿ-map k)) (Equiv.ε Σ-map∙≃map∙-Ω (suspend∙ _ ∘∙ Equiv.from (Ωⁿ≃Sⁿ-map k) l)) ⟩
    Equiv.to (Ωⁿ≃Sⁿ-map (1 + k)) (Equiv.from Σ-map∙≃map∙-Ω (suspend∙ A ∘∙ Equiv.from (Ωⁿ≃Sⁿ-map k) l))
      ≡⟨ ap (Equiv.to (Ωⁿ≃Sⁿ-map (1 + k))) (suspend∙-is-unit (Equiv.from (Ωⁿ≃Sⁿ-map k) l)) ⟩
    Equiv.to (Ωⁿ≃Sⁿ-map _) (Susp-map∙ (Equiv.from (Ωⁿ≃Sⁿ-map k) l))
      ∎

suspend-loop-agrees
  : ∀ {ℓ} {A : Type∙ ℓ} (l : ⌞ Ωⁿ 1 A ⌟)
  → suspend-loop 1 A l
  ≡ Ω¹-map (suspend∙ A) .fst l
suspend-loop-agrees {A = A} l = sym (lemma4 A 1 l) ∙ transport-refl _

module Sⁿ-stability n k (p : suc k ≤ n + n) where

  abstract
    p' : suc (k + 2) ≤ suc n + suc n
    p' = s≤s (≤-trans (≤-refl' (+-commutative k 2)) (≤-trans (s≤s p) (≤-refl' (+-commutative (suc n) n))))
  e1 = πₙ-def (Sⁿ (2 + n)) (1 + k)
  e2 = Ωⁿ-suc (n-Tr∙ (Sⁿ (2 + n)) (2 + k + 2)) (1 + k)
  e3 = n-Tr-Ω¹ (Sⁿ (2 + n)) (k + 2)
  e4 = Sⁿ-stability-worker n (k + 2) p'
  e5 = πₙ-def (Sⁿ (1 + n)) k
  opaque
    Sⁿ-stability
      : ⌞ πₙ₊₁ (1 + k) (Sⁿ (2 + n)) ⌟ ≃ ⌞ πₙ₊₁ k (Sⁿ (1 + n)) ⌟
    Sⁿ-stability =
      ⌞ πₙ₊₁ (1 + k) (Sⁿ (2 + n)) ⌟
        ≃⟨ e1 .fst ⟩
      ⌞ Ωⁿ (2 + k) (n-Tr∙ (Sⁿ (2 + n)) (2 + k + 2)) ⌟
        ≃⟨ e2 .fst ⟩
      ⌞ Ωⁿ (1 + k) (Ωⁿ 1 (n-Tr∙ (Sⁿ (2 + n)) (2 + k + 2))) ⌟
        ≃˘⟨ Ωⁿ-ap (1 + k) e3 .fst ⟩
      ⌞ Ωⁿ (1 + k) (n-Tr∙ (Ωⁿ 1 (Sⁿ (2 + n))) (1 + k + 2)) ⌟
        ≃˘⟨ Ωⁿ-ap (1 + k) e4 .fst ⟩
      ⌞ Ωⁿ (1 + k) (n-Tr∙ (Sⁿ (1 + n)) (1 + k + 2)) ⌟
        ≃˘⟨ e5 .fst ⟩
      ⌞ πₙ₊₁ k (Sⁿ (1 + n)) ⌟
        ≃∎

    trace
      : (l : ⌞ Ωⁿ (1 + k) (Sⁿ (1 + n)) ⌟)
      → (⌞ πₙ₊₁ k (Sⁿ (1 + n)) ⌟ , inc l) ≃∙ (⌞ πₙ₊₁ (1 + k) (Sⁿ (2 + n)) ⌟ , inc (suspend-loop (suc k) (Sⁿ (suc n)) l))
    trace l =
      ⌞ πₙ₊₁ k (Sⁿ (1 + n)) ⌟ , inc l
          ≃∙⟨ e5 .fst , πₙ-def-inc _ k l ⟩
      ⌞ Ωⁿ (1 + k) (n-Tr∙ (Sⁿ (1 + n)) (1 + k + 2)) ⌟ , Ωⁿ-map (1 + k) inc∙ .fst l
          ≃∙⟨ Ωⁿ-ap (1 + k) e4 .fst , (Ωⁿ-map-∘ (1 + k) (Equiv∙.to∙ e4) inc∙ ·ₚ l) ∙ ap (λ x → Ωⁿ-map (1 + k) x .fst l) (Sⁿ-stability-worker-inc n (k + 2) p') ⟩
      ⌞ Ωⁿ (1 + k) (n-Tr∙ (Ωⁿ 1 (Sⁿ (2 + n))) (1 + k + 2)) ⌟ , Ωⁿ-map (1 + k) (inc∙ ∘∙ suspend∙ _) .fst l
          ≃∙⟨ Ωⁿ-ap (1 + k) e3 .fst , (Ωⁿ-map-∘ (1 + k) (Equiv∙.to∙ (n-Tr-Ω¹ _ (k + 2))) _ ·ₚ l) ⟩
      ⌞ Ωⁿ (1 + k) (Ωⁿ 1 (n-Tr∙ (Sⁿ (2 + n)) (2 + k + 2))) ⌟ , Ωⁿ-map (1 + k) (Equiv∙.to∙ (n-Tr-Ω¹ _ (k + 2)) ∘∙ inc∙ ∘∙ suspend∙ _) .fst l
          ≃∙⟨ id≃ , ap (λ x → Ωⁿ-map (1 + k) x .fst l) (sym (∘∙-assoc (Equiv∙.to∙ (n-Tr-Ω¹ _ (k + 2))) inc∙ (suspend∙ _))) ⟩
      ⌞ Ωⁿ (1 + k) (Ωⁿ 1 (n-Tr∙ (Sⁿ (2 + n)) (2 + k + 2))) ⌟ , Ωⁿ-map (1 + k) ((Equiv∙.to∙ (n-Tr-Ω¹ _ (k + 2)) ∘∙ inc∙) ∘∙ suspend∙ _) .fst l
          ≃∙⟨ id≃ , ap (λ x → Ωⁿ-map (1 + k) (x ∘∙ suspend∙ _) .fst l) (n-Tr-Ω¹-inc _ (k + 2)) ⟩
        ⌞ Ωⁿ (1 + k) (Ωⁿ 1 (n-Tr∙ (Sⁿ (2 + n)) (2 + k + 2))) ⌟
      , Ωⁿ-map (1 + k) (Ω¹-map inc∙ ∘∙ suspend∙ _) .fst l
          ≃∙˘⟨ id≃ , (Ωⁿ-map-∘ (1 + k) _ _ ·ₚ l) ⟩
        ⌞ Ωⁿ (1 + k) (Ωⁿ 1 (n-Tr∙ (Sⁿ (2 + n)) (2 + k + 2))) ⌟
      , Ωⁿ-map (1 + k) (Ω¹-map inc∙) .fst (Ωⁿ-map (1 + k) (suspend∙ _) .fst l)
          ≃∙˘⟨ Ωⁿ-suc (n-Tr∙ (Sⁿ (2 + n)) (2 + k + 2)) (1 + k) .fst , Ω-suc-natural (1 + k) inc∙ ·ₚ (Ωⁿ-map (1 + k) (suspend∙ _) .fst l) ⟩
        ⌞ Ωⁿ (2 + k) (n-Tr∙ (Sⁿ (2 + n)) (2 + k + 2)) ⌟
      , Ωⁿ-map (2 + k) inc∙ .fst (Equiv.from (Ωⁿ-suc _ (1 + k) .fst) (Ωⁿ-map (1 + k) (suspend∙ _) .fst l))
          ≃∙⟨ id≃ , ap (Ωⁿ-map (2 + k) inc∙ .fst) (lemma4 (Sⁿ (1 + n)) (1 + k) l) ⟩
        ⌞ Ωⁿ (2 + k) (n-Tr∙ (Sⁿ (2 + n)) (2 + k + 2)) ⌟
      , Ωⁿ-map (2 + k) inc∙ .fst (suspend-loop (suc k) (Sⁿ (suc n)) l)
          ≃∙˘⟨ πₙ-def (Sⁿ (2 + n)) (1 + k) .fst
             , πₙ-def-inc _ (suc k) (suspend-loop (suc k) (Sⁿ (suc n)) l) ⟩
        ⌞ πₙ₊₁ (1 + k) (Sⁿ (2 + n)) ⌟
      , inc (suspend-loop (suc k) (Sⁿ (suc n)) l)
          ≃∙∎

    Sⁿ-stability-inc
      : Equiv.from Sⁿ-stability ⊙ inc
      ≡ inc ⊙ suspend-loop (suc k) (Sⁿ (suc n))
    Sⁿ-stability-inc = ext λ l → trace l .snd

open Sⁿ-stability using (Sⁿ-stability; Sⁿ-stability-inc) public

πₙSⁿ≃Int : ∀ n → ⌞ πₙ₊₁ n (Sⁿ (suc n)) ⌟ ≃ ⌞ ℤ ⌟
πₙSⁿ≃Int 0 =
  ∥ ⌞ Ω¹ (Sⁿ 1) ⌟ ∥₀      ≃⟨ ∥-∥₀-ap (Ωⁿ-ap 1 SuspS⁰≃∙S¹ .fst) ⟩
  ∥ ⌞ Ω¹ (S¹ , base) ⌟ ∥₀ ≃⟨ Equiv.inverse (_ , ∥-∥₀-idempotent (hlevel 2)) ⟩
  ⌞ Ω¹ (S¹ , base) ⌟      ≃⟨ ΩS¹≃Int ⟩
  Int                     ≃∎

πₙSⁿ≃Int 1 = Iso→Equiv (i.to , iso i.from (happly i.invl) (happly i.invr)) where
  module i = Cat.Reasoning._≅_ (Sets lzero) (F-map-iso (Forget-structure _) π₂S²≅ℤ)

πₙSⁿ≃Int (suc (suc n)) =
  ⌞ πₙ₊₁ (2 + n) (Sⁿ (3 + n)) ⌟
    ≃⟨ Sⁿ-stability (1 + n) (1 + n) (s≤s (+-≤r n (1 + n))) ⟩
  ⌞ πₙ₊₁ (1 + n) (Sⁿ (2 + n)) ⌟
    ≃⟨ πₙSⁿ≃Int (suc n) ⟩
  ⌞ ℤ ⌟
    ≃∎

degree∙ : ∀ n → (Sⁿ (suc n) →∙ Sⁿ (suc n)) → Int
degree∙ n f = πₙSⁿ≃Int n .fst (inc (Ωⁿ≃Sⁿ-map (suc n) .fst f))

opaque
  unfolding π₂S²≅ℤ

  compatible
    : ∀ n (l : ⌞ Ωⁿ (suc n) (Sⁿ (suc n)) ⌟)
    → πₙSⁿ≃Int (suc n) .fst (inc (suspend-loop (suc n) (Sⁿ (suc n)) l))
    ≡ πₙSⁿ≃Int n .fst (inc l)
  compatible zero l =
    ΩS¹≃Int .fst (Ω²ΣG≃ΩG .fst (inc (Ωⁿ-map 2 (Susp-map∙ {A∙ = Sⁿ 1} SuspS⁰→∙S¹) .fst (suspend-loop 1 (Sⁿ 1) l))))
      ≡⟨ ap (ΩS¹≃Int .fst ⊙ Ω²ΣG≃ΩG .fst ⊙ inc) (suspend-loop∙-natural 1 _ _ SuspS⁰→∙S¹ ·ₚ l) ⟩
    ΩS¹≃Int .fst (Ω²ΣG≃ΩG .fst (inc (suspend-loop 1 _ (Ω¹-map SuspS⁰→∙S¹ · l))))
      ≡⟨ ap (ΩS¹≃Int .fst ⊙ Ω²ΣG≃ΩG .fst ⊙ inc) (suspend-loop-agrees _) ⟩
    ΩS¹≃Int .fst (Ω²ΣG≃ΩG .fst (inc (Ω¹-map (suspend∙ _) .fst (Ω¹-map SuspS⁰→∙S¹ · l))))
      ≡˘⟨ ap (ΩS¹≃Int .fst ⊙ Ω²ΣG≃ΩG .fst) (Ω²ΣG≃ΩG-inv (Ω¹-map SuspS⁰→∙S¹ · l)) ⟩
    ΩS¹≃Int .fst (Ω²ΣG≃ΩG .fst (Equiv.from Ω²ΣG≃ΩG (Ω¹-map SuspS⁰→∙S¹ · l)))
      ≡⟨ ap (ΩS¹≃Int .fst) (Equiv.ε Ω²ΣG≃ΩG _) ⟩
    ΩS¹≃Int .fst (Ω¹-map SuspS⁰→∙S¹ · l)
      ∎
  compatible (suc n) l =
    πₙSⁿ≃Int (2 + n) .fst (inc (suspend-loop (2 + n) (Sⁿ (2 + n)) l)) ≡⟨⟩
    πₙSⁿ≃Int (1 + n) .fst (Sⁿ-stability (1 + n) (1 + n) _ .fst (inc (suspend-loop (2 + n) (Sⁿ (2 + n)) l)))
      ≡˘⟨ ap (πₙSⁿ≃Int (1 + n) .fst ⊙ Sⁿ-stability (1 + n) (1 + n) _ .fst) (Sⁿ-stability-inc (1 + n) (1 + n) _ $ₚ l) ⟩
    πₙSⁿ≃Int (1 + n) .fst (Sⁿ-stability (1 + n) (1 + n) _ .fst (Equiv.from (Sⁿ-stability (1 + n) (1 + n) _) (inc l)))
      ≡⟨ ap (πₙSⁿ≃Int (1 + n) .fst) (Equiv.ε (Sⁿ-stability (1 + n) (1 + n) _) (inc l)) ⟩
    πₙSⁿ≃Int (1 + n) .fst (inc l) ∎

degree∙-compatible
  : ∀ n (l : Sⁿ (suc n) →∙ Sⁿ (suc n))
  → degree∙ (suc n) (Susp-map∙ l) ≡ degree∙ n l
degree∙-compatible n l =
  degree∙ (suc n) (Susp-map∙ l) ≡˘⟨ ap (degree∙ (suc n) ⊙ Susp-map∙) (Equiv.η (Ωⁿ≃Sⁿ-map (1 + n)) l) ⟩
  πₙSⁿ≃Int (suc n) · (inc (suspend-loop (suc n) (Sⁿ (suc n)) (Ωⁿ≃Sⁿ-map (suc n) · l))) ≡⟨ compatible n _ ⟩
  degree∙ n l ∎
```

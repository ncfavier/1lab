open import 1Lab.Prelude
open import 1Lab.Reflection
open import 1Lab.Reflection.Subst

module 1Lab.Reflection.Unbind where

private
  -- de Bruijn index → type → drop?
  Predicate = Nat → Arg Term → Bool

  -- Given a predicate on types and a context Γ, yields (Δ , σ) such that
  --   Δ ⊢ σ : Γ
  -- where Δ is the largest subtelescope of Γ with all the types satisfying the predicate removed.
  -- Example:
  -- drop-tele isI (A : I → Type, B : A → Type, i : I, a : A i, b : B a)
  --   = (A : I → Type, B : A → Type) , strengthen 3 ids
  drop-tele : Predicate → Telescope → Telescope × Subst
  drop-tele p = go 0 where
    go : Nat → Telescope → Telescope × Subst
    go n ((na , arg ai t) ∷ ts) with go (suc n) ts
    … | ts' , s with p n (arg ai t) | subst-tm s t
    …   | false | just t' = (na , arg ai t') ∷ ts' , liftS 1 s
    …   | _     | _       = ts' , strengthenS 1 s
    go _ [] = [] , ids

  -- Selects the n-th variable.
  _th : Nat → Predicate
  _th n i _ = i == n

  -- Selects all interval variables.
  isI : Predicate
  isI _ (arg _ (def (quote I) _)) = true
  isI _ _ = false

-- Drops selected variables from the given hole's context by pruning.
-- This can result in more constraints being in the pattern fragment, hence solvable.
-- Example:
--   _0 (a = a) (i = i0) =? a : A
--   unbind isI _0
--   _1 (a = a) =? a : A
--   _1 := a
--   _0 := _1
unbind : Predicate → Term → TC ⊤
unbind p hole = do
  ctx' , s ← drop-tele p <$> getContext
  just hole' ← subst-tm (invertS s) <$> inTopContext ctx' (new-meta unknown)
    where _ → typeError [] -- weakening a meta can't fail
  unify hole hole'

macro
  -- Unbinds the given variable.
  _#_ : Term → ∀ {ℓ} {A : Type ℓ} → A → Term → TC ⊤
  _#_ (var i []) a hole = do
    -- Quoting is done manually to work around https://github.com/agda/agda/issues/5738#issuecomment-1013295556
    quoteTC a >>= unify hole
    unbind (i th) hole
  _#_ i a hole = typeError [ "cannot unbind non-variable term " , termErr i ]

  -- Unbinds all interval variables.
  I#_ : ∀ {ℓ} {A : Type ℓ} → A → Term → TC ⊤
  I#_ a hole = do
    quoteTC a >>= unify hole
    unbind isI hole

infixr -1 _#_ I#_

-- Test cases
private
  refl' : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
  refl' x i = I# _

  prop→prop : ∀ {ℓ} {A : Type ℓ} → is-prop A → is-prop A
  prop→prop p x y i = p (I# _) (i # _) i

  prop→prop' : ∀ {ℓ} {A : Type ℓ} → is-prop A → (x y : A)
             → (i : I) → A [ i ∨ ~ i ↦ (λ { (i = i0) → x; (i = i1) → y }) ]
  prop→prop' p x y i = inS (p (I# _) (I# y) i)

  open import Data.Set.Truncation renaming (inc to ∣_∣₀)

  ∥-∥₀-rec-∘ : ∀ {ℓ} {A B C : Type ℓ} (f : A → B) (g : B → C)
    → ∥-∥₀-rec squash (∣_∣₀ ∘ g) ∘ ∥-∥₀-rec squash (∣_∣₀ ∘ f) ≡ ∥-∥₀-rec squash (∣_∣₀ ∘ g ∘ f)
  ∥-∥₀-rec-∘ f g i ∣ x ∣₀ = I# _
  ∥-∥₀-rec-∘ f g i (squash a b p q j k) = is-set→squarep
    {A = λ i j → ∥-∥₀-rec-∘ f g i a ≡ ∥-∥₀-rec-∘ f g i b}
    (λ i j → is-hlevel-suc 2 squash _ _)
    (I# λ i k → ∥-∥₀-rec-∘ (k # _) (I# _) i (p k)) (i # j # k # _) (I# _) (I# _)
    i j k

```agda
open import 1Lab.Type.Sigma
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Prim.HCompU where
```

# Primitive: Composition for universes

This module binds the operations `prim^glueU`{.Agda} and
`prim^unglueU`{.Agda}, which expose the fibrancy structure of the
universe as being a `Glue`{.Agda}-like type former. Additionally, we
prove `extend-transp-fibre`{.Agda}, which is used internally for
composition in the universe.

```agda
primitive
  prim^glueU
    : {ℓ : Level} {φ : I} {T : I → Partial φ (Type ℓ)}
      {A : Type ℓ [ φ ↦ T i0 ]}
    → PartialP φ (T i1) → outS A → hcomp T (outS A)

  prim^unglueU
    : {ℓ : Level} {φ : I} {T : I → Partial φ (Type ℓ)}
      {A : Type ℓ [ φ ↦ T i0 ]}
    → hcomp T (outS A) → outS A

  -- Needed for transp.
  primFaceForall : (I → I) → I

extend-transp-fibre
  : ∀ {l} (e : I → Type l) (φ : I)
    (a : Partial φ (e i0))
    (b : e i1 [ φ ↦ (λ o → transp e i0 (a o)) ])
  → fibre (transp e i0) (outS b)
extend-transp-fibre e φ a b = _ , λ j →
  comp e
    (λ where
      i (φ = i1) → coe0→i e i (a 1=1)
      i (j = i0) → coe0→i e i (g i1)
      i (j = i1) → g (~ i))
    (g i1)
  where
    g : ∀ i → e (~ i)
    g k = fill (λ i → e (~ i))
      (λ where
        i (φ = i1) → coe0→i e (~ i) (a 1=1)
        i (φ = i0) → coe1→i e (~ i) (outS b))
      (inS (outS b))
      k

{-# BUILTIN TRANSPPROOF extend-transp-fibre #-}
```
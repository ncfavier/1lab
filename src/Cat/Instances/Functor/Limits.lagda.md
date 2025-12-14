<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Cat.Functor.Adjoint.Continuous
open import Cat.Instances.Functor.Duality
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Equivalence
open import Cat.Diagram.Limit.Base
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Coherence
open import Cat.Instances.Functor
open import Cat.Functor.Constant
open import Cat.Functor.Closed
open import Cat.Diagram.Duals
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.Functor.Limits where
```

# Limits in functor categories

Let $\cC$ be a category admitting $\cD$-shaped limits. Then the
functor category $[\cE,\cS]$, for $\cE$ _any_ category, also
admits $\cD$-shaped limits. In particular, if $\cC$ is
$(\iota,\kappa)$-complete, then so is $[\cE,\cC]$.

```agda
module _
  {o₁ ℓ₁} {C : Precategory o₁ ℓ₁}
  {o₂ ℓ₂} {D : Precategory o₂ ℓ₂}
  {o₃ ℓ₃} {E : Precategory o₃ ℓ₃}
  (F : Functor D Cat[ E , C ])
  where
```

<!--
```agda
  open Functor
  open _=>_

  import Cat.Reasoning C as C
  import Cat.Reasoning D as D
  import Cat.Reasoning E as E

  private
    module F = Functor F
```
-->

Let $F : \cD \to [\cE,\cC]$ be a diagram, and suppose $\cC$
admits limits of $\cD$-shaped diagrams; We wish to compute the limit
$\lim F$. First, observe that we can `Uncurry`{.Agda} $F$ to obtain a
functor $F' : \cD \times \cE \to \cC$; By fixing the value of
the $\cE$ coordinate (say, to $x$), we obtain a family $F(-, x)$ of
$\cD$-shaped diagrams in $\cC$, which, by assumption, all have
limits.

```agda
  open import Cat.Functor.Kan.Base
  open import Cat.Functor.Kan.Pointwise
  open import Cat.Instances.Product
  open import Cat.Instances.Shape.Terminal
  is-pointwise-limit
    : (limF : Functor E C) (cone : Const limF => F)
    → Type _
  -- is-pointwise-limit limF cone = ∀ e → preserves-is-limit (Eval e) F limF cone
  is-pointwise-limit limF cone = ∀ e → becomes-ran !F F (!Const limF) cone (Eval e)

  is-pointwise-colimit
    : (limF : Functor E C) (cocone : F => Const limF)
    → Type _
  is-pointwise-colimit limF cocone = ∀ e → becomes-lan !F F (!Const limF) cocone (Eval e)

  -- TODO does the fact that evaluation functors jointly create limits follow from an analogous fact about kan extensions + (pointwise) limit ≃ (pointwise) ran along projection?

  is-limit→is-pointwise-limit
    : (limF : Functor E C) (cone : Const limF => F)
    -- → C has pointwise limits of F
    → is-limit F limF cone
    → is-pointwise-limit limF cone
  is-limit→is-pointwise-limit limF cone lim e = {!   !}

  is-pointwise-limit→is-limit
    : (limF : Functor E C) (cone : Const limF => F)
    → is-pointwise-limit limF cone
    → is-limit F limF cone
  is-pointwise-limit→is-limit limF cone lims = generalize-limitp (to-is-limit ml) refl where
    open make-is-limit
    module lims e = is-limit (lims e)

    ml : make-is-limit F limF
    ml .ψ = cone .η
    ml .commutes f = ext λ j → sym (cone .is-natural _ _ f ηₚ j) ∙ C.idr _
    ml .universal eps p .η e = lims.universal e (λ j → eps j .η e) λ f → p f ηₚ e
    ml .universal eps p .is-natural x y f =
      lims.unique₂ y _
      (λ g → C.pulll (p g ηₚ y))
      (λ j → C.pulll (lims.factors _ _ _))
      (λ j → C.pulll (cone .η j .is-natural x y f)
           ∙ C.pullr (lims.factors _ _ _)
           ∙ sym (eps j .is-natural x y f))
    ml .factors eps p = ext λ j → lims.factors j _ _
    ml .unique eps p other q = ext λ e → lims.unique _ _ _ _ λ j → q j ηₚ e

  module _ (colimF : Functor E C) (cocone : F => Const colimF) where
    uncurry-eta : Uncurry F => colimF F∘ Snd
    uncurry-eta .η = uncurry-nt cocone .η
    uncurry-eta .is-natural x y f = uncurry-nt cocone .is-natural x y f ∙ (C.eliml refl C.⟩∘⟨refl)

    -- pointwise-lan→pointwise-colimit
    --   : is-pointwise-lan uncurry-eta
    --   → is-pointwise-colimit colimF cocone
    -- pointwise-lan→pointwise-colimit pointwise e =
    --   {! pointwise-lan→has-comma-colimits   !}

    -- pointwise-colimit→pointwise-lan
    --   : is-pointwise-colimit colimF cocone
    --   → is-pointwise-lan uncurry-eta
    -- pointwise-colimit→pointwise-lan pointwise =
    --   {!    !}

  module _ (limF : Functor E C) (cone : Const limF => F) where
    uncurry-eps : limF F∘ Snd => Uncurry F
    uncurry-eps .η = uncurry-nt cone .η
    uncurry-eps .is-natural x y f = C.intro-inner refl ∙ uncurry-nt cone .is-natural x y f
    -- uncurry-ran : is-ran Snd (Uncurry F) limF uncurry-eps
    -- uncurry-ran = {!   !}

    -- TODO do this (and the converse) via representability?
    is-limit→uncurry-ran
      : is-limit F limF cone
      → is-ran Snd (Uncurry F) limF uncurry-eps
    is-limit→uncurry-ran lim = {!   !}
    -- is-limit→uncurry-ran lim = done where
    --   coh-cone : ∀ {M} → M F∘ Snd => Uncurry F → !Const M F∘ !F => F
    --   coh-cone eps = ununcurry-nt (eps ∘nt NT (λ _ → C.id) (λ x y f → C.idl _ ∙ C.id-comm-sym))
    --   done : is-ran Snd (Uncurry F) limF uncurry-eps
    --   done .is-ran.σ {M = M} eps = lim .is-ran.σ (coh-cone eps) .η _
    --   done .is-ran.σ-comm {β = β} = ext λ (d , e) → lim .is-ran.σ-comm {β = coh-cone β} ηₚ d ηₚ e ∙ C.idr _
    --   done .is-ran.σ-uniq {β = β} {σ'} com = ext λ e → lim .is-ran.σ-uniq {β = coh-cone β} {σ' = !constⁿ σ'} (ext λ d e → C.idr _ ∙ com ηₚ (d , e)) ηₚ _ ηₚ e

    -- http://www.tac.mta.ca/tac/reprints/articles/10/tr10.pdf page 64

    pointwise-ran→pointwise-limit
      : is-pointwise-ran uncurry-eps
      → is-pointwise-limit limF cone
    pointwise-ran→pointwise-limit pointwise e =
      {! pointwise-ran→has-comma-limits' pointwise e   !}

    -- pointwise-limit→pointwise-ran
    --   : is-pointwise-limit limF cone
    --   → is-pointwise-ran uncurry-eps
    -- pointwise-limit→pointwise-ran pointwise =
    --   {!    !}

  module _ (has-D-lims : (F : Functor D C) → Limit F) where
    module D-lim x = Limit (has-D-lims (Eval x F∘ F))
```

Let us call the limit of $F(-, x)$ --- taken in $\cC$ ---
`lim-for`{.Agda}, and similarly the unique, "terminating" cone
homomorphism $K \to \lim F(-, x)$ will be called `!-for`{.Agda}.

```agda
    private
      !-for : ∀ {x y} (f : E.Hom x y) → C.Hom (D-lim.apex x) (D-lim.apex y)
      !-for {x} {y} f =
        D-lim.universal y
          (λ j → F.₀ j .F₁ f C.∘ D-lim.ψ x j)
          (λ g →
            C.extendl (F.₁ g .is-natural x y f)
            ∙ (C.refl⟩∘⟨ D-lim.commutes x g))

    functor-apex : Functor E C
    functor-apex .F₀ x = D-lim.apex x
    functor-apex .F₁ {x} {y} f = !-for f
    functor-apex .F-id =
      sym $ D-lim.unique _ _ _ _ λ j →
        C.elimr refl ∙ C.introl (F.₀ j .F-id)
    functor-apex .F-∘ f g =
      sym $ D-lim.unique _ _ _ _ λ j →
        C.pulll (D-lim.factors _ _ _)
        ∙ C.pullr (D-lim.factors _ _ _)
        ∙ C.pulll (sym (F.₀ j .F-∘ _ _))

    functor-cone : Const functor-apex => F
    functor-cone .η j .η e = D-lim.ψ e j
    functor-cone .η j .is-natural x y f = D-lim.factors _ _ _
    functor-cone .is-natural x y f = ext λ j →
      C.elimr refl ∙ sym (D-lim.commutes _ _)

    functor-is-limit : is-limit F functor-apex functor-cone
    functor-is-limit = is-pointwise-limit→is-limit functor-apex functor-cone λ e →
      generalize-limitp (D-lim.has-limit e) refl

    functor-limit : Limit F
    functor-limit = to-limit functor-is-limit
```

As a corollary, if $\cD$ is an $(o,\ell)$-complete category, then so
is $[\cC,\cD]$.

```agda
Functor-cat-is-complete :
  ∀ {o ℓ} {o₁ ℓ₁} {C : Precategory o₁ ℓ₁} {o₂ ℓ₂} {D : Precategory o₂ ℓ₂}
  → is-complete o ℓ D → is-complete o ℓ Cat[ C , D ]
Functor-cat-is-complete D-complete F = functor-limit F D-complete
```

<!--
```agda
module _
  {o₁ ℓ₁} {C : Precategory o₁ ℓ₁}
  {o₂ ℓ₂} {D : Precategory o₂ ℓ₂}
  {o₃ ℓ₃} {E : Precategory o₃ ℓ₃}
  (has-D-colims : ∀ (F : Functor D C) → Colimit F)
  (F : Functor D Cat[ E , C ])
  where

  functor-colimit : Colimit F
  functor-colimit = colim where
    F' : Functor (D ^op) Cat[ E ^op , C ^op ]
    F' = op-functor→ F∘ Functor.op F

    F'-lim : Limit F'
    F'-lim = functor-limit F'
      (λ f → subst Limit (Functor-path (λ _ → refl) (λ _ → refl))
        (Colimit→Co-limit (has-D-colims (unopF f))))

    LF'' : Limit (op-functor← F∘ (op-functor→ F∘ Functor.op F))
    LF'' = right-adjoint-limit (is-equivalence.F⊣F⁻¹ op-functor-is-equiv) F'-lim

    LFop : Limit (Functor.op F)
    LFop = subst Limit (F∘-assoc ∙ ap (_F∘ Functor.op F) op-functor←→ ∙ F∘-idl) LF''

    colim : Colimit F
    colim = Co-limit→Colimit LFop

Functor-cat-is-cocomplete :
  ∀ {o ℓ} {o₁ ℓ₁} {C : Precategory o₁ ℓ₁} {o₂ ℓ₂} {D : Precategory o₂ ℓ₂}
  → is-cocomplete o ℓ D → is-cocomplete o ℓ Cat[ C , D ]
Functor-cat-is-cocomplete D-cocomplete = functor-colimit D-cocomplete
```
-->

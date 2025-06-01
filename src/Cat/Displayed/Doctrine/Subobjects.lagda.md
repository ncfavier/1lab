<!--
```agda
open import Cat.Displayed.Instances.Subobjects
open import Cat.Diagram.Product
open import Cat.Displayed.Cocartesian.Weak
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Doctrine
open import Cat.Regular.Image
open import Cat.Prelude
open import Cat.Regular

import Cat.Displayed.Instances.Subobjects.Reasoning

open Regular-hyperdoctrine
```
-->

```agda
module Cat.Displayed.Doctrine.Subobjects where
```

```agda
module _ {o ℓ} {C : Precategory o ℓ} (reg : is-regular C) (cat : is-category C) where
  open is-regular reg
  module S = Cat.Displayed.Instances.Subobjects.Reasoning lex.pullbacks
  opf = (Subobject-opfibration C image[_] lex.pullbacks)
  open Cocartesian-fibration S.Subobjects opf

  Sub-regular : Regular-hyperdoctrine C (o ⊔ ℓ) ℓ
  Sub-regular .ℙ = Subobjects C
  Sub-regular .ℙ-fix = _
  Sub-regular .ℙ-coh = _
  Sub-regular .has-is-thin _ _ = {! hlevel 1  !}
  Sub-regular .has-univalence x = Sub-is-category C cat
  Sub-regular .fibrewise-meet = Sub-products C lex.pullbacks
  Sub-regular .fibrewise-top x = Sub-terminal C
  Sub-regular .cartesian = with-pullbacks.Subobject-fibration C lex.pullbacks
  Sub-regular .cocartesian = opf
  Sub-regular .subst-& f m n = Sub-is-category C cat .to-path S.^*-∩ₘ
  Sub-regular .subst-aye f = Sub-is-category C cat .to-path S.^*-⊤ₘ

  -- these are in Jacobs
  Sub-regular .frobenius f = Sub-is-category C cat .to-path (Sub-antisym C
    {!   !}
    {!   !})
  Sub-regular .beck-chevalley pb = Sub-is-category C cat .to-path (Sub-antisym C
    {!   !}
    {!   !})
```

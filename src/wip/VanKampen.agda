{-# OPTIONS --lossy-unification #-}
open import Cat.Displayed.Cartesian.Indexing
open import Cat.Displayed.Instances.Identity
open import Cat.Displayed.Instances.Pullback
open import Cat.Diagram.Pullback.Properties
open import Cat.Displayed.Instances.Slice
open import Cat.Displayed.Cartesian.Weak
open import Cat.Instances.Functor.Limits
open import Cat.Functor.FullSubcategory
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Conservative
open import Cat.Displayed.Cartesian
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.Equivalence
open import Cat.Functor.Naturality
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Functor.Kan.Base
open import Cat.Functor.Pullback
open import Cat.Displayed.Fibre
open import Cat.Functor.Adjoint
open import Cat.Instances.Slice
open import Cat.Displayed.Base
open import Cat.Functor.Final
open import Cat.Functor.Base
open import Cat.Prelude

open import wip.SliceColimits

import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Displayed.Solver as Ds
import Cat.Reasoning
import Cat.Morphism

module wip.VanKampen where

{-
module _ {o ℓ o' ℓ'}
  {B : Precategory o ℓ}
  (E : Displayed B o' ℓ')
  where

  Cartesian-section : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  Cartesian-section = Vertical-fibred-functor (IdD B) E

  Cartesian-sections : Precategory (o ⊔ ℓ ⊔ o' ⊔ ℓ') (o ⊔ ℓ ⊔ ℓ')
  Cartesian-sections = Vertical-fibred-functors {ℰ = IdD B} {E}

module _ {o ℓ o' ℓ' o'' ℓ''}
  {B : Precategory o ℓ}
  {C : Precategory o'' ℓ''} (F : Functor C B)
  (E : Displayed B o' ℓ')
  where

  open Functor
  open Vertical-functor
  open Vertical-fibred-functor
  open _=>↓_
  open Precategory B
  module B = Cat.Reasoning B
  open Displayed E
  open Cat.Displayed.Reasoning E
  open Cat.Displayed.Morphism E
  open is-cartesian

  rebase' : ∀ {x y x' y' x'' y''} → (f : Hom x y)
           → {f' : Hom[ f ] x' y'} {f'' : Hom[ f ] x'' y''}
           → is-cartesian E f f'
           → is-cartesian E f f''
           → Hom[ id ] y' y''
           → Hom[ id ] x' x''
  rebase' f {f' = f'} c' c'' vert = universal' c'' B.id-comm (vert ∘' f')

  cart[] : ∀ {a b f g} {p : f ≡ g} {a' : Ob[ a ]} {b' : Ob[ b ]} {f' : Hom[ f ] a' b'}
    → is-cartesian E f f' → is-cartesian E g (hom[ p ] f')
  cart[] {p = p} {a'} {b'} {f'} c = transport (λ i → is-cartesian E (p i) (transp (λ j → Hom[ p (i ∧ j) ] a' b') (~ i) f')) c

  ≅↓→≅ : ∀ {x} {x' y' : Ob[ x ]} → x' ≅↓ y' → Cat.Morphism.Isomorphism (Fibre E x) x' y'
  ≅↓→≅ i .Cat.Morphism.to = i .to'
  ≅↓→≅ i .Cat.Morphism.from = i .from'
  ≅↓→≅ i .Cat.Morphism.inverses .Cat.Morphism.Inverses.invl = from-pathp (i .invl')
  ≅↓→≅ i .Cat.Morphism.inverses .Cat.Morphism.Inverses.invr = from-pathp (i .invr')

  lemma : ∀ {x} {y} {x'} {y'} f f' → is-cartesian E {F .F₀ x} {F .F₀ y} {x'} {y'} (F .F₁ f) f' → is-cartesian (Change-of-base F E) f f'
  lemma f f' c .universal m h' = c .universal (F .F₁ m) (hom[ F .F-∘ f m ] h')
  lemma f f' c .commutes m h' =
    hom[ F .F-∘ f m ]⁻ (f' ∘' c .universal (F .F₁ m) (hom[ F .F-∘ f m ] h')) ≡⟨ ap hom[ F .F-∘ f m ]⁻ (c .commutes _ _) ⟩
    hom[ F .F-∘ f m ]⁻ (hom[ F .F-∘ f m ] h')                                 ≡⟨ Ds.disp! E ⟩
    h'                                                                  ∎
  lemma f f' c .unique {m = m} {h' = h'} m' p =
   c .unique m' $
        f' ∘' m'                                    ≡⟨ Ds.disp! E ⟩
        hom[ F .F-∘ f m ] (hom[ F .F-∘ f m ]⁻ (f' ∘' m')) ≡⟨ ap hom[ F .F-∘ f m ] p ⟩
        hom[ F .F-∘ f m ] h' ∎

  -- FALSE
  -- lemma' : ∀ {x} {y} {x'} {y'} f f' → is-cartesian (Change-of-base F E) f f' → is-cartesian E {F .F₀ x} {F .F₀ y} {x'} {y'} (F .F₁ f) f'
  -- lemma' f f' c .universal m h = {! c .universal   !}
  -- lemma' f f' c .commutes = {!   !}
  -- lemma' f f' c .unique = {!   !}

  open is-weak-cartesian
  lemma'' : ∀ {x} {y} {x'} {y'} f f' → is-weak-cartesian (Change-of-base F E) f f' → is-weak-cartesian E {F .F₀ x} {F .F₀ y} {x'} {y'} (F .F₁ f) f'
  lemma'' f f' c .universal h = hom[ F .F-id ] (c .universal h)
  lemma'' f f' c .commutes h = cast[] $
    (f' ∘' hom[] (c .universal h)) ≡[]⟨ unwrapr _ ⟩
    (f' ∘' (c .universal h)) ≡[]⟨ wrap _ ⟩
    hom[] (f' ∘' (c .universal h)) ≡[]⟨ c .commutes h ⟩
    h ∎
  lemma'' f f' c .unique h com = shiftr _ (to-pathp (c .unique (hom[ F .F-id ]⁻ h) (cast[] (unwrap _ ∙[] unwrapr _ ∙[] com))))
-}

  {-
  restr : Functor (Cartesian-sections E) (Cartesian-sections (Change-of-base F E))
  restr .F₀ F' .vert .F₀' = F' .vert .F₀'
  restr .F₀ F' .vert .F₁' = F' .vert .F₁'
  restr .F₀ F' .vert .F-id' = {! F' .vert .F-id'  !}
  restr .F₀ F' .vert .F-∘' = {!   !}
  restr .F₀ F' .F-cartesian _ c = lemma _ _ (F' .F-cartesian _ (idd-is-cartesian B))
  restr .F₁ α' .η' _ = hom[ F .F-id ]⁻ (α' .η' _)
  restr .F₁ α' .is-natural' x' y' f' = {! α' .is-natural' x' y' f'  !}
  restr .F-id = {!   !}
  restr .F-∘ = {!   !}

  module _ (final : is-final F) where
    restr-ff : is-fully-faithful restr
    restr-ff = {!   !}

    module _ (cart : Cartesian-fibration E) where
      open Cartesian-fibration

      restr-eso : is-split-eso restr
      restr-eso F' .fst .vert .F₀' {x} _ = has-lift.x' cart
        (final .is-final.map x)
        (F' .vert .F₀' {final .is-final.point x} _)
      restr-eso F' .fst .vert .F₁' {a} {b} {f} _ = {! rebase cart ? ?  !}
      restr-eso F' .fst .vert .F-id' = {!   !}
      restr-eso F' .fst .vert .F-∘' = {!   !}
      restr-eso F' .fst .F-cartesian = {!   !}
      restr-eso F' .snd = {!   !}

      restr-eqv : is-equivalence restr
      restr-eqv = ff+split-eso→is-equivalence restr-ff {!   !}
  -}

  {-
  module _ (t : Terminal B) where
    open Terminal t

    ε : Functor (Cartesian-sections E) (Fibre E top)
    ε .F₀ F' = F' .vert .F₀' {top} _
    ε .F₁ α' = α' .η' _
    ε .F-id = refl
    ε .F-∘ _ _ = refl

    ε-is-ff : is-fully-faithful ε
    ε-is-ff {F'} {G'} = is-iso→is-equiv i where
      r : ∀ x f → Hom[ id ] (F' .vert .F₀' {x} _) (G' .vert .F₀' {x} _)
      r x f = rebase' ! (F' .F-cartesian _ (idd-is-cartesian B)) (G' .F-cartesian _ (idd-is-cartesian B)) f
      i : is-iso (ε .F₁ {F'} {G'})
      i .is-iso.inv g .η' {x} _ = r x g
      i .is-iso.inv g .is-natural' {x} {y} {f = f} _ _ _ = uniquep₂ (G' .F-cartesian _ (idd-is-cartesian B)) _ _ refl _ _ (
        G' .vert .F₁' _ ∘' r y g ∘' F' .vert .F₁' {f = f} _ ≡[]⟨ {!   !} ⟩
        g ∘' F' .vert .F₁' {f = !} _ ∘' F' .vert .F₁' {f = f} _ ≡[]⟨ {! ap (g ∘'_) (sym (F' .vert .F-∘')) !} ⟩
        g ∘' F' .vert .F₁' {f = !} _ ≡[]⟨ {!   !} ⟩
        G' .vert .F₁' {f = !} _ ∘' r x g ≡[]⟨ {!   !} ⟩
        G' .vert .F₁' {f = !} _ ∘' G' .vert .F₁' {f = f} _ ∘' r x g ∎)
        refl
      {
      r(g, x); G(!x) = F(!x); g
      r(g, y); G(!y) = F(!y); g

      F(!x) = F(f); F(!y)
      G(!x) = G(f); G(!y)

      weak-mono (G(!y)) $
      r(g, x); G(f); G(!y)
      = r(g, x); G(!x)
      = F(!x); g
      = F(f); F(!y); g
      = F(f); r(g, y); G(!y)

      goal: r(g, x); G(f) = F(f); r(g, y)
      https://q.uiver.app/#q=WzAsOSxbMiwyLCJ4Il0sWzMsMSwiXFx0b3AiXSxbMiwwLCJ5Il0sWzAsMiwiRih4KSJdLFswLDAsIkYoeSkiXSxbMSwyLCJHKHgpIl0sWzEsMCwiRyh5KSJdLFs0LDIsIkYoXFx0b3ApIl0sWzQsMCwiRyhcXHRvcCkiXSxbMCwxXSxbMiwxXSxbMCwyLCJmIl0sWzMsNCwiRihmKSJdLFs1LDYsIkcoZikiXSxbMyw1LCJyKGcsIHgpIiwyXSxbNCw2XSxbNyw4LCJnIiwyXV0=
      }
      i .is-iso.rinv g = sym (uniquep (G' .F-cartesian _ (idd-is-cartesian B)) B.id-comm refl _ g {!   !})
      i .is-iso.linv n = =>↓-path {!   !}

    module _ (cart : Cartesian-fibration E) where
      module cart = Cartesian-fibration cart
      open import Cat.Morphism using (_≅_; Inverses)

      ε-eso : is-split-eso ε
      ε-eso top' .fst .vert .F₀' {x} _ = cart.has-lift.x' ! top'
      ε-eso top' .fst .vert .F₁' {a} {b} {f} _ = cart.has-lift.universal' ! top' (!-unique₂ _ _) (cart.has-lift.lifting ! top')
      ε-eso top' .fst .vert .F-id' = sym (cart.has-lift.uniquep ! top' _ refl (!-unique₂ _ _) id' (idr' _))
      ε-eso top' .fst .vert .F-∘' = {!  !}
      ε-eso top' .fst .F-cartesian _ _ = cartesian-pasting E {!   !} {!   !}
      ε-eso top' .snd = ≅↓→≅ i
        where
          i : cart.has-lift.x' ! top' ≅↓ top'
          i = invertible[]→iso[] $ vertical+cartesian→invertible E {f' = hom[ !-unique _ ] (cart.has-lift.lifting ! top')} $ cart[] (cart.has-lift.cartesian ! top')

      ε-is-equivalence : is-equivalence ε
      ε-is-equivalence = ff+split-eso→is-equivalence (λ {x y} → ε-is-ff {x} {y}) ε-eso
  -}

module _ {oj ℓj oc ℓc}
  {J : Precategory oj ℓj}
  {C : Precategory oc ℓc}
  (pb : has-pullbacks C)
  (G : Functor J C)
  -- (c : Colimit G)
  {X} (eta : G => Const X)
  where

  open import Cat.Diagram.Limit.Pullback
  open import Cat.Instances.Shape.Cospan
  module C = Cat.Reasoning C
  open Cat.Reasoning C

  {-
  pb' : has-pullbacks Cat[ J , C ]
  pb' {A} {B} {X} α β = go where
    open Pullback
    open Functor
    open _=>_
    module pb j = Pullback (pb (α .η j) (β .η j))
    go : Pullback Cat[ J , C ] α β
    go .apex .F₀ j = pb.apex j
    go .apex .F₁ {x} {y} f = pb.universal y {p₁' = A .F₁ f C.∘ pb.p₁ x} {p₂' = B .F₁ f C.∘ pb.p₂ x} (C.extendl (α .is-natural _ _ f) ∙ (C.refl⟩∘⟨ pb.square x) ∙ C.extendl (sym (β .is-natural _ _ f)))
    go .apex .F-id {x} = sym (pb.unique x (C.idr _ ∙ C.introl (A .F-id)) (C.idr _ ∙ C.introl (B .F-id)))
    go .apex .F-∘ {x} {y} {z} f g = {! pb.unique₂  !}
    go .p₁ .η x = pb.p₁ x
    go .p₁ .is-natural x y f = {!   !}
    go .p₂ .η x = pb.p₂ x
    go .p₂ .is-natural = {!   !}
    go .has-is-pb = {!   !}
  -}

  {-
  S∘G : Displayed J (oc ⊔ ℓc) ℓc
  S∘G = Change-of-base G (Slices C)
  -}

  open Vertical-functor
  open Vertical-fibred-functor
  open Functor
  open _=>_
  module E' = Cat.Reasoning (Slice Cat[ J , C ] G)
  module JC = Cat.Reasoning Cat[ J , C ]

  is-equifibered : ∀ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'} {F G : Functor C D} → F => G → Type _
  is-equifibered {C = C} {D} {F = F} {G} α = ∀ {x y} (f : C .Precategory.Hom x y) → is-pullback D (F .F₁ f) (α .η y) (α .η x) (G .F₁ f)

  Eq : E'.Ob → Type _
  Eq (cut α) = is-equifibered α
  Equifibered : Precategory _ _
  Equifibered = Restrict {C = Slice Cat[ J , C ] G} Eq

  module E = Cat.Reasoning Equifibered

  {-
  Comp : Functor (Cartesian-sections S∘G) Equifibered
  Comp .Functor.F₀ x .object ./-Obj.domain .Functor.F₀ y = x .vert .F₀' {y} _ ./-Obj.domain
  Comp .Functor.F₀ x .object ./-Obj.domain .Functor.F₁ f = x .vert .F₁' {f = f} _ .Slice-hom.to
  Comp .Functor.F₀ x .object ./-Obj.domain .Functor.F-id = ap Slice-hom.to (x .vert .F-id') ∙ transport-refl _
  Comp .Functor.F₀ x .object ./-Obj.domain .Functor.F-∘ f g = ap Slice-hom.to (x .vert .F-∘') ∙ transport-refl _
  Comp .Functor.F₀ x .object ./-Obj.map ._=>_.η y = x .vert .F₀' _ ./-Obj.map
  Comp .Functor.F₀ x .object ./-Obj.map ._=>_.is-natural _ _ f = sym (x .vert .F₁' _ .Slice-hom.commute)
  Comp .Functor.F₀ x .witness f = rotate-pullback $ weak-cartesian→pullback _ (lemma'' _ _ _ _ (cartesian→weak-cartesian _ (x .F-cartesian _ (idd-is-cartesian _))))
  Comp .Functor.F₁ n ./-Hom.map ._=>_.η x = n ._=>↓_.η' {x} _ .Slice-hom.to
  Comp .Functor.F₁ n ./-Hom.map ._=>_.is-natural x y f = sym (transport-refl _) ∙ apd (λ _ → Slice-hom.to) (n ._=>↓_.is-natural' {f = f} _ _ _) ∙ transport-refl _
  Comp .Functor.F₁ n ./-Hom.commutes = ext λ x → sym (n ._=>↓_.η' {x} _ .Slice-hom.commute) ∙ C.eliml (G .Functor.F-id)
  Comp .Functor.F-id = ext λ x → transport-refl _
  Comp .Functor.F-∘ f g = ext λ x → transport-refl _ ∙ transport-refl _

  Comp-is-ff : is-fully-faithful Comp
  Comp-is-ff = is-iso→is-equiv i where
    i : is-iso (Comp .Functor.F₁)
    i .is-iso.inv f ._=>↓_.η' {x} _ .Slice-hom.to = f ./-Hom.map ._=>_.η x
    i .is-iso.inv f ._=>↓_.η' {x} _ .Slice-hom.commute = C.eliml (G .Functor.F-id) ∙ sym (f ./-Hom.commutes ηₚ x)
    i .is-iso.inv f ._=>↓_.is-natural' {x} {y} {f'} _ _ _ = Slice-pathp _ _ (transport-refl _ ∙ f ./-Hom.map ._=>_.is-natural x y f' ∙ sym (transport-refl _))
    i .is-iso.rinv f = trivial!
    i .is-iso.linv f = =>↓-path λ _ → Slice-path _ refl

  Comp-is-precat-iso : is-precat-iso Comp
  Comp-is-precat-iso .is-precat-iso.has-is-ff = Comp-is-ff
  Comp-is-precat-iso .is-precat-iso.has-is-iso = is-iso→is-equiv is where
    is : is-iso (Comp .F₀)
    is .is-iso.inv y .vert .F₀' {x} _ = cut (y .object ./-Obj.map .η x)
    is .is-iso.inv y .vert .F₁' {x} {y'} {f} _ .Slice-hom.to = y .object ./-Obj.domain .F₁ {x} {y'} f
    is .is-iso.inv y .vert .F₁' {x} {y'} {f} _ .Slice-hom.commute = sym (y .object ./-Obj.map .is-natural x y' f)
    is .is-iso.inv y .vert .F-id' = Slice-path _ (y .object ./-Obj.domain .F-id ∙ sym (transport-refl _))
    is .is-iso.inv y .vert .F-∘' = Slice-path _ (y .object ./-Obj.domain .F-∘ _ _ ∙ sym (transport-refl _))
    is .is-iso.inv y .F-cartesian {f = f} _ _ = lemma _ _ _ _ (pullback→cartesian _ (rotate-pullback (y .witness f)))
    is .is-iso.rinv y = Restrict-ob-path (/-Obj-path (Functor-path (λ _ → refl) (λ _ → refl)) (Nat-pathp _ _ λ _ → refl)) (is-prop→pathp (λ _ → hlevel 1) _ _)
    is .is-iso.linv y = Vertical-fibred-functor-path (λ _ → refl) λ _ → refl
  -}

  C/X = Slice C X
  module C/X = Cat.Reasoning C/X

  open /-Hom
  open /-Obj
  module _ where
    open Pullback

    Cst : Functor C/X Equifibered
    Cst .F₀ (cut {X} p) = restrict go equi module Cst where
      module pb j = Pullback (pb p (eta .η j))
      go : Precategory.Ob (Slice Cat[ J , C ] G)
      go ./-Obj.domain .F₀ x = pb.apex x
      go ./-Obj.domain .F₁ {x} {y} f = pb.universal y {p₁' = pb.p₁ x} {p₂' = G .F₁ f C.∘ pb.p₂ x} (pb.square x ∙ C.pushl (sym (eta .is-natural _ _ f ∙ C.idl _)))
      go ./-Obj.domain .F-id {x} = sym (pb.unique x (C.idr _) (C.idr _ ∙ C.introl (G .F-id)))
      go ./-Obj.domain .F-∘ {x} {y} {z} f g = sym (pb.unique z (C.pulll (pb.p₁∘universal z) ∙ pb.p₁∘universal y) (C.pulll (pb.p₂∘universal z) ∙ C.extendr (pb.p₂∘universal y) ∙ (sym (G .F-∘ _ _) C.⟩∘⟨refl)))
      go ./-Obj.map .η x = pb.p₂ x
      go ./-Obj.map .is-natural x y f = pb.p₂∘universal y
      equi : is-equifibered (go .map)
      equi {x} {y} f = pasting-outer→left-is-pullback (pb.has-is-pb y) (subst₂ (λ a b → is-pullback C a _ (pb.p₂ x) b) (sym (pb.p₁∘universal y)) (sym (eta .is-natural _ _ f ∙ C.idl _)) (pb.has-is-pb x)) (pb.p₂∘universal y)
    Cst .F₁ h ./-Hom.map .η x = Base-change pb (eta .η x) .F₁ h .map
    Cst .F₁ {X} {Y} h ./-Hom.map .is-natural x y f =
      unique₂ (pb (Y .map) (eta .η y)) {p = C.pulll (h .commutes) ∙ pb (X .map) (eta .η x) .square ∙ C.pushl (sym (eta .is-natural _ _ f ∙ C.idl _))}
      (C.pulll (pb (Y .map) (eta .η y) .p₁∘universal) ∙ C.pullr (pb (X .map) (eta .η y) .p₁∘universal))
      (C.pulll (pb (Y .map) (eta .η y) .p₂∘universal) ∙ pb (X .map) (eta .η y) .p₂∘universal)
      (C.pulll (pb (Y .map) (eta .η y) .p₁∘universal) ∙ pb (Y .map) (eta .η x) .p₁∘universal)
      (C.pulll (pb (Y .map) (eta .η y) .p₂∘universal) ∙ C.pullr (pb (Y .map) (eta .η x) .p₂∘universal))
    Cst .F₁ h ./-Hom.commutes = ext λ x → pb _ (eta .η x) .p₂∘universal
    Cst .F-id = /-Hom-path (ext λ x → ap map (Base-change pb (eta .η x) .F-id))
    Cst .F-∘ f g = /-Hom-path (ext λ x → ap map (Base-change pb (eta .η x) .F-∘ f g))

  -- Cst : Functor C/X (Cartesian-sections S∘G)
  -- Cst .F₀ (cut map) .vert .F₀' {x} _ = Base-change pb (eta .η x) .F₀ (cut map)
  -- Cst .F₀ (cut map) .vert .F₁' {a} {b} {f} _ = {! Base-change pb (eta .η b) .F₁  !}
  -- Cst .F₀ (cut map) .vert .F-id' = {!   !}
  -- Cst .F₀ (cut map) .vert .F-∘' = {!   !}
  -- Cst .F₀ (cut map) .F-cartesian = {!   !}
  -- Cst .F₁ = {!   !}
  -- Cst .F-id = {!   !}
  -- Cst .F-∘ = {!   !}

  thing : ∀ (A : E.Ob) → Functor J C/X
  thing A .F₀ j = cut (eta .η j ∘ A .object .map .η j)
  thing A .F₁ g .map = A .object .domain .F₁ g
  thing A .F₁ g .commutes = pullr (A .object .map .is-natural _ _ g) ∙ pulll (eta .is-natural _ _ g ∙ idl _)
  thing A .F-id = ext (A .object .domain .F-id)
  thing A .F-∘ g h = ext (A .object .domain .F-∘ _ _)
  {-# TERMINATING #-}
  Cst-in : ∀ {A B} → (E.Hom A (Cst .F₀ B)) ≃ (thing A => Const B)
  Cst-in {A} {B} = Iso→Equiv is where
    open is-iso
    is : Iso (E.Hom A (Cst .F₀ B)) (thing A => Const B)
    is .fst h .η j .map = pb _ _ .Pullback.p₁ ∘ h .map .η j
    is .fst h .η j .commutes = extendl (pb _ _ .Pullback.square) ∙ (refl⟩∘⟨ h .commutes ηₚ j)
    is .fst h .is-natural _ _ g = ext (pullr (h .map .is-natural _ _ g) ∙ pulll (pb _ _ .Pullback.p₁∘universal) ∙ sym (idl _))
    is .snd .inv h .map .η j = pb _ _ .Pullback.universal (h .η j .commutes)
    is .snd .inv h .map .is-natural _ _ g = Pullback.unique₂ (pb _ _) {p = (refl⟩∘⟨ pulll (pb _ _ .Pullback.p₁∘universal)) ∙ extendl (h .η _ .commutes) ∙ (refl⟩∘⟨ pushl (sym (pb _ _ .Pullback.p₂∘universal)))} refl refl (pulll (pb _ _ .Pullback.p₁∘universal) ∙ pb _ _ .Pullback.p₁∘universal ∙ sym (unext (h .is-natural _ _ g) ∙ idl _) ∙ pushl (sym (pb _ _ .Pullback.p₁∘universal))) (pulll (pb _ _ .Pullback.p₂∘universal) ∙ pullr (pb _ _ .Pullback.p₂∘universal) ∙ sym (A .object .map .is-natural _ _ g) ∙ pushl (sym (pb _ _ .Pullback.p₂∘universal)))
    is .snd .inv h .commutes = ext λ j → pb _ _ .Pullback.p₂∘universal
    is .snd .rinv h = ext λ j → pb _ _ .Pullback.p₁∘universal
    is .snd .linv h = ext λ j → sym (pb _ _ .Pullback.unique refl (h .commutes ηₚ j))

  is-van-kampen : Type (oj ⊔ ℓj ⊔ oc ⊔ ℓc)
  is-van-kampen = is-equivalence Cst
  module is-van-kampen (vk : is-van-kampen) where
    Co : Functor Equifibered (Slice C X)
    Co = vk .is-equivalence.F⁻¹

    VK-iso : ∀ {A B} → C/X.Hom (Co .F₀ A) B ≃ E.Hom A (Cst .F₀ B)
    VK-iso = _ , L-adjunct-is-equiv (is-equivalence.F⁻¹⊣F vk)
    Co-out : ∀ {A B} → C/X.Hom (Co .F₀ A) B ≃ (thing A => Const B)
    Co-out {A} {B} = VK-iso ∙e Cst-in
    Co-out-natural : ∀ {A B B'} (f : C/X.Hom (Co .F₀ A) B) (h : C/X.Hom B B')
      → Co-out .fst (h C/X.∘ f) ≡ const-nt h ∘nt Co-out .fst f
    Co-out-natural f h = ap (Cst-in .fst) (L-adjunct-naturalr (is-equivalence.F⁻¹⊣F vk) h f) ∙ ext λ j → extendl (pb _ _ .Pullback.p₁∘universal)

  -- TODO use _⋆_
  is-van-kampen' : Type (oj ⊔ ℓj ⊔ oc ⊔ ℓc)
  is-van-kampen' =
    ∀ Y (f : Hom Y X)
    → (F : Functor J C) (α : F => G) (eq : is-equifibered α)
    → (β : F => Const Y) (_ : eta ∘nt α ≡ const-nt f ∘nt β)
    → (∀ j → is-pullback C (β .η j) f (α .η j) (eta .η j)) ≃ is-colimit F Y β

  module _ (F : Functor J C) (α : F => G) (eq : is-equifibered α) where
    promote : Functor J C/X
    promote = thing (restrict (cut α) eq)

    whatevs : ∀ Y (f : Hom Y X) (β : F => Const Y) (_ : eta ∘nt α ≡ const-nt f ∘nt β) → promote => Const (cut f)
    whatevs Y f β com .η j .map = β .η j
    whatevs Y f β com .η j .commutes = sym (com ηₚ j)
    whatevs Y f β com .is-natural _ _ h = ext (β .is-natural _ _ h)

    module _ (vk : is-van-kampen) where
      open is-van-kampen vk

      whatever : promote => Const (Co .F₀ (restrict (cut α) eq))
      whatever = Equiv.to Co-out C/X.id

      Co-is-colimit : is-colimit promote (Co .F₀ (restrict (cut α) eq)) whatever
      Co-is-colimit = to-is-colimitp mk refl where
        open make-is-colimit
        mk : make-is-colimit _ _
        mk .ψ = _
        mk .commutes g = whatever .is-natural _ _ g ∙ C/X.idl _
        mk .universal eps comm = Equiv.from Co-out (NT eps λ _ _ h → ext (ap map (comm h) ∙ sym (idl _)))
        mk .factors {j} eps comm = (sym (Co-out-natural C/X.id (mk .universal eps comm)) ηₚ j) ∙ ap (λ x → Co-out .fst x .η j) (C/X.idr _) ∙ Equiv.ε Co-out _ ηₚ j
        mk .unique eps comm u fac = Equiv.adjunctl Co-out (ap (Co-out .fst) (sym (C/X.idr _)) ∙ Co-out-natural C/X.id u ∙ ext λ j → unext (fac j))

  is-van-kampen'' : Type (oj ⊔ ℓj ⊔ oc ⊔ ℓc)
  is-van-kampen'' =
    ∀ Y (f : Hom Y X)
    → (F : Functor J C) (α : F => G) (eq : is-equifibered α)
    → (β : F => Const Y) (com : eta ∘nt α ≡ const-nt f ∘nt β)
    → (∀ j → is-pullback C (β .η j) f (α .η j) (eta .η j)) ≃ is-colimit (promote F α eq) (cut f) (whatevs F α eq Y f β com)

  module _ (colims : (A : E.Ob) → Colimit (A .object .domain)) (vk : is-van-kampen) Y (f : Hom Y X) (F : Functor J C) (α : F => G) (eq : is-equifibered α) (β : F => Const Y) (com : eta ∘nt α ≡ const-nt f ∘nt β) where
  -- toVK : is-van-kampen → is-van-kampen'
  -- toVK vk Y f F α eq β com = i ∙e ii ∙e wut ∙e iii ∙e colim-slice where
    open is-van-kampen vk
    A : E.Ob
    A = restrict (cut α) eq
    h : thing A => Const (cut f)
    what : Forget-slice F∘ thing A ≡ F
    what = Functor-path (λ _ → refl) (λ _ → refl)
    h = whatevs F α eq Y f β com
    h' : E.Hom A (Cst .F₀ (cut f))
    h' = Equiv.from Cst-in h
    i : (∀ j → is-pullback C (β .η j) f (α .η j) (eta .η j)) ≃ E.is-invertible {a = A} {Cst .F₀ (cut f)} h'
    i =
      (∀ j → is-pullback C (β .η j) f (α .η j) (eta .η j)) ≃⟨ Π-cod≃ (λ j → pullback-unique (pb _ _ .Pullback.has-is-pb) (sym (com ηₚ j)) e⁻¹) ⟩
      (∀ j → is-invertible (h' .map .η j))                 ≃⟨ prop-ext (hlevel 1) (hlevel 1) (invertible→invertibleⁿ (h' .map)) is-invertibleⁿ→is-invertible ⟩
      is-invertibleⁿ (h' .map)                             ≃˘⟨ conservative→equiv {F = Forget-slice} Forget-slice-is-conservative ⟩
      E'.is-invertible h'                                  ≃˘⟨ conservative→equiv {F = Forget-full-subcat} (is-ff→is-conservative {F = Forget-full-subcat} is-fully-faithful-Forget-full-subcat) ⟩
      E.is-invertible h'                                   ≃∎

    ii : E.is-invertible {a = A} {Cst .F₀ (cut f)} h'
       ≃ C/X.is-invertible (Equiv.from (VK-iso {A = A}) h')
    ii = R-adjunct-preserves-invertible Co (is-equivalence.inverse-equivalence vk) h'

    h'' = Co-is-colimit F α eq vk .is-colimit.universal (λ j → h .η j) λ g → ext (β .is-natural _ _ g ∙ idl _)
    wut : C/X.is-invertible (Equiv.from (VK-iso {A = A}) h') ≃ C/X.is-invertible h''
    wut = path→equiv (ap C/X.is-invertible (ap (Equiv.from (Co-out {A} {cut f})) (ext λ _ → refl)))
    iii : C/X.is-invertible h'' ≃ is-colimit (promote F α eq) (cut f) (whatevs F α eq Y f β com)
    iii = prop-ext (hlevel 1) (hlevel 1)
      (λ inv → is-invertible→is-colimitp {K = Const _} (Co-is-colimit F α eq vk) _ (λ g → ext (β .is-natural _ _ g ∙ idl _)) refl inv)
      iii'
      where
      iii' : is-colimit (promote F α eq) (cut f) (whatevs F α eq Y f β com) → C/X.is-invertible h''
      iii' col = colimits→invertiblep col (Co-is-colimit F α eq vk) (Co-is-colimit F α eq vk .is-colimit.factors _ λ g → ext (β .is-natural _ _ g ∙ idl _))
    colim-path : ∀ {K : Ob} {D D' : Functor J C} {eta : D => Const K} {eta' : D' => Const K} (p : D ≡ D') (peta : PathP (λ i → p i => Const K) eta eta') → is-colimit D K eta ≡ is-colimit D' K eta'
    colim-path = {!   !}
    colim-slice : is-colimit (promote F α eq) (cut f) (whatevs F α eq Y f β com) ≃ is-colimit F Y β
    colim-slice = prop-ext (hlevel 1) (hlevel 1)
      (Forget-slice-preserves (thing A)) (Forget-slice-reflects (thing A))
      ∙e path→equiv {! colim-path ? ?  !}

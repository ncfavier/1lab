open import Cat.CartesianClosed.Locally
open import Cat.Functor.Adjoint.Compose
open import Cat.Diagram.Colimit.Cocone
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Adjoint.Hom
open import Cat.Diagram.Equaliser
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Functor.Constant
open import Cat.Diagram.Product
open import Cat.Functor.Adjoint
open import Cat.Instances.Slice
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning

open Functor
open Cocone
open /-Obj
open /-Hom
open _=>_

module wip.SigmaAdjointLifting where

module _
    {o ℓ} {C : Precategory o ℓ} {B}
    (prod : has-products C)
    {od ℓd} {D : Precategory od ℓd} (eqs : has-equalisers D) (F : Functor D (Slice C B))
  where

  open Equalisers D eqs
  private
    module C = Cat.Reasoning C
    module C/B = Cat.Reasoning (Slice C B)
    module D = Cat.Reasoning D
    module F = Cat.Functor.Reasoning F

  compose-Forget/
    : (G : Functor (Slice C B) D)
    → F ⊣ G
    → Forget/ F∘ F ⊣ G F∘ constant-family prod
  compose-Forget/ G F⊣G = LF⊣GR F⊣G (Forget⊣constant-family prod)

  lift-Forget/
    : (G' : Functor C D)
    → Forget/ F∘ F ⊣ G'
    → Σ (Functor (Slice C B) D) λ G → F ⊣ G
  lift-Forget/ G' UF⊣G' = G , F⊣G where
    module G' = Cat.Functor.Reasoning G'
    module UF⊣G' = _⊣_ UF⊣G'

    σ : Cocone (Id {C = D})
    σ .coapex = G'.₀ B
    σ .ψ X = L-adjunct UF⊣G' (F.₀ X .map)
    σ .commutes f = L-adjunct-ap UF⊣G' (F.₁ f .commutes)

    G : Functor (Slice C B) D
    G .F₀ p = Equ (G'.₁ (p .map)) (σ .ψ (G'.₀ (p .domain)))
    G .F₁ {x} {y} f = equaliser.universal _ _ $
      G'.₁ (y .map) D.∘ G'.₁ (f .map) D.∘ equaliser.equ _ _           ≡⟨ G'.pulll (f .commutes) ⟩
      G'.₁ (x .map) D.∘ equaliser.equ _ _                             ≡⟨ equaliser.equal _ _ ⟩
      σ .ψ (G'.₀ (x .domain)) D.∘ equaliser.equ _ _                   ≡˘⟨ D.pulll (σ .commutes _) ⟩
      σ .ψ (G'.₀ (y .domain)) D.∘ G'.₁ (f .map) D.∘ equaliser.equ _ _ ∎
    G .F-id = sym (equaliser.unique _ _ (D.idr _ ∙ G'.introl refl))
    G .F-∘ f g = sym (equaliser.unique _ _ (D.pulll (equaliser.factors _ _)
      ∙ D.pullr (equaliser.factors _ _) ∙ G'.pulll refl))

    module G = Cat.Functor.Reasoning G

    F⊣G : F ⊣ G
    F⊣G = hom-iso-inv→adjoints
      (Equiv.from eqv)
      (inverse-is-equiv (eqv .snd))
      λ f g h → ext $
        R-adjunct UF⊣G' (equaliser.equ _ _ D.∘ G.₁ f D.∘ h D.∘ g)           ≡⟨ ap (R-adjunct UF⊣G') (D.pulll (equaliser.factors _ _)) ⟩
        R-adjunct UF⊣G' ((G'.₁ (f .map) D.∘ equaliser.equ _ _) D.∘ h D.∘ g) ≡⟨ ap (R-adjunct UF⊣G') (D.extendl (sym (D.assoc _ _ _))) ⟩
        R-adjunct UF⊣G' (G'.₁ (f .map) D.∘ (equaliser.equ _ _ D.∘ h) D.∘ g) ≡⟨ R-adjunct-natural₂ UF⊣G' _ _ _ ⟩
        f .map C.∘ R-adjunct UF⊣G' (equaliser.equ _ _ D.∘ h) C.∘ F.₁ g .map ∎
      where
        Slice-hom-equiv : ∀ {x : D.Ob} {y : C/B.Ob} → C/B.Hom (F.₀ x) y ≃ Σ (C.Hom (F.₀ x .domain) (y .domain)) λ h → y .map C.∘ h ≡ F.₀ x .map
        Slice-hom-equiv .fst f = (f .map) , (f .commutes)
        Slice-hom-equiv .snd = is-iso→is-equiv λ where
          .is-iso.from (f , c) .map → f
          .is-iso.from (f , c) .commutes → c
          .is-iso.rinv _ → refl
          .is-iso.linv _ → ext refl
        eqv : ∀ {x : D.Ob} {y : C/B.Ob} → C/B.Hom (F.₀ x) y ≃ D.Hom x (G.₀ y)
        eqv = Slice-hom-equiv ∙e Σ-ap (adjunct-hom-equiv UF⊣G') (λ f → ap-equiv (adjunct-hom-equiv UF⊣G') ∙e ∙-pre-equiv (sym (L-adjunct-naturalr UF⊣G' _ _)) ∙e ∙-post-equiv (sym (σ .commutes _))) ∙e equaliser.equaliser-univ _ _ e⁻¹

module _
    {o ℓ} {C : Precategory o ℓ} {A B} (p : C .Precategory.Hom A B)
    (prod : has-products C) (pullbacks : has-pullbacks C)
  where

  private
    module C = Cat.Reasoning C
    module lex/ {b} = Finitely-complete (Slice-lex {b = b} pullbacks)

    prod/ : ∀ {a} → has-products (Slice C a)
    prod/ = Slice-products pullbacks

    terminal/ : ∀ {a} → Terminal (Slice C a)
    terminal/ = Slice-terminal-object

  open import Cat.Diagram.Exponential
  open import Cat.Functor.Pullback

  exp→pi : (∀ x → Exponential (Slice C B) prod/ terminal/ (cut p) x) → Σ (Functor (Slice C A) (Slice C B)) λ G → Base-change pullbacks p ⊣ G
  exp→pi cart = lift-Forget/ prod lex/.equalisers (Base-change pullbacks p) {!   !} (adjoint-natural-isol {! Slice-product-functor ? ?  !} {!   !})

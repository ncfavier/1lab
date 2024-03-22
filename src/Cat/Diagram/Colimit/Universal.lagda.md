<!--
```agda
open import Cat.Prelude
open import Cat.Instances.Shape.Join
open import Cat.Instances.Shape.Terminal
open import 1Lab.Reflection.Regularity
open import Cat.Diagram.Pullback
open import Cat.Diagram.Pullback.Properties
open import Cat.Functor.Naturality
open import Cat.Functor.Pullback
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Kan.Base
open import Cat.Functor.Base
open import Cat.Instances.Slice
open import Cat.Instances.Slice.Colimit
open import Cat.Diagram.Colimit.Base

open import Data.Sum

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Colimit.Universal where
```

# Universal colimits {defines="universal-colimit pullback-stable-colimit"}

A [[colimit]] is called **universal**, or **pullback-stable**, if it is
preserved under [[base change|pullback functor]].

There are two ways to make this precise: first, we might consider
pulling back a colimiting cocone --- say, to simplify, a coproduct
diagram $A \to A + B \ot B$ --- along some morphism $f : Y \to A + B$:

~~~{.quiver}
% https://q.uiver.app/#q=WzAsNixbMCwxLCJBIl0sWzEsMSwiQStCIl0sWzIsMSwiQiJdLFsxLDAsIlkiXSxbMCwwLCJmXiogQSJdLFsyLDAsImZeKiBCIl0sWzAsMV0sWzIsMV0sWzMsMSwiZiIsMl0sWzQsM10sWzQsMF0sWzQsMSwiIiwwLHsic3R5bGUiOnsibmFtZSI6ImNvcm5lciJ9fV0sWzUsMl0sWzUsM10sWzUsMSwiIiwyLHsic3R5bGUiOnsibmFtZSI6ImNvcm5lciJ9fV1d
\[\begin{tikzcd}
	{f^* A} & Y & {f^* B} \\
	A & {A+B} & B
	\arrow[from=2-1, to=2-2]
	\arrow[from=2-3, to=2-2]
	\arrow["f"', from=1-2, to=2-2]
	\arrow[from=1-1, to=1-2]
	\arrow[from=1-1, to=2-1]
	\arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=2-2]
	\arrow[from=1-3, to=2-3]
	\arrow[from=1-3, to=1-2]
	\arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-90}, draw=none, from=1-3, to=2-2]
\end{tikzcd}\]
~~~

We say that the bottom colimit is stable under pullback if the top
cocone $f^* A \to Y \ot f^* B$ is colimiting.

Alternatively, we might consider a *second* cocone with a map from $A + B$
and pull it back along some morphism $f : Y \to X$ like so:

~~~{.quiver}
% https://q.uiver.app/#q=WzAsOCxbMiwzLCJCIl0sWzEsMywiQStCIl0sWzAsMywiQSJdLFsxLDIsIlgiXSxbMSwxLCJZIl0sWzIsMCwiZl4qIEIiXSxbMSwwLCJmXiooQSArIEIpIl0sWzAsMCwiZl4qIEEiXSxbMCwxXSxbMiwxXSxbMSwzXSxbNCwzLCJmIl0sWzYsNF0sWzcsNl0sWzUsNl0sWzcsNF0sWzUsNF0sWzAsM10sWzIsM10sWzcsMl0sWzUsMF0sWzcsMywiIiwxLHsic3R5bGUiOnsibmFtZSI6ImNvcm5lciJ9fV0sWzUsMywiIiwxLHsic3R5bGUiOnsibmFtZSI6ImNvcm5lciJ9fV1d
\[\begin{tikzcd}
	{f^* A} & {f^*(A + B)} & {f^* B} \\
	& Y \\
	& X \\
	A & {A+B} & B
	\arrow[from=4-3, to=4-2]
	\arrow[from=4-1, to=4-2]
	\arrow[from=4-2, to=3-2]
	\arrow["f", from=2-2, to=3-2]
	\arrow[from=1-2, to=2-2]
	\arrow[from=1-1, to=1-2]
	\arrow[from=1-3, to=1-2]
	\arrow[from=1-1, to=2-2]
	\arrow[from=1-3, to=2-2]
	\arrow[from=4-3, to=3-2]
	\arrow[from=4-1, to=3-2]
	\arrow[from=1-1, to=4-1]
	\arrow[from=1-3, to=4-3]
	\arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-2]
	\arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-90}, draw=none, from=1-3, to=3-2]
\end{tikzcd}\]
~~~

In this case, we again say that the colimit is stable under pullback if
the top diagram is colimiting in $\cC/Y$, which amounts to saying that the
[[pullback functor]] $f^* : \cC/X \to \cC/Y$ preserves this colimit.

::: source
Higher Topos Theory, lemma 6.1.3.3
:::

```agda
module _ {oj ℓj oc ℓc}
  {J : Precategory oj ℓj}
  {C : Precategory oc ℓc}
  (pb : has-pullbacks C)
  (G : Functor J C)
  (c : Colimit G)
  where
  open Cat.Reasoning C
  open Functor
  open _=>_

  module c = Colimit c

  extend : ∀ {Z} → G => Const Z → Functor J (Slice C Z)
  extend p .F₀ j = cut (p .η j)
  extend p .F₁ f ./-Hom.map = G .F₁ f
  extend p .F₁ f ./-Hom.commutes = p .is-natural _ _ f ∙ idl _
  extend p .F-id = ext (G .F-id)
  extend p .F-∘ f g = ext (G .F-∘ f g)

  module _ {Z} {G : Functor J C} where
    extend' : G => Const Z → Functor (J ⋆ ⊤Cat) C
    extend' α .F₀ (inl j) = G .F₀ j
    extend' α .F₀ (inr tt) = Z
    extend' α .F₁ {inl x} {inl y} (lift f) = G .F₁ f
    extend' α .F₁ {inl x} {inr tt} (lift f) = α .η x
    extend' α .F₁ {inr tt} {inr tt} (lift tt) = id
    extend' α .F-id {inl x} = G .F-id
    extend' α .F-id {inr x} = refl
    extend' α .F-∘ {inl x} {inl y} {inl z} f g = G .F-∘ _ _
    extend' α .F-∘ {inl x} {inl y} {inr z} f g = sym (α .is-natural _ _ _ ∙ idl _)
    extend' α .F-∘ {inl x} {inr y} {inr z} f g = sym (idl _)
    extend' α .F-∘ {inr x} {inr y} {inr z} f g = sym (idl _)

  is-universal-colimit : Type _
  is-universal-colimit = ∀ {Y Z} (f : Hom Y Z) (p : G => Const Z) → preserves-colimit (Base-change pb f) (extend p)

  is-universal-colimit' : Type _
  is-universal-colimit' =
    ∀ {Y} (F : Functor J C) (β : F => Const Y) (α : extend' β => extend' c.cocone) → is-equifibered α → is-colimit F Y β
    -- ∀ {Y} (f : Hom Y c.coapex)
    -- → (F : Functor J C) (α : F => G) (eq : is-equifibered α)
    -- → (β : F => Const Y) (_ : c.cocone ∘nt α ≡ const-nt f ∘nt β)
    -- → (∀ j → is-pullback C (β .η j) f (α .η j) (c.cocone .η j))
    -- → is-colimit F Y β

  forwards : is-universal-colimit → is-universal-colimit'
  forwards uni F β α eq = natural-isos→is-lan idni
    (iso→isoⁿ
      (λ j → invertible→iso _ (Equiv.from (pullback-unique (rotate-pullback (eq {inl j} {inr _} _)) (pb _ _ .Pullback.square)) (pb _ _ .Pullback.has-is-pb)))
      (λ f → {!   !}))
    (iso→⊤-natural-iso (invertible→iso _ (invertible-is-pullback-stable _ id _ id-invertible (rotate-pullback (pb _ _ .Pullback.has-is-pb)))))
    (ext λ j → {!   !})
    (Forget/-preserves-colimits _ {!   !} foo)
    where
      eta : extend c.cocone => const! (cut id) F∘ !F
      eta .η j = Slice-terminal-object' _ .centre
      eta .is-natural _ _ f = ext (c.eta .is-natural _ _ f ∙ (c.Ext.F-id ⟩∘⟨refl))
      colim : is-lan !F (extend c.cocone) (Const (cut id)) eta
      colim = Forget/-reflects-colimits _ (natural-isos→is-lan idni (path→iso (Functor-path (λ _ → refl) (λ _ → refl))) (iso→⊤-natural-iso id-iso) (ext (λ j → eliml (idl _) ∙ elimr {! Regularity.reduce! !})) c.has-lan)
      foo : preserves-lan (Base-change pb (α .η (inr _))) colim
      foo = uni (α .η (inr _)) c.cocone colim

  backwards : is-universal-colimit' → is-universal-colimit
  backwards uni f p colim = {! uni  !}
```

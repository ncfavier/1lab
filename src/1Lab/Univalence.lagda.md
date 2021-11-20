```
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Univalence where
```

# Univalence

The univalence axiom says that equivalent types can be identified. In
cubical type theory, this is implemented computationally using the
`Glue`{.Agda} type former, which - roughly - lets us fill a cube of
types where some of the faces can be an equivalence.

The idea is that if you have an open box in `Type`{.Agda}, it's possible
to replace some faces with _equivalences_ rather than _paths_ and still
have everything work out. For example, we can extend the canonical
equivalence of unary and binary natural numbers to a path in the
universe:

<figure>

~~~{.quiver .short-2}
\[\begin{tikzcd}
  {\mathrm{Nat}} && {\mathrm{Bin}}
  \arrow["\simeq", from=1-1, to=1-3]
\end{tikzcd}\]
~~~

<figcaption>
Even though this diagram indicates a _path_, the arrow is marked with
$\simeq$, to indicate that it comes from an equivalence.
</figcaption>

</figure>

In the one-dimensional case, this corresponds to having a constant
`ua`{.Agda} which turns an equivalence into a path. If this function
additionally satisfies "transport along ua(f) is the same as applying f"
(`uaβ`{.Agda}), then this function can be shown to be an inverse to the
map `pathToEquiv`{.Agda}.

To do this, Cubical Agda provides us with a primitive satisfying an
appropriate _boundary condition_: Depending on a given formula, the type
former `Glue`{.Agda} reduces to one of the types involved, and transport
along the path generated by `Glue`{.Agda} involves applying the
equivalence.

[an internal Agda module]: agda://Agda.Builtin.Cubical.HCompU

<details>
<summary>
First, bindings must be provided for the Cubical Agda `Glue`{.Agda}
primitives. There is also [an internal Agda module] that needs to be
loaded, since it provides a proof that transport along a path is an
equivalence.  This is needed internally, for homogeneous composition in
`Type`{.Agda}.
</summary>

```
private
  variable
    ℓ ℓ' : Level

  primitive
    primGlue : (A : Type ℓ) {φ : I}
             → (T : Partial φ (Type ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
             → Type ℓ'

    prim^glue : {A : Type ℓ} {φ : I}
              → {T : Partial φ (Type ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
              → PartialP φ T → A → primGlue A T e

    prim^unglue : {A : Type ℓ} {φ : I}
                → {T : Partial φ (Type ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
                → primGlue A T e → A

open import Agda.Builtin.Cubical.HCompU
```
</details>

Now we can build a friendly interface for them:

```
Glue : (A : Type ℓ) {φ : I}
     → (Te : Partial φ (Σ[ T ∈ Type ℓ' ] (T ≃ A)))
     → Type ℓ'
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

unglue : {A : Type ℓ} (φ : I) {T : Partial φ (Type ℓ')}
         {e : PartialP φ (λ o → T o ≃ A)} → primGlue A T e → A
unglue φ = prim^unglue {φ = φ}
```

The arguments to Glue are a _base type_ `A`, and a [family of partial
types], which must all be equivalent to the base type `A`. The point of
`Glue` it satisfies a _boundary condition_: When `φ = i1`, `Glue B (λ _
→ A, eqv)` reduces to `A`:

[family of partial types]: agda://1Lab.Path.Partial

```
module _ {A B : Type} {e : A ≃ B} where
  private
    Glue-boundary : Glue B {i1} (λ x → A , e) ≡ A
    Glue-boundary i = A
```

From this computation rule, we can turn any equivalence into a path:

```
ua : {A B : Type ℓ} → A ≃ B → A ≡ B
ua {A = A} {B} eqv i = Glue B λ { (i = i0) → A , eqv
                                ; (i = i1) → B , _ , idEquiv
                                }
```

Why does this definition go through? Because of the boundary condition
for Glue! When `i = i0`, the whole thing evaluates to `A`, meaning that
the left endpoint of the path is correct. The same thing happens with
the right endpoint. And, what's more, the evaluation rules for
`transport`{.Agda} give us the correct computation rule for this path:

```
uaβ : {A B : Type ℓ} (f : A ≃ B) (x : A) → transport (ua f) x ≡ f .fst x
uaβ {A = A} {B} f x i = transp (λ _ → B) i (f .fst x)
```

There is also a convenient composition of `ua` and `isIso→isEquiv`{.Agda}:

```
Iso→path : {A B : Type ℓ} → Iso A B → A ≡ B
Iso→path (f , iiso) = ua (f , isIso→isEquiv iiso)
```

# The axiom

```
pathToEquiv : {A B : Type ℓ} → A ≡ B → A ≃ B
pathToEquiv {A = A} {B} = J (λ x _ → A ≃ x) (_ , idEquiv)

pathToEquiv-refl : {A : Type ℓ} → pathToEquiv (λ i → A) ≡ (_ , idEquiv)
pathToEquiv-refl {A = A} = JRefl (λ x _ → A ≃ x) (_ , idEquiv)
```

The actual univalence axiom says that the canonical map `A ≡ B`, defined
using `J`, is an equivalence. This map is `pathToEquiv`{.Agda}, defined
right above. In more intuitive terms, it's "casting" the identity
equivalence `A ≃ A` along a proof that `A ≡ B` to get an equivalence `A
≃ B`.


```
univalence : {A B : Type ℓ} → isEquiv (pathToEquiv {A = A} {B})
```

We can now prove the univalence theorem - this map is an isomorphism,
and thus, an equivalence. First, we need a small lemma that says `ua id
≡ refl`. This will be used to show one direction of the inverse.

```
uaIdEquiv : {A : Type ℓ} → ua (_ , idEquiv {A = A}) ≡ refl
uaIdEquiv {A = A} i j = Glue A {φ = i ∨ ~ j ∨ j} (λ _ → A , _ , idEquiv)

univalence {A = A} {B} = isIso→isEquiv iiso where
```

It's easy to show that using `Glue`{.Agda}. There are two interval
variables, this is a path between paths: a square. When `i = i0`, the
glue is stuck[^1], so we get `Glue A (λ _ → A , _ , idEquiv)`. When `i =
i1`, by the argument `φ`, the glue computes away, and we get `refl`,
hence the type.

[^1]: Pardon the pun.

```
  iiso : isIso pathToEquiv
  isIso.g iiso = ua
```

The inverse to `pathToEquiv`{.Agda} is the `ua`{.Agda} map which turns
equivalences into paths.

```
  isIso.right-inverse iiso (f , isEqv) = Σ-Path p (isProp-isEquiv f _ _) where
    p : transport (λ i → A → ua (f , isEqv) i) (λ x → x) ≡ f
    p i x = transp (λ j → B) i (f (transp (λ j → A) i x))
```

We have that `pathToEquiv (ua f) ≡ f` in two parts. Since equivalences
are pairs, we can reduce this to proving that the function is preserved,
and proving that the equivalence proof is preserved. The latter is easy
since equivalence proofs are propositions.

For the former, Agda basically does all the work for us: All we need to
show is that `transport (λ i → B) (f (transport (λ i → A) x))` is equal
to `f`. This we do using `transp`{.Agda}, which, when `i = i1`, behaves
like the identity function.

```
  isIso.left-inverse iiso = 
    J (λ _ p → ua (pathToEquiv p) ≡ p)
      (ap ua (JRefl (λ x _ → A ≃ x) (_ , idEquiv)) ∙ uaIdEquiv)

univalence-Iso : {A B : Type ℓ} → Iso (A ≡ B) (A ≃ B)
univalence-Iso = pathToEquiv , isEquiv→isIso univalence
```

To show that `pathToEquiv (ua p) ≡ p`, we do path induction on `p`,
reducing this to showing that `ua (pathToEquiv refl) ≡ refl`. By
`JRefl`{.Agda}, we have that `pathToEquiv refl` is `idEquiv`{.Agda},
which means the `uaIdEquiv`{.Agda} lemma proves what we wanted.

## Useful Consequences

One useful consequence of the fact that `(A ≡ B) ≡ (A ≃ B)`[^2] is that
the type of _equivalences_ satisfies the same induction principle as the
type of _equalities_. What I mean, precisely, is that the type `Σ B (A ≃
B)` is contractible, just like the type `Σ B (A ≡ B)`. From this, we get
"equivalence induction": `EquivJ`{.Agda}

```
EquivContr : {ℓ : _} (A : Type ℓ) → isContr (Σ[ B ∈ Type ℓ ] A ≃ B)
isContr.centre (EquivContr A)          = A , _ , idEquiv
isContr.paths (EquivContr A) (B , A≃B) = Σ-Path (ua A≃B) (Σ-Path p q)
  where
    p : _
    p i x = transp (λ i → B) i (fst A≃B (transp (λ j → A) i x))

    q : _
    q = isProp-isEquiv (A≃B .fst) _ _
```

We can use the same decomposition of `J`{.Agda} as transport +
contractibility of singletons for equivalences. Since we have that `(A ,
_ , idEquiv) ≡ (B , eqv)`, we can transport a proof of `P (A , _)` to a
proof of `P (B , eqv)`. Modulo currying, this is exactly the same thing
as `J`{.Agda}.

```
EquivJ : {ℓ ℓ' : _} {A : Type ℓ}
       → (P : (B : Type ℓ) → A ≃ B → Type ℓ')
       → P A (_ , idEquiv)
       → {B : Type ℓ} (e : A ≃ B)
       → P B e
EquivJ P pid eqv =
  subst (λ e → P (e .fst) (e .snd))
        (EquivContr _ .isContr.paths (_ , eqv))
        pid
```

[^2]: Not the fundamental theorem of engineering!

Equivalence induction makes proving several properties about
equivalences almost trivial. For example, if `f` is an equivalence, then
so is its action on paths. 

```
isEquiv→isEquiv-ap : {ℓ : _} {A B : Type ℓ}
                   → (f : A → B) → isEquiv f
                   → {x y : A}
                   → isEquiv (ap f {x = x} {y = y})
isEquiv→isEquiv-ap f eqv =
  EquivJ
    (λ B e → isEquiv (ap (e .fst)))
    idEquiv
    (f , eqv)
```

The proof can be rendered in English roughly as follows:

> Suppose $f : A \to B$ `is an equivalence`{.Agda ident=isEquiv}. We want to
show that, for any choice of $x, y : A$, the map $\mathrm{ap}(f)_{x,y} :
x \equiv y \to f(x) \equiv f(y)$ is an equivalence.
>
> By `induction`{.Agda ident=EquivJ}, it suffices to cover the case
where $B$ is $A$, and $f$ is the identity function.
>
> But then, we have that $\mathrm{ap}(\mathrm{id})$ is [definitionally
equal](agda://1Lab.Path#ap-id) to $\mathrm{id}$, which is known to be
`an equivalence`{.Agda ident=idEquiv}. <span class=qed>$\blacksquare$</span>
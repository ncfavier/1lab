module TT.SOGAT where

open import 1Lab.Prelude hiding (id ; _∘_)

-- the theory of SOGAT signatures as a QIIT
-- ≈ the initial GCwF⁺ with an internal model of DTT⁺
module ToS⁺ where
  data Con : Type
  data Sub : Con → Con → Type
  data Ty  : Con → Type
  data Tm  : ∀ Γ → Ty Γ → Type

  variable
    Γ Δ Θ Ψ : Con
    A B C : Ty Γ
    ρ σ δ ν : Sub Γ Δ
    a a' b b' c c' : Tm Γ A

  infixl 4 _▹_

  data Con where
    []  : Con
    _▹_ : (Γ : Con) → Ty Γ → Con

  private
    _[_]T' : Ty Δ → Sub Γ Δ → Ty Γ
    _[_]t' : Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T')

    _∘'_ : Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
    [∘]T' : A [ δ ∘' σ ]T' ≡ A [ δ ]T' [ σ ]T'

    π₁'  : Sub Γ (Δ ▹ A) → Sub Γ Δ
    π₂'  : (σ : Sub Γ (Δ ▹ A)) → Tm Γ (A [ π₁' σ ]T')

  data Sub where
    id  : Sub Γ Γ
    _∘_ : Sub Δ Θ → Sub Γ Δ → Sub Γ Θ

    idl   : id ∘ σ ≡ σ
    idr   : σ ∘ id ≡ σ
    assoc : (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)

    []  : Sub Γ []
    []η : (σ : Sub Γ []) → [] ≡ σ

    _▹_ : (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T') → Sub Γ (Δ ▹ A)
    π₁  : Sub Γ (Δ ▹ A) → Sub Γ Δ
    π₁β : π₁ (σ ▹ a) ≡ σ

    ▹∘
      : ∀ {Γ Δ Θ} (δ : Sub Δ Γ) (σ : Sub Θ Δ) (A : Ty Γ) {a : Tm Δ (A [ δ ]T')} {b : Tm Θ (A [ δ ∘' σ ]T')}
      → PathP (λ i → Tm Θ ([∘]T' {A = A} {δ = δ} {σ = σ} i)) b (a [ σ ]t')
      → (δ ▹ a) ∘ σ ≡ (δ ∘' σ ▹ b)

    πη  : σ ≡ (π₁' σ ▹ π₂' σ)

    squash : is-set (Sub Γ Δ)

  data Ty where
    _[_]T : Ty Δ → Sub Γ Δ → Ty Γ
    [id]T : A [ id ]T' ≡ A
    [∘]T : A [ δ ∘' σ ]T' ≡ A [ δ ]T' [ σ ]T'

    U   : Ty Γ
    U[] : U [ σ ]T' ≡ U
    -- U[id] : [id]T ≡ U[] {Γ}
    -- U[∘] : (γ : Sub Δ Γ) (δ : Sub Θ Δ) → Square ...
    -- are these coherences actually needed?

    U⁺   : Ty Γ
    U⁺[] : U⁺ [ σ ]T' ≡ U⁺

    El : Tm Γ U → Ty Γ
    El[]
      : (σ : Sub Γ Δ)
      → (p : PathP (λ i → Tm Γ (U[] {σ = σ} i)) (a [ σ ]t') a')
      → El a [ σ ]T' ≡ El a'

    Π : (a : Tm Γ U) (B : Ty (Γ ▹ El a)) → Ty Γ
    Π[]
      : ∀ {t₀}
      → (p : PathP (λ i → Tm Γ (U[] {σ = σ} i)) (a [ σ ]t') a')
      → (p' : PathP (λ i → Tm (Γ ▹ El[] σ p i) ([∘]T' {A = El a} {δ = σ} {σ = π₁' id} (~ i))) (π₂' id) t₀)
      → Π a B [ σ ]T ≡ Π a' (B [ σ ∘' π₁' id ▹ t₀ ]T)

    𝟙   : Ty Γ
    𝟙[] : 𝟙 [ σ ]T' ≡ 𝟙

    Eq   : (A : Ty Γ) (a b : Tm Γ A) → Ty Γ
    Eq[] : Eq A a b [ σ ]T' ≡ Eq (A [ σ ]T') (a [ σ ]t') (b [ σ ]t')

    squash : is-groupoid (Ty Γ)
    -- This is actually too strict: Ty should be 2-truncated because its standard
    -- interpretation is groupoid-presheaves over set-presheaves (same problem for ToS).
    -- Adding all the required coherences is probably intractable and I don't
    -- even know whether the result would be set-truncated.
    -- Things to try:
    -- - don't add any coherences? or just enough for the initial model to be well-behaved?
    -- - define semantics in another way:
    --   - a model of T is a CwR functor from the syntactic category of T to PSh(C)?
    -- - do some kind of higher-order encoding
    -- - adapt the BCDE definition of GATs somehow
    -- - use a set universe of sets? 2LTT?

  _[_]T' = _[_]T
  _∘'_   = _∘_
  π₁'    = π₁
  [∘]T' = [∘]T

  data Tm where
    _[_]t : Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
    [id]t : {a : Tm Γ A} → PathP (λ i → Tm Γ ([id]T {A = A} i)) (a [ id ]t) a
    [∘]t : {a : Tm Γ A} → PathP (λ i → Tm Γ ([∘]T {A = A} {δ = δ} {σ = σ} i)) (a [ δ ∘ σ ]t) (a [ δ ]t [ σ ]t)

    π₂ : (σ : Sub Γ (Δ ▹ A)) → Tm Γ (A [ π₁ σ ]T)
    π₂β : PathP (λ i → Tm Γ (A [ π₁β {σ = σ} {a = a} i ]T)) (π₂ (σ ▹ a)) a

    star : Tm Γ 𝟙
    𝟙η : (a : Tm Γ 𝟙) → a ≡ star

    app   : Tm Γ (Π a B) → Tm (Γ ▹ El a) B
    lam   : Tm (Γ ▹ El a) B → Tm Γ (Π a B)
    lam[]
      : ∀ {t₀ t}
      → (p : PathP (λ i → Tm Γ (U[] {σ = σ} i)) (a [ σ ]t') a')
      → (p' : PathP (λ i → Tm (Γ ▹ El[] σ p i) ([∘]T' {A = El a} {δ = σ} {σ = π₁ id} (~ i))) (π₂' id) t₀)
      → PathP (λ i → Tm Γ (Π[] {a = a} {B = B} p p' i))
          (lam t [ σ ]t)
          (lam (t [ σ ∘ π₁ id ▹ t₀ ]t))
    Πβ    : app (lam a) ≡ a
    Πη    : lam (app a) ≡ a

    inc : Tm Γ U⁺ → Tm Γ U
    inc[]
      : PathP (λ i → Tm Γ (U⁺[] {σ = σ} i)) (a [ σ ]t') b
      → PathP (λ i → Tm Γ (U[] {σ = σ} i)) (inc a [ σ ]t') (inc b)

    rfl : Tm Γ (Eq A a a)
    reflect : Tm Γ (Eq A a b) → a ≡ b
    Eq-prop : (x y : Tm Γ (Eq A a b)) → x ≡ y

    π⁺ : (a⁺ : Tm Γ U⁺) (b : Tm (Γ ▹ El (inc a⁺)) U) → Tm Γ U
    π⁺[]
      : ∀ {a⁺ b a⁺' b' t₀}
      → (p : PathP (λ i → Tm Γ (U⁺[] {σ = σ} i)) (a⁺ [ σ ]t') a⁺')
      → PathP (λ i → Tm (Γ ▹ El[] σ (inc[] p) i) ([∘]T' {A = El (inc a⁺)} {δ = σ} {σ = π₁' id} (~ i))) (π₂' id) t₀
      → PathP (λ i → Tm (Γ ▹ El (inc a⁺')) (U[] {σ = σ ∘ π₁ id ▹ t₀} i)) (b [ σ ∘ π₁ id ▹ t₀ ]t') b'
      → PathP (λ i → Tm Γ (U[] {σ = σ} i)) (π⁺ a⁺ b [ σ ]t') (π⁺ a⁺' b')

    app⁺  : ∀ {a⁺ b} → Tm Γ (El (π⁺ a⁺ b)) → Tm (Γ ▹ El (inc a⁺)) (El b)
    lam⁺  : ∀ {a⁺ b} → Tm (Γ ▹ El (inc a⁺)) (El b) → Tm Γ (El (π⁺ a⁺ b))
    lam⁺[]
      : ∀ {a⁺ b a⁺' b' t₀ t t'}
      → (p : PathP (λ i → Tm Γ (U⁺[] {σ = σ} i)) (a⁺ [ σ ]t') a⁺')
      → (p' : PathP (λ i → Tm (Γ ▹ El[] σ (inc[] p) i) ([∘]T' {A = El (inc a⁺)} {δ = σ} {σ = π₁' id} (~ i))) (π₂' id) t₀)
      → (p'' : PathP (λ i → Tm (Γ ▹ El (inc a⁺')) (U[] {σ = σ ∘ π₁ id ▹ t₀} i)) (b [ σ ∘ π₁ id ▹ t₀ ]t') b')
      → PathP (λ i → Tm (Γ ▹ El (inc a⁺')) (El[] _ p'' i)) (t [ σ ∘ π₁ id ▹ t₀ ]t') t'
      → PathP (λ i → Tm Γ (El[] σ (π⁺[] p p' p'') i)) (lam⁺ t [ σ ]t') (lam⁺ t')
    π⁺β    : app⁺ (lam⁺ a) ≡ a
    π⁺η    : lam⁺ (app⁺ a) ≡ a

    squash : is-set (Tm Γ A)

  _[_]t' = _[_]t
  π₂'    = π₂

  El⁺ : Tm Γ U⁺ → Ty Γ
  El⁺ a = El (inc a)

  wk : Sub (Γ ▹ A) Γ
  wk = π₁ id

  vz : Tm (Γ ▹ A) (A [ wk ]T)
  vz = π₂ id

  _⇒_ : Tm Γ U → Ty Γ → Ty Γ
  _⇒_ = λ a B → Π a (B [ wk ]T)

SOGAT : Type
SOGAT = ToS⁺.Con

SOGAT→ : SOGAT → SOGAT → Type
SOGAT→ = ToS⁺.Sub

module PCF.ExtE.TyDeriv where

open import Prelude hiding (_⊆_)
open import Data.Unit
open import Data.Empty
open import Data.Dec
open import Data.String
open import Data.List
open import Structures.IdentitySystem hiding (J)

open import Interlude
open import PCF.ExtE.TyTerm

infix  4  _∋_⦂_
infix  4  _⊢_⦂_
infixl 5 _,_⦂_

-- context

data Ctx : 𝒰 where
  ∅    : Ctx
  _,_⦂_ : Ctx → Id → Ty → Ctx

_＋＋_ : Ctx → Ctx → Ctx
Γ ＋＋ ∅ = Γ
Γ ＋＋ (Δ , x ⦂ A) = Γ ＋＋ Δ , x ⦂ A

Context-≃ : Iso Ctx (List (Id × Ty))
Context-≃ = ff , iso gg ri li
  where
  ff : Ctx → List (Id × Ty)
  ff ∅          = []
  ff (c , i ⦂ t) = (i , t) ∷ ff c
  gg : List (Id × Ty) → Ctx
  gg []            = ∅
  gg ((i , t) ∷ l) = gg l , i ⦂ t
  ri : gg is-right-inverse-of ff
  ri []            = refl
  ri ((i , t) ∷ l) = ap ((i , t) ∷_) (ri l)
  li : gg is-left-inverse-of ff
  li ∅          = refl
  li (c , i ⦂ t) = ap (_, i ⦂ t) (li c)

-- lookup and context inclusion

data _∋_⦂_ : Ctx → Id → Ty → 𝒰 where

  here : ∀ {Γ x y A B}
       → x ＝ y
       → A ＝ B
         ------------------
       → Γ , y ⦂ B ∋ x ⦂ A

  there : ∀ {Γ x y A B}
        → x ≠ y
        → Γ ∋ x ⦂ A
          ------------------
        → Γ , y ⦂ B ∋ x ⦂ A

-- as we already have ids, the indices hold no additional information
∋-is-prop : ∀ {Γ x A}
           → is-prop (Γ ∋ x ⦂ A)
∋-is-prop {Γ} {x} {A} = is-prop-η go
  where
  go : ∀ {Γ} → (p q : Γ ∋ x ⦂ A) → p ＝ q
  go (here ei₁ et₁) (here ei₂ et₂) = ap² here (is-prop-β (is-of-hlevel-β 0 hlevel! _ _) ei₁ ei₂)
                                              (is-prop-β (is-of-hlevel-β 0 Ty-is-set _ _) et₁ et₂)
  go (here ei₁ et₁) (there ne₂ i₂) = absurd (ne₂ ei₁)
  go (there ne₁ i₁) (here ei₂ et₂) = absurd (ne₁ ei₂)
  go (there ne₁ i₁) (there ne₂ i₂) = ap² there (is-prop-β hlevel! ne₁ ne₂)
                                               (go i₁ i₂)

∋-unique : ∀ {Γ x A B}
          → Γ ∋ x ⦂ A
          → Γ ∋ x ⦂ B
          → A ＝ B
∋-unique (here ei₁ et₁) (here ei₂ et₂) = et₁ ∙ sym et₂
∋-unique (here ei₁ et₁) (there ne₂ i₂) = absurd (ne₂ ei₁)
∋-unique (there ne₁ i₁) (here ei₂ et₂) = absurd (ne₁ ei₂)
∋-unique (there ne₁ i₁) (there ne₂ i₂) = ∋-unique i₁ i₂

∅-empty : ∀ {x A} → ¬ (∅ ∋ x ⦂ A)
∅-empty ()

_⊆_ : Ctx → Ctx → 𝒰
_⊆_ Γ₁ Γ₂ = ∀ t i → Γ₁ ∋ i ⦂ t → Γ₂ ∋ i ⦂ t

⊆-∅ : ∀ {Γ} → ∅ ⊆ Γ
⊆-∅ t i ()

⊆-ext : ∀ {Γ₁ Γ₂ x A} → Γ₁ ⊆ Γ₂ → (Γ₁ , x ⦂ A) ⊆ (Γ₂ , x ⦂ A)
⊆-ext {x} {A} sub  B  y (here ei et)  = here ei et
⊆-ext         sub  B  y (there ne H1) = there ne (sub B y H1)

⊆-shadow : ∀ {Γ x A B} → (Γ , x ⦂ A , x ⦂ B) ⊆ (Γ , x ⦂ B)
⊆-shadow t i (here ei et)            = here ei et
⊆-shadow t i (there i≠i (here ei _)) = absurd (i≠i ei)
⊆-shadow t i (there i≠x (there _ p)) = there i≠x p

⊆-exch : ∀ {Γ x y A B} → x ≠ y → (Γ , y ⦂ B , x ⦂ A) ⊆ (Γ , x ⦂ A , y ⦂ B)
⊆-exch x≠y t i (here ei et)              = there (λ e → x≠y (sym ei ∙ e)) (here ei et)
⊆-exch x≠y t i (there x (here ei et))    = here ei et
⊆-exch x≠y t i (there i≠z (there i≠y p)) = there i≠y (there i≠z p)

-- typing judgement

data _⊢_⦂_ : Ctx → Term → Ty → 𝒰 where

  -- Axiom
  ⊢` : ∀ {Γ x A}
      → Γ ∋ x ⦂ A
        -----------
      → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B T}
      → A ＝ T
      → Γ , x ⦂ A ⊢ N ⦂ B
        -------------------
      → Γ ⊢ ƛ x ⦂ T ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _⊢·_ : ∀ {Γ L M A B}
        → Γ ⊢ L ⦂ A ⇒ B
        → Γ ⊢ M ⦂ A
          -------------
        → Γ ⊢ L · M ⦂ B

  -- Y-combinator
  ⊢Y : ∀ {Γ M A}
    → Γ ⊢ M ⦂ A ⇒ A
      ---------------
    → Γ ⊢ Y M ⦂ A

  -- constant
  ⊢＃ : ∀ {Γ n}
        --------------
       → Γ ⊢ ＃ n ⦂ 𝓝

  -- successor
  ⊢𝓈 : ∀ {Γ M}
      → Γ ⊢ M ⦂ 𝓝
        --------------
      → Γ ⊢ 𝓈 M ⦂ 𝓝

  -- predecessor
  ⊢𝓅 : ∀ {Γ M}
      → Γ ⊢ M ⦂ 𝓝
        --------------
      → Γ ⊢ 𝓅 M ⦂ 𝓝

  -- if-zero
  ⊢?⁰ : ∀ {Γ L M N A}
    → Γ ⊢ L ⦂ 𝓝
    → Γ ⊢ M ⦂ A
    → Γ ⊢ N ⦂ A
      -------------------
    → Γ ⊢ ?⁰ L ↑ M ↓ N ⦂ A

-- typing uniqueness

⊢-unique : ∀ {Γ M A B}
          → Γ ⊢ M ⦂ A
          → Γ ⊢ M ⦂ B
          → A ＝ B
⊢-unique {M = .(` x)}          {A}        {B}         (⊢` {x} i₁)                   (⊢` i₂)       = ∋-unique i₁ i₂
⊢-unique {Γ} {M = .(ƛ x ⦂ T ⇒ N)}  {.(A₁ ⇒ B₁)} {.(A₂ ⇒ B₂)} (⊢ƛ {x} {N} {A = A₁} {B = B₁} {T} e₁ t₁) (⊢ƛ {A = A₂} {B = B₂} e₂ t₂) =
  let a12 = e₁ ∙ sym e₂ in
  ap² _⇒_ a12 (⊢-unique (subst (λ q → Γ , x ⦂ q ⊢ N ⦂ B₁) a12 t₁) t₂)
⊢-unique {M = .(_ · _)}        {A}        {B}         (x ⊢· x₁)                     (y ⊢· y₁)     = snd $ ⇒-inj $ ⊢-unique x y
⊢-unique {M = .(Y _)}          {A}        {B}         (⊢Y x)                        (⊢Y y)        = fst $ ⇒-inj $ ⊢-unique x y
⊢-unique {M = .(＃ _)}          {.𝓝}      {.𝓝}       ⊢＃                            ⊢＃           = refl
⊢-unique {M = .(𝓈 _)}          {.𝓝}     {.𝓝}         (⊢𝓈 x)                       (⊢𝓈 y)        = refl
⊢-unique {M = .(𝓅 _)}          {.𝓝}     {.𝓝}        (⊢𝓅 x)                        (⊢𝓅 y)        = refl
⊢-unique {M =.(?⁰ _ ↑ _ ↓ _)} {A}       {B}          (⊢?⁰ x x₁ x₂)                 (⊢?⁰ y y₁ y₂) = ⊢-unique x₁ y₁

-- derivations are props

⊢-is-prop : ∀ {Γ M A}
          → is-prop (Γ ⊢ M ⦂ A)
⊢-is-prop {Γ} {M} {A} = is-prop-η go
  where
  go : ∀ {Γ M A} → (p q : Γ ⊢ M ⦂ A) → p ＝ q
  go (⊢` x) (⊢` y) = ap ⊢` (is-prop-β ∋-is-prop x y)
  go (⊢ƛ e p) (⊢ƛ e₂ q) = ap² ⊢ƛ (is-prop-β (is-of-hlevel-β 0 Ty-is-set _ _) e e₂) (go p q)
  go {Γ} {A} (_⊢·_ {L} {M} p p₁) (q ⊢· q₁) =
    J (λ T eT → (q¹ : Γ ⊢ L ⦂ T ⇒ A)
              → (q² : Γ ⊢ M ⦂ T)
              → (p ⊢· p₁) ＝ (q¹ ⊢· q²))
      (λ q¹ q² → ap² _⊢·_ (go p q¹) (go p₁ q²))
      (⊢-unique p₁ q₁) q q₁
  go (⊢Y p) (⊢Y q) = ap ⊢Y (go p q)
  go ⊢＃ ⊢＃ = refl
  go (⊢𝓈 p) (⊢𝓈 q) = ap ⊢𝓈 (go p q)
  go (⊢𝓅 p) (⊢𝓅 q) = ap ⊢𝓅 (go p q)
  go (⊢?⁰ p p₁ p₂) (⊢?⁰ q q₁ q₂) = ap³-simple ⊢?⁰ (go p q) (go p₁ q₁) (go p₂ q₂)

-- weakening / renaming

weaken : ∀ {Γ₁ Γ₂ t T} → Γ₁ ⊆ Γ₂ → Γ₁ ⊢ t ⦂ T → Γ₂ ⊢ t ⦂ T
weaken {t = .(` x)}   {T}              sub (⊢` {x} p)                  =
  ⊢` (sub T x p)
weaken {t = .(ƛ x ⦂ T ⇒ N)} {T = .(A ⇒ B)} sub (⊢ƛ {x} {N} {A} {B} {T} e ⊢N)     =
  ⊢ƛ e (weaken (⊆-ext sub) ⊢N)
weaken {t = .(L · M)}                  sub (_⊢·_ {L} {M} ⊢L ⊢M)       =
  (weaken sub ⊢L) ⊢· (weaken sub ⊢M)
weaken {t = .(Y M)}                    sub (⊢Y {M} ⊢M)                 =
  ⊢Y (weaken sub ⊢M)
weaken {t = .(＃ n)}                    sub (⊢＃ {n})                   =
  ⊢＃ {n = n}
weaken {t = .(𝓈 M)}                    sub (⊢𝓈 {M} ⊢M)                 =
  ⊢𝓈 (weaken sub ⊢M)
weaken {t = .(𝓅 M)}                    sub (⊢𝓅 {M} ⊢M)                 =
  ⊢𝓅 (weaken sub ⊢M)
weaken {t = ?⁰ L ↑ M ↓ N}              sub (⊢?⁰ {L} {M} {N} ⊢L ⊢M ⊢N) =
  ⊢?⁰ (weaken sub ⊢L) (weaken sub ⊢M) (weaken sub ⊢N)

weaken-∅ : ∀ {t T} Γ → ∅ ⊢ t ⦂ T → Γ ⊢ t ⦂ T
weaken-∅ Γ H0 = weaken ⊆-∅ H0

drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = weaken ⊆-shadow ⊢M

swap : ∀ {Γ x y M A B C}
  → x ≠ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≠y ⊢M = weaken (⊆-exch x≠y) ⊢M

-- substitution preserves typing

subst-ty : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B
subst-ty {Γ} {x = y} {V}     ⊢V (⊢` {x} (here et ei)) with x ≟ y
... | yes _ = weaken-∅ Γ (subst (∅ ⊢ V ⦂_) (sym ei) ⊢V)
... | no ctra = absurd (ctra et)
subst-ty     {x = y}         ⊢V (⊢` {x} (there ne ix)) with x ≟ y
... | yes prf = absurd (ne prf)
... | no ctra = ⊢` ix
subst-ty {Γ} {x = y}     {A} ⊢V (⊢ƛ {x} {N} {A = A⁰} {B}  e ⊢N) with x ≟ y
... | yes prf = ⊢ƛ e (drop (subst (λ q → Γ , q ⦂ A , x ⦂ A⁰ ⊢ N ⦂ B) (sym prf) ⊢N))
... | no ctra = ⊢ƛ e (subst-ty ⊢V (swap ctra ⊢N))
subst-ty                     ⊢V (⊢M ⊢· ⊢N)           = (subst-ty ⊢V ⊢M) ⊢· (subst-ty ⊢V ⊢N)
subst-ty                     ⊢V (⊢Y ⊢N)               = ⊢Y (subst-ty ⊢V ⊢N)
subst-ty                     ⊢V ⊢＃                    = ⊢＃
subst-ty                     ⊢V (⊢𝓈 ⊢N)               = ⊢𝓈 (subst-ty ⊢V ⊢N)
subst-ty                     ⊢V (⊢𝓅 ⊢N)               = ⊢𝓅 (subst-ty ⊢V ⊢N)
subst-ty                     ⊢V (⊢?⁰ ⊢L ⊢M ⊢N )      = ⊢?⁰ (subst-ty ⊢V ⊢L) (subst-ty ⊢V ⊢M) (subst-ty ⊢V ⊢N)

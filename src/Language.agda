module Language where

open import Prelude
open import Correspondences.Base using (Corr²)
open import Data.Empty
open import Data.Dec
open import Data.String
open import Data.List

private variable
  ℓ : Level

-- relation properties

ℛ : 𝒰 ℓ → 𝒰 (ℓsuc ℓ)
ℛ {ℓ} X = Corr² ℓ (X , X)

normal-form : {X : 𝒰 ℓ} → ℛ X → X → 𝒰 ℓ
normal-form {X} R x = ¬ Σ[ x′ ꞉ X ] (R x x′)

deterministic : {X : 𝒰 ℓ} → ℛ X → 𝒰 ℓ
deterministic {X} R =  ∀ (x y1 y2 : X) → R x y1 → R x y2 → y1 ＝ y2

-- names

Id : 𝒰
Id = String

infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  2 _—↠_
infix  3 _∎ᵣ
infix  4 _—→_
infix  4  _∋_⦂_
infix  4  _⊢_⦂_
infix  5 ƛ_⇒_
infixl 5 _,_⦂_
infixl 7 _·_
infixr 7 _⇒_
infix  9 `_
infix  9 _[_:=_]

-- types

data Ty : 𝒰 where
  _⇒_ : Ty → Ty → Ty
  𝟙   : Ty

-- terms

data Term : 𝒰 where
  `_   : Id → Term
  ƛ_⇒_ : Id → Term → Term
  _·_  : Term → Term → Term

-- TODO terms form a set

-- substitution

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _        = V
... | no  _        = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _        = ƛ x ⇒ N
... | no  _        = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ] = L [ y := V ] · M [ y := V ]

-- values

data Value : Term → 𝒰 where
  V-ƛ : ∀ {x N} → Value (ƛ x ⇒ N)

-- reduction step

data _—→_ : Term → Term → 𝒰 where
  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

-- step RTC

data _—↠_ : Term → Term → 𝒰 where
  _∎ᵣ : ∀ M
      ---------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

-- normal form

nf : Term → 𝒰
nf = normal-form _—→_

nf-is-prop : ∀ {t} → is-prop (nf t)
nf-is-prop = ¬-is-prop

value-nf : ∀ {t} → Value t → nf t
value-nf {t = .(ƛ x ⇒ N)} (V-ƛ {x} {N}) (M , ())

-- context

data Context : 𝒰 where
  ∅     : Context
  _,_⦂_ : Context → Id → Ty → Context

Context-≃ : Iso Context (List (Id × Ty))
Context-≃ = ff , iso gg ri li
  where
  ff : Context → List (Id × Ty)
  ff ∅          = []
  ff (c , i ⦂ t) = (i , t) ∷ ff c
  gg : List (Id × Ty) → Context
  gg []            = ∅
  gg ((i , t) ∷ l) = gg l , i ⦂ t
  ri : gg is-right-inverse-of ff
  ri []            = refl
  ri ((i , t) ∷ l) = ap ((i , t) ∷_) (ri l)
  li : gg is-left-inverse-of ff
  li ∅          = refl
  li (c , i ⦂ t) = ap (_, i ⦂ t) (li c)

-- lookup and context inclusion

data _∋_⦂_ : Context → Id → Ty → 𝒰 where

  here : ∀ {Γ x A}
      ------------------
       → Γ , x ⦂ A ∋ x ⦂ A

  there : ∀ {Γ x y A B}
        → x ≠ y
        → Γ ∋ x ⦂ A
          ------------------
        → Γ , y ⦂ B ∋ x ⦂ A

∅-empty : ∀ {x A} → ¬ (∅ ∋ x ⦂ A)
∅-empty ()

_⊆_ : Context → Context → 𝒰
_⊆_ Γ₁ Γ₂ = ∀ t i → Γ₁ ∋ i ⦂ t → Γ₂ ∋ i ⦂ t

⊆-∅ : ∀ {Γ} → ∅ ⊆ Γ
⊆-∅ t i ()

⊆-ext : ∀ {Γ₁ Γ₂ x A} → Γ₁ ⊆ Γ₂ → (Γ₁ , x ⦂ A) ⊆ (Γ₂ , x ⦂ A)
⊆-ext {x} {A} sub .A .x  here         = here
⊆-ext         sub  t  i (there ne H1) = there ne (sub t i H1)

⊆-shadow : ∀ {Γ x A B} → (Γ , x ⦂ A , x ⦂ B) ⊆ (Γ , x ⦂ B)
⊆-shadow t i here = here
⊆-shadow t i (there i≠i here) = absurd (i≠i refl)
⊆-shadow t i (there i≠x (there _ p)) = there i≠x p

⊆-exch : ∀ {Γ x y A B} → x ≠ y → (Γ , y ⦂ B , x ⦂ A) ⊆ (Γ , x ⦂ A , y ⦂ B)
⊆-exch x≠y t i  here                     = there x≠y here
⊆-exch x≠y t i (there x here)            = here
⊆-exch x≠y t i (there i≠z (there i≠y p)) = there i≠y (there i≠z p)

-- typing judgement

data _⊢_⦂_ : Context → Term → Ty → 𝒰 where

  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _⊢·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

-- weakening / renaming

weaken : ∀ {Γ₁ Γ₂ t T} → Γ₁ ⊆ Γ₂ → Γ₁ ⊢ t ⦂ T → Γ₂ ⊢ t ⦂ T
weaken {t = .(` x)}   {T}     sub (⊢` {x} p)               = ⊢` (sub T x p)
weaken {t = .(ƛ x ⇒ N)} {T = .(A ⇒ B)} sub (⊢ƛ {x} {N} {A} {B} ⊢N) =
  ⊢ƛ (weaken (⊆-ext sub) ⊢N)
weaken {t = .(L · M)}           sub (_⊢·_ {L} {M} ⊢L ⊢M) =
  (weaken sub ⊢L) ⊢· (weaken sub ⊢M)

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
subst-ty {Γ} {x = y}     ⊢V (⊢` {x} here) with x ≟ y
... | yes _   = weaken-∅ Γ ⊢V
... | no  x≠y = absurd (x≠y refl)
subst-ty {x = y}         ⊢V (⊢` {x} (there x≠y ∋x)) with x ≟ y
... | yes eq  = absurd (x≠y eq)
... | no  _   = ⊢` ∋x
subst-ty {Γ} {x = y} {A} ⊢V (⊢ƛ {x} {N} {A = C} {B} ⊢N) with x ≟ y
... | yes eq  = ⊢ƛ (drop (subst (λ n → Γ , n ⦂ A , x ⦂ C ⊢ N ⦂ B) (sym eq) ⊢N))
... | no  x≠y = ⊢ƛ (subst-ty ⊢V (swap x≠y ⊢N))
subst-ty                 ⊢V (⊢L ⊢· ⊢M) = (subst-ty ⊢V ⊢L) ⊢· (subst-ty ⊢V ⊢M)

-- preservation

preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve (⊢` ())
preserve (⊢ƛ ⊢N)           ()
preserve (⊢L ⊢· ⊢M)       (ξ-·₁ L—→L′)    = (preserve ⊢L L—→L′) ⊢· ⊢M
preserve (⊢L ⊢· ⊢M)       (ξ-·₂ VL M—→M′) = ⊢L ⊢· (preserve ⊢M M—→M′)
preserve ((⊢ƛ ⊢N) ⊢· ⊢V) (β-ƛ VV)        = subst-ty ⊢V ⊢N

-- context invariance

-- appears free in
data afi : String → Term → 𝒰 where
  afi-var  : ∀ {x} → afi x (` x)
  afi-appl : ∀ {x M N} → afi x M → afi x (M · N)
  afi-appr : ∀ {x M N} → afi x N → afi x (M · N)
  afi-abs  : ∀ {x y N} → x ≠ y → afi x N → afi x (ƛ y ⇒ N)

closed : Term → 𝒰
closed t = ∀ i → ¬ afi i t

free-in-ctx : ∀ {w M A Γ} → afi w M → Γ ⊢ M ⦂ A → Σ[ B ꞉ Ty ] (Γ ∋ w ⦂ B)
free-in-ctx afi-var       (⊢` {A} p) = A , p
free-in-ctx {w} (afi-abs ne a) (⊢ƛ {x} ⊢N) with (free-in-ctx a ⊢N)
... | B , here = absurd (ne refl)
... | B , there _ p = B , p
free-in-ctx (afi-appl a) (⊢L ⊢· ⊢M) = free-in-ctx a ⊢L
free-in-ctx (afi-appr a) (⊢L ⊢· ⊢M) = free-in-ctx a ⊢M

∅⊢-closed : ∀ {M A} → ∅ ⊢ M ⦂ A → closed M
∅⊢-closed ⊢M i a with (free-in-ctx a ⊢M)
... | (B , p) = ∅-empty p

-- determinism

step-det : deterministic _—→_
step-det .(L · M)          .(L₁ · M)         .(L₂ · M)        (ξ-·₁ {L} {L′ = L₁} {M} LL₁)       (ξ-·₁ {L′ = L₂} LL₂)       =
  ap (_· M) (step-det L L₁ L₂ LL₁ LL₂)
step-det .(L · M₁)         .(L′ · M₁)        .(L · M₂)        (ξ-·₁ {L} {L′} {M = M₁} LL′)       (ξ-·₂ {M′ = M₂} VL M₁₂)    =
  absurd (value-nf VL (L′ , LL′))
step-det .(L · M)          .(L · M′)         .(L′ · M)        (ξ-·₂ {V = L} {M} {M′} VL MM′)     (ξ-·₁ {L′} LL′)            =
  absurd (value-nf VL (L′ , LL′))
step-det .(L · M)          .(L · M₁)         .(L · M₂)        (ξ-·₂ {V = L} {M} {M′ = M₁} _ MM₁) (ξ-·₂ {M′ = M₂} _ MM₂)     =
  ap (L ·_) (step-det M M₁ M₂ MM₁ MM₂)
step-det .((ƛ x ⇒ N) · M₁) .((ƛ x ⇒ N) · M₂) .(N [ x := M₁ ]) (ξ-·₂ {M′ = M₂} _ M₁₂)             (β-ƛ {x} {N} {V = M₁} VM₁) =
  absurd (value-nf VM₁ (M₂ , M₁₂))
step-det .((ƛ x ⇒ N) · L)  .(N [ x := L ])   .((ƛ x ⇒ N) · M) (β-ƛ {x} {N} {V = L} VL)           (ξ-·₂ {M′ = M} _ LM)       =
  absurd (value-nf VL (M , LM))
step-det .((ƛ x ⇒ N) · V)  .(N [ x := V ])   .(N [ x := V ])  (β-ƛ {x} {N} {V} VV)               (β-ƛ _)                    =
  refl


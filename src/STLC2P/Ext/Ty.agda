module STLC2P.Ext.Ty where

open import Prelude hiding (_⊆_)
open import Data.Empty
open import Data.Dec
open import Data.String
open import Data.List

open import STLC2P.Ext.Term

infix  4  _∋_⦂_
infix  4  _⊢_⦂_
infixl 5 _,_⦂_
infixr 7 _⇒_

-- types

data Ty : 𝒰 where
  _⇒_ : Ty → Ty → Ty
  _𝕩_ : Ty → Ty → Ty
  𝟚   : Ty

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

  -- true
  ⊢𝓉 : ∀ {Γ}
      ----------
    → Γ ⊢ 𝓉 ⦂ 𝟚

  -- false
  ⊢𝒻 : ∀ {Γ}
      ----------
    → Γ ⊢ 𝒻 ⦂ 𝟚

  -- if
  ⊢⁇ : ∀ {Γ L M N A}
    → Γ ⊢ L ⦂ 𝟚
    → Γ ⊢ M ⦂ A
    → Γ ⊢ N ⦂ A
      -------------------
    → Γ ⊢ ⁇ L ↑ M ↓ N ⦂ A

  -- pair
  ⊢〈〉 : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A
    → Γ ⊢ M ⦂ B
      ---------------------
    → Γ ⊢ 〈 L ⹁ M 〉 ⦂ A 𝕩 B

  -- fst
  ⊢⇀₁ : ∀ {Γ L A B}
    → Γ ⊢ L ⦂ A 𝕩 B
      -------------
    → Γ ⊢ L ⇀₁ ⦂ A

  -- snd
  ⊢⇀₂ : ∀ {Γ L A B}
    → Γ ⊢ L ⦂ A 𝕩 B
      -------------
    → Γ ⊢ L ⇀₂ ⦂ B

¬ƛ⦂𝟚 : ∀ {x N} → ¬ (∅ ⊢ ƛ x ⇒ N ⦂ 𝟚)
¬ƛ⦂𝟚 ()

¬〈〉⦂𝟚 : ∀ {L M} → ¬ (∅ ⊢ 〈 L ⹁ M 〉 ⦂ 𝟚)
¬〈〉⦂𝟚 ()

-- weakening / renaming

weaken : ∀ {Γ₁ Γ₂ t T} → Γ₁ ⊆ Γ₂ → Γ₁ ⊢ t ⦂ T → Γ₂ ⊢ t ⦂ T
weaken {t = .(` x)}         {T}         sub (⊢` {x} p)              =
  ⊢` (sub T x p)
weaken {t = .(ƛ x ⇒ N)}     {.(A ⇒ B)}  sub (⊢ƛ {x} {N} {A} {B} ⊢N) =
  ⊢ƛ (weaken (⊆-ext sub) ⊢N)
weaken {t = .(L · M)}              sub (_⊢·_ {L} {M} ⊢L ⊢M)   =
  (weaken sub ⊢L) ⊢· (weaken sub ⊢M)
weaken {t = .𝓉}             {.𝟚}       sub  ⊢𝓉                     =
  ⊢𝓉
weaken {t = .𝒻}             {.𝟚}       sub  ⊢𝒻                    =
  ⊢𝒻
weaken {t = .(⁇ _ ↑ _ ↓ _)} {T}         sub (⊢⁇ ⊢L ⊢M ⊢N)        =
  ⊢⁇ (weaken sub ⊢L) (weaken sub ⊢M) (weaken sub ⊢N)
weaken {t = .(〈 _ ⹁ _ 〉)}     {.(_ 𝕩 _)} sub  (⊢〈〉 ⊢L ⊢M)           =
  ⊢〈〉 (weaken sub ⊢L) (weaken sub ⊢M)
weaken {t = .(_ ⇀₁)}        {T}        sub  (⊢⇀₁ {B} ⊢L)          =
  ⊢⇀₁ (weaken sub ⊢L)
weaken {t = .(_ ⇀₂)}        {T}        sub  (⊢⇀₂ {A} ⊢L)          =
  ⊢⇀₂ (weaken sub ⊢L)

weaken-∅ : ∀ {t T} Γ → ∅ ⊢ t ⦂ T → Γ ⊢ t ⦂ T
weaken-∅ Γ H0 = weaken ⊆-∅ H0

dropᵧ : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
dropᵧ {Γ} {x} {M} {A} {B} {C} ⊢M = weaken ⊆-shadow ⊢M

swapᵧ : ∀ {Γ x y M A B C}
  → x ≠ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swapᵧ {Γ} {x} {y} {M} {A} {B} {C} x≠y ⊢M = weaken (⊆-exch x≠y) ⊢M

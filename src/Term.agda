module Term where

open import Prelude
open import Data.Empty
open import Data.Dec
open import Data.String
open import Rel

-- names

Id : 𝒰
Id = String

infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  2 _—↠_
infix  3 _∎ᵣ
infix  4 _—→_
infix  5 ƛ_⇒_
infixl 7 _·_
infix  9 `_
infix  9 _[_:=_]

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

-- context invariance

-- appears free in
data afi : String → Term → 𝒰 where
  afi-var  : ∀ {x} → afi x (` x)
  afi-appl : ∀ {x M N} → afi x M → afi x (M · N)
  afi-appr : ∀ {x M N} → afi x N → afi x (M · N)
  afi-abs  : ∀ {x y N} → x ≠ y → afi x N → afi x (ƛ y ⇒ N)

closed : Term → 𝒰
closed t = ∀ i → ¬ afi i t

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

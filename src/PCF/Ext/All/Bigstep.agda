{-# OPTIONS --guarded #-}
module PCF.Ext.All.Bigstep where

open import Prelude
open import Data.Empty
open import Data.Nat hiding (_·_)
open import Data.String

open import Later
open import PCF.Ext.TyTerm
open import PCF.Ext.Subst

-- Step-indexed Big-Step Operational Semantics (guarded form)
-- Inspired by Escardo'99

Q·-rec : (Term → ℕ → (Val → ℕ → 𝒰) → ▹ 𝒰)
       → Term → (Val → ℕ → 𝒰)
       → Val → ℕ → 𝒰
Q·-rec ⇓▹ _ _ (v-ƛ _ _ _)  zero   = ⊥
Q·-rec ⇓▹ s Q (v-ƛ x A t) (suc m) = ▸ ⇓▹ (t [ x := s ]) m Q
Q·-rec ⇓▹ _ _ (v-＃ _)     _      = ⊥

Q𝓈 : (Val → ℕ → 𝒰)
   → Val → ℕ → 𝒰
Q𝓈 Q (v-＃ _)     zero   = ⊥
Q𝓈 Q (v-＃ n)    (suc l) = ▹ Q (v-＃ (suc n)) l
Q𝓈 Q (v-ƛ _ _ _)  l      = ⊥

-- Paviotti'16 2.3.1 says this should guard against n=0 but then it's inconsistent with small-step
Q𝓅 : (Val → ℕ → 𝒰)
   → Val → ℕ → 𝒰
Q𝓅 Q (v-＃ _)     zero   = ⊥
Q𝓅 Q (v-＃ n)    (suc l) = ▹ Q (v-＃ (pred n)) l
Q𝓅 Q (v-ƛ _ _ _)  _      = ⊥

Q?-rec : (Term → ℕ → (Val → ℕ → 𝒰) → ▹ 𝒰)
       → Term → Term → (Val → ℕ → 𝒰)
       → Val → ℕ → 𝒰
Q?-rec ⇓▹ _ _ _ (v-＃  _)       zero   = ⊥
Q?-rec ⇓▹ s _ Q (v-＃  zero)   (suc m) = ▸ ⇓▹ s m Q
Q?-rec ⇓▹ _ t Q (v-＃ (suc _)) (suc m) = ▸ ⇓▹ t m Q
Q?-rec ⇓▹ _ _ _ (v-ƛ _ _ _)     _      = ⊥

⇓⁅⁆-case : (Term → ℕ → (Val → ℕ → 𝒰) → ▹ 𝒰)
        → Term → ℕ → (Val → ℕ → 𝒰) → 𝒰
⇓⁅⁆-case ⇓▹ (` _)           _      _ = ⊥
⇓⁅⁆-case ⇓▹ (ƛ x ⦂ A ⇒ t)   k      Q = Q (v-ƛ x A t) k
⇓⁅⁆-case ⇓▹ (r · s)         k      Q = ⇓⁅⁆-case ⇓▹ r k (Q·-rec ⇓▹ s Q)
⇓⁅⁆-case ⇓▹ (Y _)           zero   _ = ⊥
⇓⁅⁆-case ⇓▹ (Y t)          (suc k) Q = ▸ ⇓▹ (t · Y t) k Q
⇓⁅⁆-case ⇓▹ (＃ n)          k      Q = Q (v-＃ n) k
⇓⁅⁆-case ⇓▹ (𝓈 t)           k      Q = ⇓⁅⁆-case ⇓▹ t k (Q𝓈 Q)
⇓⁅⁆-case ⇓▹ (𝓅 t)           k      Q = ⇓⁅⁆-case ⇓▹ t k (Q𝓅 Q)
⇓⁅⁆-case ⇓▹ (?⁰ r ↑ s ↓ t)  k      Q = ⇓⁅⁆-case ⇓▹ r k (Q?-rec ⇓▹ s t Q)

⇓⁅⁆-distr : ▹ (Term → ℕ → (Val → ℕ → 𝒰) → 𝒰)
           → Term → ℕ → (Val → ℕ → 𝒰) → ▹ 𝒰
⇓⁅⁆-distr f t n Q = f ⊛ next t ⊛ next n ⊛ next Q

⇓⁅⁆-body : ▹ (Term → ℕ → (Val → ℕ → 𝒰) → 𝒰)
           → Term → ℕ → (Val → ℕ → 𝒰) → 𝒰
⇓⁅⁆-body = ⇓⁅⁆-case ∘ ⇓⁅⁆-distr

Q· : Term → (Val → ℕ → 𝒰)
   → Val → ℕ → 𝒰
Q· = Q·-rec $ ⇓⁅⁆-distr $ dfix ⇓⁅⁆-body

Q? : Term → Term → (Val → ℕ → 𝒰)
   → Val → ℕ → 𝒰
Q? = Q?-rec $ ⇓⁅⁆-distr $ dfix ⇓⁅⁆-body

_⇓⁅_⁆_ : Term → ℕ → (Val → ℕ → 𝒰) → 𝒰
_⇓⁅_⁆_ = fix ⇓⁅⁆-body

-- syntax sugar

_⇓⁅_⁆⁰_ : Term → ℕ → (Val → 𝒰) → 𝒰
s ⇓⁅ k ⁆⁰ Q = s ⇓⁅ k ⁆ (λ v l → (l ＝ 0) × (Q v))

_⇓⁅_⁆ᵛ_ : Term → ℕ → Val → 𝒰
s ⇓⁅ k ⁆ᵛ v = s ⇓⁅ k ⁆⁰ (_＝ v)

_⇓^_ : Term → Val → 𝒰
s ⇓^ v = Σ[ k ꞉ ℕ ] s ⇓⁅ k ⁆ᵛ v

-- equations

Q·-eq : ∀ {t x A s m Q} → Q· s Q (v-ƛ x A t) (suc m) ＝ ▹ ((t [ x := s ]) ⇓⁅ m ⁆ Q)
Q·-eq {t} {x} {s} {m} {Q} i = ▹[ α ] pfix ⇓⁅⁆-body i α (t [ x := s ]) m Q

Q?0-eq : ∀ {s t m Q} → Q? s t Q (v-＃ 0) (suc m) ＝ ▹ (s ⇓⁅ m ⁆ Q)
Q?0-eq {s} {m} {Q} i = ▹[ α ] pfix ⇓⁅⁆-body i α s m Q

Q?s-eq : ∀ {s t m n Q} → Q? s t Q (v-＃ (suc n)) (suc m) ＝ ▹ (t ⇓⁅ m ⁆ Q)
Q?s-eq {t} {m} {Q} i = ▹[ α ] pfix ⇓⁅⁆-body i α t m Q

--·-eq : ∀ {r s k Q} → (r · s) ⇓⁅ k ⁆ Q ＝ ▹ (r ⇓⁅ k ⁆ (Q· s Q))
--·-eq {r} {s} {k} {Q} i = ▹[ α ] pfix ⇓⁅⁆-body i α r k (Q· s Q)

Y-eq : ∀ {t k Q} → (Y t) ⇓⁅ suc k ⁆ Q ＝ ▹ ((t · Y t) ⇓⁅ k ⁆ Q)
Y-eq {t} {k} {Q} i = ▹[ α ] pfix ⇓⁅⁆-body i α (t · Y t) k Q

--𝓈-eq : ∀ {t k Q} → 𝓈 t ⇓⁅ suc k ⁆ Q ＝ ▹ (t ⇓⁅ k ⁆ (Q𝓈 Q))
--𝓈-eq {t} {k} {Q} i = ▹[ α ] pfix ⇓⁅⁆-body i α t k (Q𝓈 Q)

--𝓅-eq : ∀ {t k Q} → 𝓅 t ⇓⁅ suc k ⁆ Q ＝ ▹ (t ⇓⁅ k ⁆ (Q𝓅 Q))
--𝓅-eq {t} {k} {Q} i = ▹[ α ] pfix ⇓⁅⁆-body i α t k (Q𝓅 Q)

--?-eq : ∀ {r s t k Q}
--     → (?⁰ r ↑ s ↓ t) ⇓⁅ k ⁆ Q ＝ ▹ (r ⇓⁅ k ⁆ (Q? s t Q))
--?-eq {r} {s} {t} {k} {Q} i = ▹[ α ] pfix ⇓⁅⁆-body i α r k (Q? s t Q)

-- un/rollings

⇉Q· : ∀ {t x s A m Q} → ▹ ((t [ x := s ]) ⇓⁅ m ⁆ Q) → Q· s Q (v-ƛ x A t) (suc m)
⇉Q· {t} {A} = transport (sym $ Q·-eq {t} {A = A})

Q·⇉ : ∀ {t x A s m Q} → Q· s Q (v-ƛ x A t) (suc m) → ▹ ((t [ x := s ]) ⇓⁅ m ⁆ Q)
Q·⇉ {t} {A} = transport (Q·-eq {t} {A = A})

⇉Q?0 : ∀ {s t m Q} → ▹ (s ⇓⁅ m ⁆ Q) → Q? s t Q (v-＃ 0) (suc m)
⇉Q?0 {s} {t} = transport (sym $ Q?0-eq {s} {t})

Q?0⇉ : ∀ {s t m Q} → Q? s t Q (v-＃ 0) (suc m) → ▹ (s ⇓⁅ m ⁆ Q)
Q?0⇉ {s} {t} = transport (Q?0-eq {s} {t})

⇉Q?s : ∀ {s t m n Q} → ▹ (t ⇓⁅ m ⁆ Q) → Q? s t Q (v-＃ (suc n)) (suc m)
⇉Q?s {s} {t} {m} {n} = transport (sym $ Q?s-eq {s} {t} {m} {n})

Q?s⇉ : ∀ {s t m n Q} → Q? s t Q (v-＃ (suc n)) (suc m) → ▹ (t ⇓⁅ m ⁆ Q)
Q?s⇉ {s} {t} {m} {n} = transport (Q?s-eq {s} {t} {m} {n})

--⇉· : ∀ {r s k Q} → ▹ (r ⇓⁅ k ⁆ (Q· s Q)) → (r · s) ⇓⁅ k ⁆ Q
--⇉· = transport (sym ·-eq)

--·⇉ : ∀ {r s k Q} → (r · s) ⇓⁅ k ⁆ Q → ▹ (r ⇓⁅ k ⁆ (Q· s Q))
--·⇉ = transport ·-eq

⇉Y : ∀ {t k Q} → ▹ ((t · Y t) ⇓⁅ k ⁆ Q) → (Y t) ⇓⁅ suc k ⁆ Q
⇉Y = transport (sym Y-eq)

Y⇉ : ∀ {t k Q} → (Y t) ⇓⁅ suc k ⁆ Q → ▹ ((t · Y t) ⇓⁅ k ⁆ Q)
Y⇉ = transport Y-eq

--⇉𝓈 : ∀ {t k Q} → ▹ (t ⇓⁅ k ⁆ (Q𝓈 Q)) → 𝓈 t ⇓⁅ suc k ⁆ Q
--⇉𝓈 {Q} = transport (sym $ 𝓈-eq {Q = Q})

--𝓈⇉ : ∀ {t k Q} → 𝓈 t ⇓⁅ suc k ⁆ Q → ▹ (t ⇓⁅ k ⁆ (Q𝓈 Q))
--𝓈⇉ {Q} = transport (𝓈-eq {Q = Q})

--⇉𝓅 : ∀ {t k Q} → ▹ (t ⇓⁅ k ⁆ (Q𝓅 Q)) → 𝓅 t ⇓⁅ suc k ⁆ Q
--⇉𝓅 {Q} = transport (sym $ 𝓅-eq {Q = Q})

--𝓅⇉ : ∀ {t k Q} → 𝓅 t ⇓⁅ suc k ⁆ Q → ▹ (t ⇓⁅ k ⁆ (Q𝓅 Q))
--𝓅⇉ {Q} = transport (𝓅-eq {Q = Q})

--⇉? : ∀ {r s t k Q}
--       → ▹ (r ⇓⁅ k ⁆ (Q? s t Q))
--       → (?⁰ r ↑ s ↓ t) ⇓⁅ k ⁆ Q
--⇉? = transport (sym ?-eq)

--?⇉ : ∀ {r s t k Q}
--         → (?⁰ r ↑ s ↓ t) ⇓⁅ k ⁆ Q
--         → ▹ (r ⇓⁅ k ⁆ (Q? s t Q))
--?⇉ = transport ?-eq


{-# OPTIONS --guarded #-}
module PCF.Ext.BigstepG where

open import Prelude
open import Data.Empty
open import Data.Nat hiding (_·_)
open import Data.String

open import Later
open import PCF.Ext.Term
open import PCF.Ext.Subst

-- Step-indexed Big-Step Operational (guarded form)

Q·-rec : (Term → ℕ → (Val → ℕ → 𝒰) → ▹ 𝒰) → Term → (Val → ℕ → 𝒰) → Val → ℕ → 𝒰
Q·-rec ⇓▹ s Q (v-ƛ x t) m = ▸ ⇓▹ (t [ x := s ]) m Q
Q·-rec ⇓▹ _ _ (v-＃ _)  _ = ⊥

Q𝓈 : (Val → ℕ → 𝒰) → Val → ℕ → 𝒰
Q𝓈 Q v l = Σ[ n ꞉ ℕ ] (v ＝ v-＃ n) × Q (v-＃ (suc n)) l

-- thesis 2.3.1 says this should guard against n=0 but then it's inconsistent with small-step
Q𝓅 : (Val → ℕ → 𝒰) → Val → ℕ → 𝒰
Q𝓅 Q v l = Σ[ n ꞉ ℕ ] (v ＝ v-＃ n) × Q (v-＃ (pred n)) l

Q?-rec : (Term → ℕ → (Val → ℕ → 𝒰) → ▹ 𝒰) → Term → Term → (Val → ℕ → 𝒰) → Val → ℕ → 𝒰
Q?-rec ⇓▹ s _ Q (v-＃  zero)   m = ▸ ⇓▹ s m Q
Q?-rec ⇓▹ _ t Q (v-＃ (suc _)) m = ▸ ⇓▹ t m Q
Q?-rec ⇓▹ _ _ _ (v-ƛ _ _)      _ = ⊥

⇓⁅⁆-case :   (Term → ℕ → (Val → ℕ → 𝒰) → ▹ 𝒰)
           → Term → ℕ → (Val → ℕ → 𝒰) → 𝒰
⇓⁅⁆-case ⇓▹ (` _)           _      _ = ⊥
⇓⁅⁆-case ⇓▹ (ƛ x ⇒ t)       k      Q = Q (v-ƛ x t) k
⇓⁅⁆-case ⇓▹ (r · s)         k      Q = ▸ ⇓▹ r k (Q·-rec ⇓▹ s Q)
⇓⁅⁆-case ⇓▹ (Y _)           zero   _ = ⊥
⇓⁅⁆-case ⇓▹ (Y t)          (suc k) Q = ▸ ⇓▹ (t · Y t) k Q
⇓⁅⁆-case ⇓▹ (＃ n)          k      Q = Q (v-＃ n) k
⇓⁅⁆-case ⇓▹ (𝓈 t)           k      Q = ▸ ⇓▹ t k (Q𝓈 Q)
⇓⁅⁆-case ⇓▹ (𝓅 t)           k      Q = ▸ ⇓▹ t k (Q𝓅 Q)
⇓⁅⁆-case ⇓▹ (?⁰ r ↑ s ↓ t)  k      Q = ▸ ⇓▹ r k (Q?-rec ⇓▹ s t Q)

⇓⁅⁆-distr : ▹ (Term → ℕ → (Val → ℕ → 𝒰) → 𝒰)
           → Term → ℕ → (Val → ℕ → 𝒰) → ▹ 𝒰
⇓⁅⁆-distr f t n Q = f ⊛ next t ⊛ next n ⊛ next Q

⇓⁅⁆-body : ▹ (Term → ℕ → (Val → ℕ → 𝒰) → 𝒰)
           → Term → ℕ → (Val → ℕ → 𝒰) → 𝒰
⇓⁅⁆-body = ⇓⁅⁆-case ∘ ⇓⁅⁆-distr

_⇓⁅_⁆_ : Term → ℕ → (Val → ℕ → 𝒰) → 𝒰
_⇓⁅_⁆_ = fix ⇓⁅⁆-body

Q· : Term → (Val → ℕ → 𝒰) → Val → ℕ → 𝒰
Q· = Q·-rec $ ⇓⁅⁆-distr $ dfix ⇓⁅⁆-body

Q? : Term → Term → (Val → ℕ → 𝒰) → Val → ℕ → 𝒰
Q? = Q?-rec $ ⇓⁅⁆-distr $ dfix ⇓⁅⁆-body

-- syntax sugar

_⇓⁅_⁆⁰_ : Term → ℕ → (Val → 𝒰) → 𝒰
s ⇓⁅ k ⁆⁰ Q = s ⇓⁅ k ⁆ (λ v l → (l ＝ 0) × (Q v))

_⇓⁅_⁆ᵛ_ : Term → ℕ → Val → 𝒰
s ⇓⁅ k ⁆ᵛ v = s ⇓⁅ k ⁆⁰ (_＝ v)

_⇓^_ : Term → Val → 𝒰
s ⇓^ v = Σ[ k ꞉ ℕ ] s ⇓⁅ k ⁆ᵛ v

-- un/roll

Q·-eq : ∀ {t x s m Q} → Q· s Q (v-ƛ x t) m ＝ ▹ ((t [ x := s ]) ⇓⁅ m ⁆ Q)
Q·-eq {t} {x} {s} {m} {Q} i = ▹[ α ] pfix ⇓⁅⁆-body i α (t [ x := s ]) m Q

roll-Q· : ∀ {t x s m Q} → ▹ ((t [ x := s ]) ⇓⁅ m ⁆ Q) → Q· s Q (v-ƛ x t) m
roll-Q· {t} = transport (sym $ Q·-eq {t})

unroll-Q· : ∀ {t x s m Q} → Q· s Q (v-ƛ x t) m → ▹ ((t [ x := s ]) ⇓⁅ m ⁆ Q)
unroll-Q· {t} = transport (Q·-eq {t})

Q?0-eq : ∀ {s t m Q} → Q? s t Q (v-＃ 0) m ＝ ▹ (s ⇓⁅ m ⁆ Q)
Q?0-eq {s} {m} {Q} i = ▹[ α ] pfix ⇓⁅⁆-body i α s m Q

roll-Q?0 : ∀ {s t m Q} → ▹ (s ⇓⁅ m ⁆ Q) → Q? s t Q (v-＃ 0) m
roll-Q?0 {s} {t} sm = transport (sym $ Q?0-eq {s} {t}) sm

unroll-Q?0 : ∀ {s t m Q} → Q? s t Q (v-＃ 0) m → ▹ (s ⇓⁅ m ⁆ Q)
unroll-Q?0 {s} {t} sm = transport (Q?0-eq {s} {t}) sm

-- TODO factor out rest of eqs

roll-Q?s : ∀ {s t m Q n} → ▹ (t ⇓⁅ m ⁆ Q) → Q? s t Q (v-＃ (suc n)) m
roll-Q?s {t} {m} {Q} tm =
  transport (λ i → ▹[ α ] pfix ⇓⁅⁆-body (~ i) α t m Q) tm

unroll-Q?s : ∀ {s t m Q n} → Q? s t Q (v-＃ (suc n)) m → ▹ (t ⇓⁅ m ⁆ Q)
unroll-Q?s {t} {m} {Q} tm =
  transport (λ i → ▹[ α ] pfix ⇓⁅⁆-body i α t m Q) tm

roll-· : ∀ {r s k Q} → ▹ (r ⇓⁅ k ⁆ (Q· s Q)) → (r · s) ⇓⁅ k ⁆ Q
roll-· {r} {s} {k} {Q} tr =
  transport (λ i → ▹[ α ] pfix ⇓⁅⁆-body (~ i) α r k (Q· s Q)) tr

unroll-· : ∀ {r s k Q} → (r · s) ⇓⁅ k ⁆ Q → ▹ (r ⇓⁅ k ⁆ (Q· s Q))
unroll-· {r} {s} {k} {Q} tr =
  transport (λ i → ▹[ α ] pfix ⇓⁅⁆-body i α r k (Q· s Q)) tr

roll-Y : ∀ {t k Q} → ▹ ((t · Y t) ⇓⁅ k ⁆ Q) → (Y t) ⇓⁅ suc k ⁆ Q
roll-Y {t} {k} {Q} tYt =
  transport (λ i → ▹[ α ] pfix ⇓⁅⁆-body (~ i) α (t · Y t) k Q) tYt

unroll-Y : ∀ {t k Q} → (Y t) ⇓⁅ suc k ⁆ Q → ▹ ((t · Y t) ⇓⁅ k ⁆ Q)
unroll-Y {t} {k} {Q} Yt =
  transport (λ i → ▹[ α ] pfix ⇓⁅⁆-body i α (t · Y t) k Q) Yt

roll-𝓈 : ∀ {t k Q} → ▹ (t ⇓⁅ k ⁆ (Q𝓈 Q)) → 𝓈 t ⇓⁅ k ⁆ Q
roll-𝓈 {t} {k} {Q} tk =
  transport (λ i → ▹[ α ] pfix ⇓⁅⁆-body (~ i) α t k (Q𝓈 Q)) tk

unroll-𝓈 : ∀ {t k Q} → 𝓈 t ⇓⁅ k ⁆ Q → ▹ (t ⇓⁅ k ⁆ (Q𝓈 Q))
unroll-𝓈 {t} {k} {Q} tk =
  transport (λ i → ▹[ α ] pfix ⇓⁅⁆-body i α t k (Q𝓈 Q)) tk

roll-𝓅 : ∀ {t k Q} → ▹ (t ⇓⁅ k ⁆ (Q𝓅 Q)) → 𝓅 t ⇓⁅ k ⁆ Q
roll-𝓅 {t} {k} {Q} tk =
  transport (λ i → ▹[ α ] pfix ⇓⁅⁆-body (~ i) α t k (Q𝓅 Q)) tk

unroll-𝓅 : ∀ {t k Q} → 𝓅 t ⇓⁅ k ⁆ Q → ▹ (t ⇓⁅ k ⁆ (Q𝓅 Q))
unroll-𝓅 {t} {k} {Q} tk =
  transport (λ i → ▹[ α ] pfix ⇓⁅⁆-body i α t k (Q𝓅 Q)) tk

roll-? : ∀ {r s t k Q}
         → ▹ (r ⇓⁅ k ⁆ (Q? s t Q))
         → (?⁰ r ↑ s ↓ t) ⇓⁅ k ⁆ Q
roll-? {r} {s} {t} {k} {Q} rst =
  transport (λ i → ▹[ α ] pfix ⇓⁅⁆-body (~ i) α r k (Q? s t Q)) rst

unroll-? : ∀ {r s t k Q}
         → (?⁰ r ↑ s ↓ t) ⇓⁅ k ⁆ Q
         → ▹ (r ⇓⁅ k ⁆ (Q? s t Q))
unroll-? {r} {s} {t} {k} {Q} rst =
  transport (λ i → ▹[ α ] pfix ⇓⁅⁆-body i α r k (Q? s t Q)) rst


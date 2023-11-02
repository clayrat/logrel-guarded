{-# OPTIONS --guarded #-}
module PCF.Ext.Bigstep where

open import Prelude
open import Data.Empty
open import Data.Nat hiding (_·_)
open import Data.String

open import Later
open import PCF.Ext.Term

-- Step-indexed Big-Step Operational Semantics (alternative)

Q𝓈 : (Val → ℕ → 𝒰)
   → Val → ℕ → 𝒰
Q𝓈 Q v l = Σ[ n ꞉ ℕ ] (v ＝ v-＃ n) × Q (v-＃ (suc n)) l

-- thesis 2.3.1 says this should guard against n=0 but then it's inconsistent with small-step
Q𝓅 : (Val → ℕ → 𝒰)
   → Val → ℕ → 𝒰
Q𝓅 Q v l = Σ[ n ꞉ ℕ ] (v ＝ v-＃ n) × Q (v-＃ (pred n)) l

-- problematic cases for termination are app+if
{-# TERMINATING #-}
mutual
  _⇓⁅_⁆_ : Term → ℕ → (Val → ℕ → 𝒰) → 𝒰
  (` _)          ⇓⁅ _     ⁆ _ = ⊥
  (ƛ x ⇒ t)      ⇓⁅ k     ⁆ Q = Q (v-ƛ x t) k
  (r · s)        ⇓⁅ k     ⁆ Q = r ⇓⁅ k ⁆ Q· s Q
  (Y _)          ⇓⁅ zero  ⁆ _ = ⊥
  (Y t)          ⇓⁅ suc k ⁆ Q = ▹ ((t · Y t) ⇓⁅ k ⁆ Q)
  (＃ n)         ⇓⁅ k     ⁆ Q = Q (v-＃ n) k
  𝓈 s            ⇓⁅ k     ⁆ Q = s ⇓⁅ k ⁆ Q𝓈 Q
  𝓅 s            ⇓⁅ k     ⁆ Q = s ⇓⁅ k ⁆ Q𝓅 Q
  (?⁰ r ↑ s ↓ t) ⇓⁅ k     ⁆ Q = r ⇓⁅ k ⁆ Q? s t Q

  Q· : Term → (Val → ℕ → 𝒰) → Val → ℕ → 𝒰
  Q· s Q (v-ƛ x t) m = (t [ x := s ]) ⇓⁅ m ⁆ Q
  Q· s Q (v-＃ _)  _ = ⊥

  Q? : Term → Term → (Val → ℕ → 𝒰) → Val → ℕ → 𝒰
  Q? s t Q (v-＃  zero)   m = s ⇓⁅ m ⁆ Q
  Q? s t Q (v-＃ (suc n)) m = t ⇓⁅ m ⁆ Q
  Q? s t Q (v-ƛ _ _)      _ = ⊥

_⇓⁅_⁆⁰_ : Term → ℕ → (Val → 𝒰) → 𝒰
s ⇓⁅ k ⁆⁰ Q = s ⇓⁅ k ⁆ λ v l → (l ＝ 0) × (Q v)

_⇓⁅_⁆ᵛ_ : Term → ℕ → Val → 𝒰
s ⇓⁅ k ⁆ᵛ v = s ⇓⁅ k ⁆⁰ (_＝ v)

_⇓^_ : Term → Val → 𝒰
s ⇓^ v = Σ[ k ꞉ ℕ ] s ⇓⁅ k ⁆ᵛ v

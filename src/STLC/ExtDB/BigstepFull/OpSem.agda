module STLC.ExtDB.BigstepFull.OpSem where

open import Prelude

open import STLC.ExtDB.Term
open import STLC.ExtDB.Ty

-- big-step / natural

infix 4 _∣_⇓_
infix 5 ⟨ƛ_⟩_
infix 5 _·ⁿᵉ_
infix 6 _＋＋_

mutual
  -- Environments
  Env : 𝒰
  Env = ℕ → Domain

  -- Domain of evaluation
  data Domain : 𝒰 where
  -- Closures
    ⟨ƛ_⟩_ : Term → Env → Domain
  -- Neutral domain elements
    ⟨_⟩ⁿᵉ : DomainNE → Domain

  -- Neutral domain
  data DomainNE : 𝒰 where
  -- Variables (de Brujin levels)
    lvl   : ℕ → DomainNE
  -- Application
    _·ⁿᵉ_ : DomainNE → Domain → DomainNE

-- Extending an environment
_＋＋_ : Env → Domain → Env
(_ ＋＋ a)  zero   = a
(γ ＋＋ _) (suc x) = γ x

-- Evaluation of terms
mutual
  data _∣_⇓_ : Env → Term → Domain → 𝒰 where
    ⇓`  : ∀ {γ i}
        → γ ∣ ` i ⇓ γ i
    ⇓ƛ  : ∀ {γ t}
        → γ ∣ ƛ t ⇓ ⟨ƛ t ⟩ γ
    ⇓·  : ∀ {γ r s f a b}
        → γ ∣ r ⇓ f
        → γ ∣ s ⇓ a
        → f · a ⇓ b
        → γ ∣ r · s ⇓ b

-- Well-defined application
  data _·_⇓_ : Domain → Domain → Domain → 𝒰 where
    ·⇓ƛ  : ∀ {γ t a b}
        → γ ＋＋ a ∣ t ⇓ b
        → (⟨ƛ t ⟩ γ) · a ⇓ b
    ·⇓ⁿᵉ : ∀ {e d}
        → ⟨ e ⟩ⁿᵉ · d ⇓ ⟨ e ·ⁿᵉ d ⟩ⁿᵉ

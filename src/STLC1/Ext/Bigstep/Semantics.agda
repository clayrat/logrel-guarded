module STLC1.Ext.Bigstep.Semantics where

open import Prelude
open import Data.Empty
open import Data.List

open import STLC1.Ext.Term
open import STLC1.Ext.Ty

infix 4 _∣_⇓_
infix 5 ⟨ƛ_⇒_⟩_

-- big-step / natural

private variable
  Γ : Ctx
  T : Ty

mutual
  -- Environments + domains
  data Env : 𝒰 where
    ∅ₑ : Env
    _﹐_↦_ : Env → Id → Domain → Env

  -- Domain of evaluation
  data Domain : 𝒰 where
   ⟨𝓉𝓉⟩ : Domain
  -- Closures
   ⟨ƛ_⇒_⟩_ : Id → Term → Env → Domain

-- lookup and context inclusion

data _∋_↦_ : Env → Id → Domain → 𝒰 where

  hereₑ : ∀ {γ x a}
      ------------------
       → (γ ﹐ x ↦ a) ∋ x ↦ a

  thereₑ : ∀ {γ x y a b}
        → x ≠ y
        → γ ∋ x ↦ a
          ------------------
        → (γ ﹐ y ↦ b) ∋ x ↦ a

-- Evaluation
data _∣_⇓_ : Env → Term → Domain → 𝒰 where
  ⇓𝓉𝓉 : ∀ {γ}
      → γ ∣ 𝓉𝓉 ⇓ ⟨𝓉𝓉⟩
  ⇓`  : ∀ {γ} {i} {a}
      → γ ∋ i ↦ a
      → γ ∣ ` i ⇓ a
  ⇓ƛ  : ∀ {γ} {x} {t}
      → γ ∣ (ƛ x ⇒ t) ⇓ (⟨ƛ x ⇒ t ⟩ γ)
  ⇓·  : ∀ {γ} {r s} {x} {δ} {t} {a b}
      → γ ∣ r ⇓ ⟨ƛ x ⇒ t ⟩ δ
      → γ ∣ s ⇓ a
      → δ ﹐ x ↦ a ∣ t ⇓ b
      → γ ∣ r · s ⇓ b

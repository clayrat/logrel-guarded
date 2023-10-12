module STLC2.Int.OpSem where

open import Prelude
open import Data.Empty
open import Data.List

open import STLC2.Int.TyTerm

-- big-step / natural

private variable
  Γ : Ctx
  T : Ty

infix 4 _∣_⇓_
infix 5 ⟨ƛ_⟩_
infix 6 _＋＋_

mutual
  -- Environments
  Env : Ctx → 𝒰
  Env Γ = ∀ {T} → Γ ∋ T → Domain T

  -- Domain of evaluation
  data Domain : Ty → 𝒰 where
  -- Booleans
   ⟨𝓉⟩ ⟨𝒻⟩ : Domain 𝟚
  -- Closures
   ⟨ƛ_⟩_ : ∀ {Γ S T}
        → Γ ﹐ S ⊢ T → Env Γ → Domain (S ⇒ T)

empty : Env ∅
empty ()

-- Extending an environment
_＋＋_ : ∀ {Γ T}
      → Env Γ → Domain T → Env (Γ ﹐ T)
(_ ＋＋ a)  here     = a
(γ ＋＋ _) (there i) = γ i

-- Evaluation of terms
data _∣_⇓_ : Env Γ → Γ ⊢ T → Domain T → 𝒰 where
  ⇓𝓉  : ∀ {γ : Env Γ}
      → γ ∣ 𝓉 ⇓ ⟨𝓉⟩
  ⇓𝒻  : ∀ {γ : Env Γ}
      → γ ∣ 𝒻 ⇓ ⟨𝒻⟩
  ⇓`  : ∀ {γ : Env Γ} {i : Γ ∋ T}
      → γ ∣ ` i ⇓ γ i
  ⇓ƛ  : ∀ {γ : Env Γ} {A} {t : Γ ﹐ A ⊢ T}
      → γ ∣ ƛ t ⇓ ⟨ƛ t ⟩ γ
  ⇓·  : ∀ {γ : Env Γ} {A r s} {Δ} {δ : Env Δ} {t : Δ ﹐ A ⊢ T} {a b}
      → γ ∣ r ⇓ ⟨ƛ t ⟩ δ
      → γ ∣ s ⇓ a
      → δ ＋＋ a ∣ t ⇓ b
      → γ ∣ r · s ⇓ b
  ⇓⁇↑ : ∀ {γ : Env Γ} {r} {s : Γ ⊢ T} {t a}
      → γ ∣ r ⇓ ⟨𝓉⟩
      → γ ∣ s ⇓ a
      → γ ∣ ⁇ r ↑ s ↓ t ⇓ a
  ⇓⁇↓ : ∀ {γ : Env Γ} {r s} {t : Γ ⊢ T} {b}
      → γ ∣ r ⇓ ⟨𝒻⟩
      → γ ∣ t ⇓ b
      → γ ∣ ⁇ r ↑ s ↓ t ⇓ b

⇓-well-defined : ∅ ⊢ T → 𝒰
⇓-well-defined {T} t = Σ[ a ꞉ Domain T ] (empty ∣ t ⇓ a)

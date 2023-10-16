module STLC2.Int.DenSem where

open import Prelude
open import Data.Bool

open import Interlude
open import STLC2.Int.TyTerm
open import STLC2.Int.OpSem
open import STLC2.Int.Norm

private variable
  Γ Δ : Ctx
  T : Ty

-- Denotation of types
𝒯⟦_⟧ : Ty → 𝒰
𝒯⟦ 𝟚 ⟧     = Bool
𝒯⟦ S ⇒ T ⟧ = 𝒯⟦ S ⟧ → 𝒯⟦ T ⟧

-- Denotation of contexts
𝒞⟦_⟧ : Ctx → 𝒰
𝒞⟦ Γ ⟧ = ∀ {T} → Γ ∋ T → 𝒯⟦ T ⟧

-- Extending denoted contexts
_＆_ : 𝒞⟦ Γ ⟧ → 𝒯⟦ T ⟧ → 𝒞⟦ Γ ﹐ T ⟧
(_ ＆ a)  here     = a
(ρ ＆ _) (there i) = ρ i

-- Appending denoted contexts
_＆＆_ : 𝒞⟦ Γ ⟧ → 𝒞⟦ Δ ⟧ → 𝒞⟦ Γ ◇ Δ ⟧
_＆＆_ {Δ = ∅}     p q = p
_＆＆_ {Δ = Δ ﹐ T} p q = (p ＆＆ (q ∘ there)) ＆ q here

-- Denotation of terms
ℰ⟦_⟧ : Γ ⊢ T → 𝒞⟦ Γ ⟧ → 𝒯⟦ T ⟧
ℰ⟦ ` i ⟧        ρ = ρ i
ℰ⟦ ƛ t ⟧        ρ = λ ta → ℰ⟦ t ⟧ (ρ ＆ ta)
ℰ⟦ r · s ⟧      ρ = ℰ⟦ r ⟧ ρ (ℰ⟦ s ⟧ ρ)
ℰ⟦ 𝓉 ⟧          ρ = true
ℰ⟦ 𝒻 ⟧          ρ = false
ℰ⟦ ⁇ r ↑ s ↓ t ⟧ ρ = if ℰ⟦ r ⟧ ρ then ℰ⟦ s ⟧ ρ else ℰ⟦ t ⟧ ρ

mutual
  -- Denotation of environments
  𝒢⟦_⟧ : Env Γ → 𝒞⟦ Γ ⟧
  𝒢⟦ γ ⟧ {T} i = 𝒟⟦ γ T i ⟧

  -- Denotation of domain elements
  𝒟⟦_⟧ : Domain T → 𝒯⟦ T ⟧
  𝒟⟦ ⟨𝓉⟩ ⟧     = true
  𝒟⟦ ⟨𝒻⟩ ⟧     = false
  𝒟⟦ ⟨ƛ t ⟩ γ ⟧ = λ ts → ℰ⟦ t ⟧ (𝒢⟦ γ ⟧ ＆ ts)

-- Denotational equivalence
_ℰ≡_ : Γ ⊢ T → Γ ⊢ T → 𝒰
_ℰ≡_ {Γ} t v = ∀ {ρ : 𝒞⟦ Γ ⟧} → ℰ⟦ t ⟧ ρ ＝ ℰ⟦ v ⟧ ρ

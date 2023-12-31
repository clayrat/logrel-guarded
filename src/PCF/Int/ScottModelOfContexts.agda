{-# OPTIONS --guarded #-}
module PCF.Int.ScottModelOfContexts where

open import Prelude
open import Data.Unit
open import Data.Nat
open import Data.Vec

open import Later
open import Guarded.Partial

open import PCF.Ty
open import PCF.Int.TyTerm
open import PCF.Int.ScottModelOfTypes

𝒞⟦_⟧ : {n : ℕ} → Ctx n → 𝒰
𝒞⟦ []    ⟧ = ⊤
𝒞⟦ Γ ﹐ σ ⟧ = 𝒞⟦ Γ ⟧ × 𝒯⟦ σ ⟧

extractᵧ : {n : ℕ} {σ : Ty} {Γ : Ctx n}
        → (x : Γ ∋ σ)
        → 𝒞⟦ Γ ⟧ → 𝒯⟦ σ ⟧
extractᵧ  here     (_ , 𝒯σ) = 𝒯σ
extractᵧ (there x) (𝒞Γ , _) = extractᵧ x 𝒞Γ

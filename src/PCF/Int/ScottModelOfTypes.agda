{-# OPTIONS --guarded #-}
module PCF.Int.ScottModelOfTypes where

open import Prelude
open import Data.Nat

open import Later
open import Guarded.Partial
open import PCF.Int.TyTerm

private variable
  ℓ : Level
  T : Ty
  A : 𝒰 ℓ

𝒯⟦_⟧ : Ty → 𝒰
𝒯⟦ 𝓝 ⟧    = Part ℕ
𝒯⟦ S ⇒ T ⟧ = 𝒯⟦ S ⟧ → 𝒯⟦ T ⟧

θ : ▹Alg (𝒯⟦ T ⟧)
θ {T = 𝓝} x▹     = later x▹
θ {S ⇒ T}  tf▹ ts = θ (tf▹ ⊛ next ts)

δ : 𝒯⟦ T ⟧ → 𝒯⟦ T ⟧
δ = θ ∘ next

^-body : (A → 𝒯⟦ T ⟧)
       → ▹ (Part A → 𝒯⟦ T ⟧)
       → Part A → 𝒯⟦ T ⟧
^-body f f^▹ (now x)    = f x
^-body f f^▹ (later p▹) = θ (f^▹ ⊛ p▹)

_^ : (A → 𝒯⟦ T ⟧)
   → Part A → 𝒯⟦ T ⟧
(f ^) = fix (^-body f)

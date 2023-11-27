{-# OPTIONS --guarded #-}
module PCF.Int.ScottModelOfTerms where

open import Prelude
open import Data.Unit
open import Data.Nat
open import Data.Vec

open import Later
open import Guarded.Partial

open import PCF.Ty
open import PCF.Int.TyTerm
open import PCF.Int.ScottModelOfTypes
open import PCF.Int.ScottModelOfContexts

private variable
  T : Ty

ifz : 𝒯⟦ T ⟧ → 𝒯⟦ T ⟧ → ℕ → 𝒯⟦ T ⟧
ifz x y  zero   = x
ifz x y (suc n) = y

ifz^ : 𝒯⟦ T ⟧ → 𝒯⟦ T ⟧ → 𝒯⟦ 𝓝 ⟧ → 𝒯⟦ T ⟧
ifz^ x y = (ifz x y) ^

δ-ifz : ∀ {k}
        {L : Part ℕ}
        {M N : 𝒯⟦ T ⟧}
       → ifz^ M N (iter k δᵖ L) ＝ iter k δ (ifz^ M N L)
δ-ifz {k = zero}              = refl
δ-ifz {k = suc k} {L} {M} {N} =
    ap (λ q → q (δᵖ (iter k δᵖ L))) (fix-path (^-body (ifz M N)))
  ∙ ap δ (δ-ifz {k = k})

ℰ⟦_⟧ : {n : ℕ} {Γ : Ctx n}
     → Γ ⊢ T → 𝒞⟦ Γ ⟧ → 𝒯⟦ T ⟧
ℰ⟦ ` x ⟧          γ = extractᵧ x γ
ℰ⟦ ƛ t ⟧          γ = ℰ⟦ t ⟧ ∘ (γ ,_)
ℰ⟦ r · s ⟧        γ = ℰ⟦ r ⟧ γ (ℰ⟦ s ⟧ γ)
ℰ⟦ Y t ⟧          γ = fix $ θ ∘ ▹map (ℰ⟦ t ⟧ γ)
ℰ⟦ ＃ n ⟧         γ = now n
ℰ⟦ 𝓈 t ⟧          γ = mapᵖ suc (ℰ⟦ t ⟧ γ)
ℰ⟦ 𝓅 t ⟧          γ = mapᵖ pred (ℰ⟦ t ⟧ γ)
ℰ⟦ ?⁰ r ↑ s ↓ t ⟧ γ = ifz^ (ℰ⟦ s ⟧ γ) (ℰ⟦ t ⟧ γ) (ℰ⟦ r ⟧ γ)

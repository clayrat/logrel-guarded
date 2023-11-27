{-# OPTIONS --guarded #-}
module PCF.Int.Correctness where

open import Prelude hiding ([_])
open import Data.Unit
open import Data.Nat hiding (_·_)
open import Data.Vec

open import Later
open import Interlude
open import Guarded.Partial

open import PCF.Ty
open import PCF.Int.TyTerm
open import PCF.Int.Bigstep
open import PCF.Int.ScottModelOfTypes
open import PCF.Int.ScottModelOfContexts
open import PCF.Int.ScottModelOfTerms
open import PCF.Int.SubstitutionDenotational

-- this breaks if we require n to be irrelevant
correctness' : {n : ℕ} {Γ : Ctx n} {σ : Ty}
               (M V : Γ ⊢ σ)
             → M ⇓' V
             → Σ[ k ꞉ ℕ ] (ℰ⟦ M ⟧ ＝ iter k δ ∘ ℰ⟦ V ⟧)
correctness' .(` _) .(` _) var-id = 0 , refl
correctness' .(ƛ _) .(ƛ _) ƛ-id = 0 , refl
correctness' .(＃ _) .(＃ _) ＃-id = 0 , refl
correctness' .(𝓅 M) .(＃ zero) (𝓅-zero {M} S) =
  let (n , e) = correctness' M (＃ zero) S in
  (n , fun-ext λ γ → ap (λ q → mapᵖ pred (q γ)) e ∙ δᵖ-map {k = n})
correctness' .(𝓅 M) .(＃ k) (𝓅-suc {M} {k} S) =
  let (n , e) = correctness' M (＃ (suc k)) S in
  (n , fun-ext λ γ → ap (λ q → mapᵖ pred (q γ)) e ∙ δᵖ-map {k = n})
correctness' .(𝓈 M) .(＃ suc k) (𝓈-arg {M} {k} S) =
  let (n , e) = correctness' M (＃ k) S in
  (n , fun-ext λ γ → ap (λ q → mapᵖ suc (q γ)) e ∙ δᵖ-map {k = n})
correctness' .(?⁰ M ↑ M₁ ↓ M₂) V (?⁰-zero {M} {M₁} {M₂} S₁ S₂) =
  let (n₁ , e₁) = correctness' M (＃ zero) S₁
      (n₂ , e₂) = correctness' M₁ V S₂
    in
  (n₁ + n₂ , fun-ext λ γ →   ap (λ q → ifz^ (ℰ⟦ M₁ ⟧ γ) (ℰ⟦ M₂ ⟧ γ) (q γ)) e₁
                           ∙ δ-ifz {k = n₁}
                           ∙ ap (λ q → iter n₁ δ (q γ)) e₂
                           ∙ sym (iter-add n₁ n₂ δ (ℰ⟦ V ⟧ γ)))
correctness' .(?⁰ M ↑ M₁ ↓ M₂) V (?⁰-suc {M} {M₁} {M₂} {k} S₁ S₂) =
  let (n₁ , e₁) = correctness' M (＃ suc k) S₁
      (n₂ , e₂) = correctness' M₂ V S₂
    in
  (n₁ + n₂ , fun-ext λ γ →   ap (λ q → ifz^ (ℰ⟦ M₁ ⟧ γ) (ℰ⟦ M₂ ⟧ γ) (q γ)) e₁
                           ∙ δ-ifz {k = n₁}
                           ∙ ap (λ q → iter n₁ δ (q γ)) e₂
                           ∙ sym (iter-add n₁ n₂ δ (ℰ⟦ V ⟧ γ)))
correctness' .(Y M) V (Y-step {M} S) =
  let (n , e) = correctness' (M · Y M) V S in
  (suc n , fun-ext λ γ → fix-path (θ ∘ ▹map (ℰ⟦ M ⟧ γ)) ∙ ap δ (happly e γ))
correctness' .(M · N) V (·-step {M} {E} {N} S₁ S₂) =
  let (n₁ , e₁) = correctness' M (ƛ E) S₁
      (n₂ , e₂) = correctness' (E [ N ]) V S₂
    in
  (n₁ + n₂ , fun-ext λ γ →   ap (λ q → q γ (ℰ⟦ N ⟧ γ)) e₁
                           ∙ δ-$ {k = n₁}
                           ∙ ap (iter n₁ δ) (β-equality E N γ)
                           ∙ ap (λ q → iter n₁ δ (q γ)) e₂
                           ∙ sym (iter-add n₁ n₂ δ (ℰ⟦ V ⟧ γ)))

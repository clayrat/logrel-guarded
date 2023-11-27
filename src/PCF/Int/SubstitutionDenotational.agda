{-# OPTIONS --guarded #-}
module PCF.Int.SubstitutionDenotational where

open import Prelude hiding ([_])
open import Data.Unit
open import Data.Nat hiding (_·_)
open import Data.Vec

open import Later
open import Interlude
open import Guarded.Partial
open import PCF.Int.TyTerm
open import PCF.Int.ScottModelOfTypes
open import PCF.Int.ScottModelOfContexts
open import PCF.Int.ScottModelOfTerms

replace-first-lemma : {@0 n : ℕ} {Γ : Ctx n} {σ τ : Ty}
                      (x : (τ ∷ Γ) ∋ σ)
                      (γ : 𝒞⟦ Γ ⟧)
                      (T : Γ ⊢ τ)
                    → (ℰ⟦ ` x ⟧ (γ , ℰ⟦ T ⟧ γ)) ＝ ℰ⟦ replace-first T x ⟧ γ
replace-first-lemma  here     γ T = refl
replace-first-lemma (there x) γ T = refl

rename-lemma : {@0 n m : ℕ} {Γ : Ctx n} {Δ : Ctx m} {σ : Ty}
               (M : Γ ⊢ σ)
               (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
               (γ : 𝒞⟦ Γ ⟧)
               (d : 𝒞⟦ Δ ⟧)
             → (∀ {A} (x : Γ ∋ A) → extractᵧ x γ ＝ extractᵧ (ρ x) d)
             → ℰ⟦ rename ρ M ⟧ d ＝ ℰ⟦ M ⟧ γ
rename-lemma                 (` x)          ρ γ d e = sym (e x)
rename-lemma {Γ} {σ = σ ⇒ τ} (ƛ M)          ρ γ d e =
  fun-ext λ z →
    rename-lemma M (extᵧ ρ) (γ , z) (d , z) go
  where
  go : {z : 𝒯⟦ σ ⟧} {A : Ty}
     → (x : (σ ∷ Γ) ∋ A)
     → extractᵧ x (γ , z) ＝ extractᵧ (extᵧ ρ x) (d , z)
  go  here     = refl
  go (there x) = e x
rename-lemma                 (M · N)        ρ γ d e =
  ap² _$_ (rename-lemma M ρ γ d e) (rename-lemma N ρ γ d e)
rename-lemma                 (Y M)          ρ γ d e =
  ap (λ q → fix (θ ∘ ▹map q)) (rename-lemma M ρ γ d e)
rename-lemma                 (＃ n)         ρ γ d e = refl
rename-lemma                 (𝓈 M)          ρ γ d e =
  ap (mapᵖ suc) (rename-lemma M ρ γ d e)
rename-lemma                 (𝓅 M)          ρ γ d e =
  ap (mapᵖ pred) (rename-lemma M ρ γ d e)
rename-lemma                 (?⁰ L ↑ M ↓ N) ρ γ d e =
  ap³-simple ifz^ (rename-lemma M ρ γ d e) (rename-lemma N ρ γ d e) (rename-lemma L ρ γ d e)

substitution-lemma : {@0 n m : ℕ} {Γ : Ctx n} {Δ : Ctx m} {σ : Ty}
                     (M : Γ ⊢ σ)
                     (f : ∀ {A} → Γ ∋ A → Δ ⊢ A)
                     (γ : 𝒞⟦ Γ ⟧)
                     (d : 𝒞⟦ Δ ⟧)
                   → (∀ {A} (x : Γ ∋ A) → ℰ⟦ ` x ⟧ γ ＝ ℰ⟦ f x ⟧ d)
                   → ℰ⟦ M ⟧ γ ＝ ℰ⟦ sub f M ⟧ d
substitution-lemma (` x)          f γ d g = g x
substitution-lemma {Γ} {σ = σ ⇒ τ} (ƛ M)          f γ d g =
  fun-ext λ z →
    substitution-lemma M (exts f) (γ , z) (d , z) go
  where
  go : {z : 𝒯⟦ σ ⟧} {A : Ty}
     → (x : (σ ∷ Γ) ∋ A)
     → ℰ⟦ ` x ⟧ (γ , z) ＝ ℰ⟦ exts f x ⟧ (d , z)
  go      here     = refl
  go {z} (there x) = g x ∙ sym (rename-lemma (f x) there d (d , z) (λ _ → refl))
substitution-lemma (M · N)        f γ d g =
  ap² (_$_) (substitution-lemma M f γ d g) (substitution-lemma N f γ d g)
substitution-lemma (Y M)          f γ d g =
  ap (λ q → fix (θ ∘ ▹map q)) (substitution-lemma M f γ d g)
substitution-lemma (＃ n)          f γ d g = refl
substitution-lemma (𝓈 M)          f γ d g =
  ap (mapᵖ suc) (substitution-lemma M f γ d g)
substitution-lemma (𝓅 M)          f γ d g =
  ap (mapᵖ pred) (substitution-lemma M f γ d g)
substitution-lemma (?⁰ L ↑ M ↓ N) f γ d g =
  ap³-simple ifz^ (substitution-lemma M f γ d g) (substitution-lemma N f γ d g) (substitution-lemma L f γ d g)

β-equality : {@0 n : ℕ} {Γ : Ctx n} {σ τ : Ty}
             (M : (τ ∷ Γ) ⊢ σ)
             (N : Γ ⊢ τ)
             (γ : 𝒞⟦ Γ ⟧)
           → (ℰ⟦ (ƛ M) · N ⟧ γ) ＝ ℰ⟦ M [ N ] ⟧ γ
β-equality {Γ} {τ} M N γ =
  substitution-lemma M (replace-first N) (γ , ℰ⟦ N ⟧ γ) γ go
  where
  go : ∀ {A}
       → (x : (τ ∷ Γ) ∋ A)
     → ℰ⟦ ` x ⟧ (γ , ℰ⟦ N ⟧ γ) ＝ ℰ⟦ replace-first N x ⟧ γ
  go  here     = refl
  go (there x) = refl

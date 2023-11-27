module PCF.Int.Bigstep where

open import Prelude hiding ([_])
open import Data.Empty
open import Data.Unit

open import PCF.Ty
open import PCF.Int.TyTerm

data _⇓'_ : ∀ {n : ℕ} {Γ : Ctx n} {σ : Ty}
          → Γ ⊢ σ → Γ ⊢ σ → 𝒰 where

  var-id : {n : ℕ} {Γ : Ctx n} {A : Ty}
           {i : Γ ∋ A}
         → (` i) ⇓' (` i)

  ƛ-id : {n : ℕ} {Γ : Ctx n} {σ τ : Ty}
         {t : (Γ ﹐ σ) ⊢ τ}
       → (ƛ t) ⇓' (ƛ t)

  ＃-id : {n : ℕ} {Γ : Ctx n}
          {k : ℕ}
        → (＃_ {n} {Γ} k) ⇓' (＃_ {n} {Γ} k)

  𝓅-zero : {n : ℕ} {Γ : Ctx n}
           {M : Γ ⊢ 𝓝}
         → M ⇓' (＃_ {n} {Γ} zero)
         → 𝓅 M ⇓' (＃_ {n} {Γ} zero)

  𝓅-suc : {n : ℕ} {Γ : Ctx n}
          {M : Γ ⊢ 𝓝}
          {k : ℕ}
         → M ⇓' (＃_ {n} {Γ} (suc k))
         → 𝓅 M ⇓' (＃_ {n} {Γ} k)

  𝓈-arg  : {n : ℕ} {Γ : Ctx n}
           {M : Γ ⊢ 𝓝}
           {k : ℕ}
         → M ⇓' ＃_ {n} {Γ} k
         → 𝓈 M ⇓' ＃_ {n} {Γ} (suc k)

  ?⁰-zero : {n : ℕ} {Γ : Ctx n} {σ : Ty}
            {M : Γ ⊢ 𝓝} {M₁ : Γ ⊢ σ} {M₂ : Γ ⊢ σ}
            {V : Γ ⊢ σ}
          → M ⇓' ＃_ {n} {Γ} zero
          → M₁ ⇓' V
          → (?⁰ M ↑ M₁ ↓ M₂) ⇓' V

  ?⁰-suc : {n : ℕ} {Γ : Ctx n} {σ : Ty}
           {M : Γ ⊢ 𝓝} {M₁ : Γ ⊢ σ} {M₂ : Γ ⊢ σ}
           {V : Γ ⊢ σ}
           {k : ℕ}
         → M ⇓' ＃_ {n} {Γ} (suc k)
         → M₂ ⇓' V
         → (?⁰ M ↑ M₁ ↓ M₂) ⇓' V

  Y-step : {n : ℕ} {Γ : Ctx n} {σ : Ty} {M : Γ ⊢ (σ ⇒ σ)} {V : Γ ⊢ σ}
         → (M · (Y M)) ⇓' V
         → (Y M) ⇓' V

  ·-step : {n : ℕ} {Γ : Ctx n} {σ τ : Ty}
           {M : Γ ⊢ (σ ⇒ τ)} {E : (Γ ﹐ σ) ⊢ τ} {N : Γ ⊢ σ}
           {V : Γ ⊢ τ}
         → M ⇓' (ƛ E)
         → (E [ N ]) ⇓' V
         → (M · N) ⇓' V

_⇓_ : {n : ℕ} {Γ : Ctx n} {σ : Ty}
    → Γ ⊢ σ → Γ ⊢ σ → 𝒰
M ⇓ N = ∥ M ⇓' N ∥₁

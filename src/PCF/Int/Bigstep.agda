module PCF.Int.Bigstep where

open import Prelude hiding ([_])
open import Data.Empty
open import Data.Unit
open import Data.Fin
open import Data.Vec
--open import Truncation.Propositional

open import PCF.Int.TyTerm

data _⇓'_ : ∀ {@0 n : ℕ} {Γ : Ctx n} {σ : Ty} → Γ ⊢ σ → Γ ⊢ σ → 𝒰 where

  var-id    : {@0 n : ℕ} {Γ : Ctx n} {A : Ty}
              {i : Γ ∋ A}
            → (` i) ⇓' (` i)

  ƛ-id      : {@0 n : ℕ} {Γ : Ctx n} {σ τ : Ty}
              {t : (σ ∷ Γ) ⊢ τ}
            → (ƛ t) ⇓' (ƛ t)

  zero-id   : {@0 n : ℕ} {Γ : Ctx n}
            → (＃_ {n} {Γ} zero) ⇓' (＃_ {n} {Γ} zero)

  𝓅-zero : {@0 n : ℕ} {Γ : Ctx n}
              {M : Γ ⊢ 𝓝}
            → M ⇓' (＃_ {n} {Γ} zero)
            → 𝓅 M ⇓' (＃_ {n} {Γ} zero)

  𝓅-suc : {@0 n : ℕ} {Γ : Ctx n}
              {M : Γ ⊢ 𝓝}
              {k : ℕ}
            → M ⇓' (＃_ {n} {Γ} (suc k))
            → 𝓅 M ⇓' (＃_ {n} {Γ} k)

  𝓈-arg  : {@0 n : ℕ} {Γ : Ctx n}
              {M : Γ ⊢ 𝓝}
              {k : ℕ}
            → M ⇓' ＃_ {n} {Γ} k
            → 𝓈 M ⇓' ＃_ {n} {Γ} (suc k)

  ?⁰-zero : {@0 n : ℕ} {Γ : Ctx n}
                {M : Γ ⊢ 𝓝} {M₁ : Γ ⊢ 𝓝} {M₂ : Γ ⊢ 𝓝}
                {V : Γ ⊢ 𝓝}
              → M ⇓' ＃_ {n} {Γ} zero
              → M₁ ⇓' V
              → (?⁰ M ↑ M₁ ↓ M₂) ⇓' V

  ?⁰-suc : {@0 n : ℕ} {Γ : Ctx n}
                {M : Γ ⊢ 𝓝} {M₁ : Γ ⊢ 𝓝} {M₂ : Γ ⊢ 𝓝}
                {V : Γ ⊢ 𝓝}
                {k : ℕ}
              → M ⇓' ＃_ {n} {Γ} (suc k)
              → M₂ ⇓' V
              → (?⁰ M ↑ M₁ ↓ M₂) ⇓' V

  Y-step  : {@0 n : ℕ} {Γ : Ctx n} {σ : Ty} {M : Γ ⊢ (σ ⇒ σ)} {V : Γ ⊢ σ}
            → (M · (Y M)) ⇓' V
            → (Y M) ⇓' V

  ·-step    : {@0 n : ℕ} {Γ : Ctx n} {σ τ : Ty}
              {M : Γ ⊢ (σ ⇒ τ)} {E : (σ ∷ Γ) ⊢ τ} {N : Γ ⊢ σ}
              {V : Γ ⊢ τ}
            → M ⇓' (ƛ E)
            → (E [ N ]) ⇓' V
            → (M · N) ⇓' V

_⇓_ : {@0 n : ℕ} {Γ : Ctx n} {σ : Ty} → Γ ⊢ σ → Γ ⊢ σ → 𝒰
M ⇓ N = ∥ M ⇓' N ∥₁

module PCF.Int.TyTerm where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Fin

open import PCF.Ty

infix  4  _⊢_
infix  5 ƛ_
infix  5 ?⁰_↑_↓_
infixl 7 _·_
infix  9 Y_
infix  9 `_
infix  9 ＃_

-- context

-- n should be irrelevant but this breaks correctness for some reason
data Ctx : ℕ → 𝒰 where
  []  : Ctx zero
  _﹐_ : ∀ {n} → Ctx n → Ty → Ctx (suc n)

-- DeBrujin index

data _∋_ : {n : ℕ} → Ctx n → Ty → 𝒰 where

  here : ∀ {n} {Γ : Ctx n} {σ}
         ------------
       → (Γ ﹐ σ) ∋ σ

  there : ∀ {n} {Γ : Ctx n} {σ τ}
        → Γ ∋ σ
          ------------
        → (Γ ﹐ τ) ∋ σ

data _⊢_ : {n : ℕ} → Ctx n → Ty → 𝒰 where

  -- Axiom
  `_ : ∀ {n} {Γ : Ctx n} {σ}
      → Γ ∋ σ
        ------
      → Γ ⊢ σ

  -- ⇒-I
  ƛ_ : ∀ {n} {Γ : Ctx n} {σ τ}
     → (Γ ﹐ σ) ⊢ τ
       ------------
     → Γ ⊢ σ ⇒ τ

  -- ⇒-E
  _·_ : ∀ {n} {Γ : Ctx n} {σ τ}
      → Γ ⊢ σ ⇒ τ
      → Γ ⊢ σ
        ----------
      → Γ ⊢ τ

  -- Y-combinator
  Y_ : ∀ {n} {Γ : Ctx n} {σ}
     → Γ ⊢ σ ⇒ σ
       ----------
     → Γ ⊢ σ

  -- constant
  ＃_ : ∀ {n} {Γ : Ctx n}
      → ℕ
        -------
      → Γ ⊢ 𝓝

  -- successor
  𝓈  : ∀ {n} {Γ : Ctx n}
     → Γ ⊢ 𝓝
       -------
     → Γ ⊢ 𝓝

  -- predecessor
  𝓅  : ∀ {n} {Γ : Ctx n}
      → Γ ⊢ 𝓝
        -------
      → Γ ⊢ 𝓝

  -- if-zero
  ?⁰_↑_↓_ : ∀ {n} {Γ : Ctx n} {σ}
    → Γ ⊢ 𝓝
    → Γ ⊢ σ
    → Γ ⊢ σ
      --------
    → Γ ⊢ σ

lookup : {n : ℕ} → Ctx n → Fin n → Ty
lookup (_ ﹐ x)  fzero   = x
lookup (Γ ﹐ _) (fsuc f) = lookup Γ f

count : {n : ℕ} {Γ : Ctx n} → (f : Fin n) → Γ ∋ lookup Γ f
count {.(suc _)} {Γ ﹐ x}  fzero   = here
count {.(suc _)} {Γ ﹐ x} (fsuc f) = there (count f)

Ren : {m n : ℕ} → Ctx m → Ctx n → 𝒰
Ren Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

extᵧ : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {σ}
    → Ren Γ Δ
      -------------------
    → Ren (Γ ﹐ σ) (Δ ﹐ σ)
extᵧ f  here       = here
extᵧ f (there x∋) = there (f x∋)

rename : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {σ}
       → Ren Γ Δ
         --------------
       → Γ ⊢ σ → Δ ⊢ σ
rename f (` x)          = ` (f x)
rename f (ƛ M)          = ƛ (rename (extᵧ f) M)
rename f (M · N)        = rename f M · rename f N
rename f (Y M)          = Y (rename f M)
rename f (＃ n)          = ＃ n
rename f (𝓈 M)          = 𝓈 (rename f M)
rename f (𝓅 M)          = 𝓅 (rename f M)
rename f (?⁰ M ↑ N ↓ P) = ?⁰ (rename f M) ↑ rename f N ↓ rename f P

Sub : {m n : ℕ} → Ctx m → Ctx n → 𝒰
Sub Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

exts : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {σ}
    → Sub Γ Δ
      -------------------
    → Sub (Γ ﹐ σ) (Δ ﹐ σ)
exts f  here      = ` here
exts f (there x∋) = rename there (f x∋)

sub : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {σ}
      → Sub Γ Δ
        --------------
      → Γ ⊢ σ → Δ ⊢ σ
sub f (` x)          = f x
sub f (ƛ M)          = ƛ (sub (exts f) M)
sub f (M · N)        = sub f M · sub f N
sub f (Y M)          = Y (sub f M)
sub f (＃ n)          = ＃ n
sub f (𝓈 M)          = 𝓈 (sub f M)
sub f (𝓅 M)          = 𝓅 (sub f M)
sub f (?⁰ M ↑ N ↓ P) = ?⁰ (sub f M) ↑ sub f N ↓ sub f P

extend-with : ∀ {m n} {Γ : Ctx m} {Δ : Ctx n} {A : Ty}
            → Δ ⊢ A
            → Sub Γ Δ
              -------------
            → Sub (Γ ﹐ A) Δ
extend-with N f  here       = N
extend-with N f (there x∋) = f x∋

replace-first : ∀ {n} {Γ : Ctx n} {A : Ty}
              → Γ ⊢ A
                -------------
              → Sub (Γ ﹐ A) Γ
replace-first N  here       = N
replace-first N (there x∋) = ` x∋

_[_] : ∀ {n} {Γ : Ctx n} {A B : Ty}
      → (Γ ﹐ A) ⊢ B
      → Γ ⊢ A
      --------------
      → Γ ⊢ B
M [ N ] = sub (replace-first N) M

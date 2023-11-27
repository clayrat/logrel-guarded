module PCF.Int.TyTerm where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Fin
open import Data.Vec

open import PCF.Ty

infix  4  _⊢_
infix  5 ƛ_
infix  5 ?⁰_↑_↓_
infixl 7 _·_
infix  9 Y_
infix  9 `_
infix  9 ＃_

-- context

Ctx : @0 ℕ → 𝒰
Ctx = Vec Ty

-- DeBrujin index

data _∋_ : {@0 n : ℕ} → Ctx n → Ty → 𝒰 where

  here : ∀ {@0 n} {Γ : Ctx n} {σ}
         ------------
       → (σ ∷ Γ) ∋ σ

  there : ∀ {@0 n} {Γ : Ctx n} {σ τ}
        → Γ ∋ σ
          ------------
        → (τ ∷ Γ) ∋ σ

data _⊢_ : {@0 n : ℕ} → Ctx n → Ty → 𝒰 where

  -- Axiom
  `_ : ∀ {@0 n} {Γ : Ctx n} {σ}
      → Γ ∋ σ
        ------
      → Γ ⊢ σ

  -- ⇒-I
  ƛ_ : ∀ {@0 n} {Γ : Ctx n} {σ τ}
     → (σ ∷ Γ) ⊢ τ
       ------------
     → Γ ⊢ σ ⇒ τ

  -- ⇒-E
  _·_ : ∀ {@0 n} {Γ : Ctx n} {σ τ}
      → Γ ⊢ σ ⇒ τ
      → Γ ⊢ σ
        ----------
      → Γ ⊢ τ

  -- Y-combinator
  Y_ : ∀ {@0 n} {Γ : Ctx n} {σ}
     → Γ ⊢ σ ⇒ σ
       ----------
     → Γ ⊢ σ

  -- constant
  ＃_ : ∀ {@0 n} {Γ : Ctx n}
      → ℕ
        -------
      → Γ ⊢ 𝓝

  -- successor
  𝓈  : ∀ {@0 n} {Γ : Ctx n}
     → Γ ⊢ 𝓝
       -------
     → Γ ⊢ 𝓝

  -- predecessor
  𝓅  : ∀ {@0 n} {Γ : Ctx n}
      → Γ ⊢ 𝓝
        -------
      → Γ ⊢ 𝓝

  -- if-zero
  ?⁰_↑_↓_ : ∀ {@0 n} {Γ : Ctx n} {σ}
    → Γ ⊢ 𝓝
    → Γ ⊢ σ
    → Γ ⊢ σ
      --------
    → Γ ⊢ σ

lookup : {@0 n : ℕ} → Ctx n → Fin n → Ty
lookup (x ∷ _)  fzero   = x
lookup (_ ∷ Γ) (fsuc f) = lookup Γ f

count : {@0 n : ℕ} {Γ : Ctx n} → (f : Fin n) → Γ ∋ lookup Γ f
count {.(suc _)} {x ∷ Γ}  fzero   = here
count {.(suc _)} {x ∷ Γ} (fsuc f) = there (count f)

Ren : {@0 m n : ℕ} → Ctx m → Ctx n → 𝒰
Ren Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

extᵧ : ∀ {@0 m n} {Γ : Ctx m} {Δ : Ctx n} {σ}
    → Ren Γ Δ
      -------------------
    → Ren (σ ∷ Γ) (σ ∷ Δ)
extᵧ f  here       = here
extᵧ f (there x∋) = there (f x∋)

rename : ∀ {@0 m n} {Γ : Ctx m} {Δ : Ctx n} {σ}
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

Sub : {@0 m n : ℕ} → Ctx m → Ctx n → 𝒰
Sub Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

exts : ∀ {@0 m n} {Γ : Ctx m} {Δ : Ctx n} {σ}
    → Sub Γ Δ
      -------------------
    → Sub (σ ∷ Γ) (σ ∷ Δ)
exts f  here      = ` here
exts f (there x∋) = rename there (f x∋)

sub : ∀ {@0 m n} {Γ : Ctx m} {Δ : Ctx n} {σ}
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

extend-with : ∀ {@0 m n} {Γ : Ctx m} {Δ : Ctx n} {A : Ty}
            → Δ ⊢ A
            → Sub Γ Δ
              -------------
            → Sub (A ∷ Γ) Δ
extend-with N f  here       = N
extend-with N f (there x∋) = f x∋

replace-first : ∀ {@0 n} {Γ : Ctx n} {A : Ty}
              → Γ ⊢ A
                -------------
              → Sub (A ∷ Γ) Γ
replace-first N  here       = N
replace-first N (there x∋) = ` x∋

_[_] : ∀ {@0 n} {Γ : Ctx n} {A B : Ty}
      → (A ∷ Γ) ⊢ B
      → Γ ⊢ A
      --------------
      → Γ ⊢ B
M [ N ] = sub (replace-first N) M

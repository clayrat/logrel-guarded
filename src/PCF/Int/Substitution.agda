module PCF.Int.Substitution where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Fin

open import PCF.Int.TyTerm

ids : {@0 n : ℕ} {Γ : Ctx n} {A : Ty} → Γ ∋ A → Γ ⊢ A
ids = `_

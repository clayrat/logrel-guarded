{-# OPTIONS --guarded #-}
module STLC.Int.NbE.Terminate where

open import Prelude hiding (apply)
open import Data.Unit
open import Later
open import Guarded.Partial
open import Guarded.Partial.Converges

open import STLC.Ty
open import STLC.Int.TyTerm
open import STLC.Int.NbE.OPE
open import STLC.Int.NbE.Norm

mutual
  V⟦_⟧ : ∀ {Γ} → (A : Ty) → Val Γ A → 𝒰
  V⟦ 𝟙 ⟧           (v-ne w) = nereadback w ⇓
  V⟦_⟧ {Γ} (A ⇒ B)  f       = ∀ {Δ} (η : Δ ≤ Γ) (u : Val Δ A) → V⟦ A ⟧ u → C⟦ B ⟧ (apply (val≤ η f) u)

  C⟦_⟧ : ∀ {Γ} → (A : Ty) → Part (Val Γ A) → 𝒰
  C⟦_⟧ {Γ} A p = Σ[ v ꞉ Val Γ A ] (p ⇓ᵖ v) × V⟦ A ⟧ v

E⟦_⟧ : ∀ {Δ} Γ → Env Δ Γ → 𝒰
E⟦ ∅ ⟧      ε       = ⊤
E⟦ Γ ﹐ A ⟧ (e 、 v) = E⟦ Γ ⟧ e × V⟦ A ⟧ v

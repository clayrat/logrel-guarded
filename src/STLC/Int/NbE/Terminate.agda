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

mutual
  val≤-id : ∀ {Δ A} → (v : Val Δ A) → val≤ id≤ v ＝ v
  val≤-id (v-ƛ t e) = ap (v-ƛ t) (env≤-id e)
  val≤-id (v-ne n)  = ap v-ne (nev≤-id n)

  env≤-id : ∀ {Γ Δ} → (ρ : Env Δ Γ) → env≤ id≤ ρ ＝ ρ
  env≤-id  ε       = refl
  env≤-id (ρ 、 v) = ap² _、_ (env≤-id ρ) (val≤-id v)

  nev≤-id : ∀ {Δ A} → (t : Ne Val Δ A) → nev≤ id≤ t ＝ t
  nev≤-id (ne-` x)   = refl
  nev≤-id (ne-· n v) = ap² ne-· (nev≤-id n) (val≤-id v)

var≤-● : ∀ {Γ Δ Η A}
       → (η : Γ ≤ Δ) (θ : Δ ≤ Η) (x : Η ∋ A)
       → var≤ η (var≤ θ x) ＝ var≤ (η ● θ) x
var≤-●  id≤       θ         x        = refl
var≤-● (weak≤ η)  θ         x        = ap there (var≤-● η θ x)
var≤-● (lift≤ η)  id≤       x        = refl
var≤-● (lift≤ η) (weak≤ θ)  x        = ap there (var≤-● η θ x)
var≤-● (lift≤ η) (lift≤ θ)  here     = refl
var≤-● (lift≤ η) (lift≤ θ) (there x) = ap there (var≤-● η θ x)

mutual
  val≤-● : ∀ {Γ Δ Η A}
         → (η : Γ ≤ Δ) (θ : Δ ≤ Η) (v : Val Η A)
         → val≤ η (val≤ θ v) ＝ val≤ (η ● θ) v
  val≤-● η θ (v-ƛ t e) = ap (v-ƛ t) (env≤-● η θ e)
  val≤-● η θ (v-ne n)  = ap v-ne (nev≤-● η θ n)

  env≤-● : ∀ {Γ Δ Η Ξ}
         → (η : Γ ≤ Δ) (θ : Δ ≤ Η) (ρ : Env Η Ξ)
         → env≤ η (env≤ θ ρ) ＝ env≤ (η ● θ) ρ
  env≤-● η θ  ε       = refl
  env≤-● η θ (ρ 、 v) = ap² _、_ (env≤-● η θ ρ) (val≤-● η θ v)

  nev≤-● : ∀ {Γ Δ Η A}
         → (η : Γ ≤ Δ) (θ : Δ ≤ Η) (t : Ne Val Η A)
         → nev≤ η (nev≤ θ t) ＝ nev≤ (η ● θ) t
  nev≤-● η θ (ne-` x)   = ap ne-` (var≤-● η θ x)
  nev≤-● η θ (ne-· n v) = ap² ne-· (nev≤-● η θ n) (val≤-● η θ v)

lookup≤ : ∀ {Γ Δ Η A} (x : Γ ∋ A) (ρ : Env Δ Γ) (η : Η ≤ Δ)
        → val≤ η (lookup x ρ) ＝ lookup x (env≤ η ρ)
lookup≤ here      (ρ 、 v) η = refl
lookup≤ (there x) (ρ 、 v) η = lookup≤ x ρ η

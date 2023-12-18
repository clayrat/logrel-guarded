module STLC.Int.NbE.OPE where

open import Prelude hiding (apply)

open import STLC.Ty
open import STLC.Int.TyTerm

data _≤_ : Ctx → Ctx → 𝒰 where
  id≤   : ∀{Γ}
        → Γ ≤ Γ
  weak≤ : ∀ {Γ Δ A}
        → Γ ≤ Δ → (Γ ﹐ A) ≤ Δ
  lift≤ : ∀ {Γ Δ A}
        → Γ ≤ Δ → (Γ ﹐ A) ≤ (Δ ﹐ A)

_●_ : ∀ {Γ Δ Η}
    → Γ ≤ Δ → Δ ≤ Η → Γ ≤ Η
id≤     ● θ       = θ
weak≤ η ● θ       = weak≤ (η ● θ)
lift≤ η ● id≤     = lift≤ η
lift≤ η ● weak≤ θ = weak≤ (η ● θ)
lift≤ η ● lift≤ θ = lift≤ (η ● θ)

η●id : ∀ {Γ Δ}
     → (η : Γ ≤ Δ)
     → η ● id≤ ＝ η
η●id  id≤      = refl
η●id (weak≤ η) = ap weak≤ (η●id η)
η●id (lift≤ x) = refl

wk : ∀ {Γ A}
   → (Γ ﹐ A) ≤ Γ
wk = weak≤ id≤

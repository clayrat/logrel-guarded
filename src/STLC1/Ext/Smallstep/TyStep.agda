module STLC1.Ext.Smallstep.TyStep where

open import Prelude
open import Data.Empty
open import Data.Dec
open import Data.String
open import Data.List

open import STLC.Ty
open import STLC1.Ext.Term
open import STLC1.Ext.TyTerm
open import STLC1.Ext.Smallstep.Step

-- substitution preserves typing

subst-ty : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B
subst-ty                 ⊢V  ⊢𝓉𝓉 = ⊢𝓉𝓉
subst-ty {Γ} {x = y}     ⊢V (⊢` {x} here) with x ≟ y
... | yes _   = weaken-∅ Γ ⊢V
... | no  x≠y = absurd (x≠y refl)
subst-ty {x = y}         ⊢V (⊢` {x} (there x≠y ∋x)) with x ≟ y
... | yes e  = absurd (x≠y e)
... | no  _   = ⊢` ∋x
subst-ty {Γ} {x = y} {A} ⊢V (⊢ƛ {x} {N} {A = C} {B} ⊢N) with x ≟ y
... | yes e  = ⊢ƛ (dropᵧ (subst (λ n → Γ , n ⦂ A , x ⦂ C ⊢ N ⦂ B) (sym e) ⊢N))
... | no  x≠y = ⊢ƛ (subst-ty ⊢V (swap x≠y ⊢N))
subst-ty                 ⊢V (⊢L ⊢· ⊢M) = (subst-ty ⊢V ⊢L) ⊢· (subst-ty ⊢V ⊢M)

-- preservation

preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve (⊢` ())
preserve (⊢ƛ ⊢N)           ()
preserve (⊢L ⊢· ⊢M)       (ξ-·₁ L→L′)   = (preserve ⊢L L→L′) ⊢· ⊢M
preserve (⊢L ⊢· ⊢M)       (ξ-·₂ _ M→M′) = ⊢L ⊢· (preserve ⊢M M→M′)
preserve ((⊢ƛ ⊢N) ⊢· ⊢V) (β-ƛ _)       = subst-ty ⊢V ⊢N

-- context invariance

free-in-ctx : ∀ {w M A Γ} → afi w M → Γ ⊢ M ⦂ A → Σ[ B ꞉ Ty ] (Γ ∋ w ⦂ B)
free-in-ctx afi-var      (⊢` {A} p) = A , p
free-in-ctx {w} (afi-abs ne a) (⊢ƛ {x} ⊢N) with (free-in-ctx a ⊢N)
... | B , here = absurd (ne refl)
... | B , there _ p = B , p
free-in-ctx (afi-appl a) (⊢L ⊢· _) = free-in-ctx a ⊢L
free-in-ctx (afi-appr a) (_ ⊢· ⊢M) = free-in-ctx a ⊢M

∅⊢-closed : ∀ {M A} → ∅ ⊢ M ⦂ A → closed M
∅⊢-closed ⊢M i a with (free-in-ctx a ⊢M)
... | (B , p) = ∅-empty p

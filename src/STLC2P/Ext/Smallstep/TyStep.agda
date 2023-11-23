module STLC2P.Ext.Smallstep.TyStep where

open import Prelude
open import Data.Empty
open import Data.Dec
open import Data.String
open import Data.List

open import STLC2P.Ext.Term
open import STLC2P.Ext.Ty
open import STLC2P.Ext.Smallstep.Step

-- substitution preserves typing

subst-ty : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B
subst-ty {Γ} {x = y}     ⊢V (⊢` {x} here) with x ≟ y
... | yes _   = weaken-∅ Γ ⊢V
... | no  x≠y = absurd (x≠y refl)
subst-ty {x = y}         ⊢V (⊢` {x} (there x≠y ∋x)) with x ≟ y
... | yes e  = absurd (x≠y e)
... | no  _   = ⊢` ∋x
subst-ty {Γ} {x = y} {A} ⊢V (⊢ƛ {x} {N} {A = C} {B} ⊢N) with x ≟ y
... | yes e  = ⊢ƛ (dropᵧ (subst (λ n → Γ , n ⦂ A , x ⦂ C ⊢ N ⦂ B) (sym e) ⊢N))
... | no  x≠y = ⊢ƛ (subst-ty ⊢V (swapᵧ x≠y ⊢N))
subst-ty                 ⊢V (⊢L ⊢· ⊢M)     = (subst-ty ⊢V ⊢L) ⊢· (subst-ty ⊢V ⊢M)
subst-ty                 ⊢V  ⊢𝓉             = ⊢𝓉
subst-ty                 ⊢V  ⊢𝒻            = ⊢𝒻
subst-ty                 ⊢V (⊢⁇ ⊢L ⊢M ⊢N) =
  ⊢⁇ (subst-ty ⊢V ⊢L) (subst-ty ⊢V ⊢M) (subst-ty ⊢V ⊢N)
subst-ty                 ⊢V (⊢〈〉 ⊢L ⊢M)     =
  ⊢〈〉 (subst-ty ⊢V ⊢L) (subst-ty ⊢V ⊢M)
subst-ty                 ⊢V (⊢⇀₁ ⊢L)       =
  ⊢⇀₁ (subst-ty ⊢V ⊢L)
subst-ty                 ⊢V (⊢⇀₂ ⊢L)       =
  ⊢⇀₂ (subst-ty ⊢V ⊢L)

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
preserve (⊢⁇ ⊢L ⊢M ⊢N)    β-𝓉          = ⊢M
preserve (⊢⁇ ⊢L ⊢M ⊢N)    β-𝒻         = ⊢N
preserve (⊢⁇ ⊢L ⊢M ⊢N)   (ξ-⁇ L→L′)    = ⊢⁇ (preserve ⊢L L→L′) ⊢M ⊢N
preserve (⊢〈〉 ⊢L ⊢M)       (ξ-〈〉₁ L→L′)   = ⊢〈〉 (preserve ⊢L L→L′) ⊢M
preserve (⊢〈〉 ⊢L ⊢M)      (ξ-〈〉₂ _ M→M′)  = ⊢〈〉 ⊢L (preserve ⊢M M→M′)
preserve (⊢⇀₁ ⊢L)         (ξ-⇀₁ L→L′)   = ⊢⇀₁ (preserve ⊢L L→L′)
preserve (⊢⇀₁ (⊢〈〉 ⊢N ⊢M)) (β-〈〉₁ _ _)   = ⊢N
preserve (⊢⇀₂ ⊢L)         (ξ-⇀₂ L→L′)   = ⊢⇀₂ (preserve ⊢L L→L′)
preserve (⊢⇀₂ (⊢〈〉 ⊢L ⊢N)) (β-〈〉₂ _ _)   = ⊢N

multi-preserve : ∀ {M N A}
               → ∅ ⊢ M ⦂ A
               → M —↠ N
                 ----------
               → ∅ ⊢ N ⦂ A
multi-preserve ⊢M (_ ∎ᵣ)         = ⊢M
multi-preserve ⊢M (_ —→⟨ S ⟩ MS) = multi-preserve (preserve ⊢M S) MS

-- context invariance

free-in-ctx : ∀ {w M A Γ} → afi w M → Γ ⊢ M ⦂ A → Σ[ B ꞉ Ty ] (Γ ∋ w ⦂ B)
free-in-ctx afi-var       (⊢` {A} p)   = A , p
free-in-ctx {w} (afi-abs ne a) (⊢ƛ {x} ⊢N) with (free-in-ctx a ⊢N)
... | B , here = absurd (ne refl)
... | B , there _ p = B , p
free-in-ctx (afi-appl a)  (⊢L ⊢· _)   = free-in-ctx a ⊢L
free-in-ctx (afi-appr a)  (_ ⊢· ⊢M)   = free-in-ctx a ⊢M
free-in-ctx (afi-test0 a) (⊢⁇ ⊢L _ _) = free-in-ctx a ⊢L
free-in-ctx (afi-test1 a) (⊢⁇ _ ⊢M _) = free-in-ctx a ⊢M
free-in-ctx (afi-test2 a) (⊢⁇ _ _ ⊢N) = free-in-ctx a ⊢N
free-in-ctx (afi-pairl a) (⊢〈〉 ⊢L _)   = free-in-ctx a ⊢L
free-in-ctx (afi-pairr a) (⊢〈〉 _ ⊢M)   = free-in-ctx a ⊢M
free-in-ctx (afi-fst a)   (⊢⇀₁ ⊢L)    = free-in-ctx a ⊢L
free-in-ctx (afi-snd a)   (⊢⇀₂ ⊢L)    = free-in-ctx a ⊢L

∅⊢-closed : ∀ {M A} → ∅ ⊢ M ⦂ A → closed M
∅⊢-closed ⊢M i a with (free-in-ctx a ⊢M)
... | (B , p) = ∅-empty p

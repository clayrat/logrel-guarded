module STLC1.Int.NbE.CtxExt where

open import Prelude
open import Data.Empty
open import Data.Dec

open import STLC1.Int.TyTerm

infix 4 _≤_

-- context extension, a special case of an OPE

data _≤_ : Ctx → Ctx → 𝒰 where
  ≤-id : ∀ {Γ Δ : Ctx}
       → Γ ＝ Δ   -- fording because we don't have K
       → Γ ≤ Δ

  ≤-ext : ∀ {Γ Δ : Ctx} {T : Ty}
        → Γ ≤ Δ
          ----------
        → Γ ﹐ T ≤ Δ

¬∅≤, : ∀ {Γ T} → ¬ (∅ ≤ Γ ﹐ T)
¬∅≤, (≤-id e) = ∅≠, e

Γ≤∅ : ∀ {Γ : Ctx} → Γ ≤ ∅
Γ≤∅ {Γ = ∅} = ≤-id refl
Γ≤∅ {Γ ﹐ _} = ≤-ext Γ≤∅

invert-≤ : ∀ {Γ Δ : Ctx} {T : Ty}
         → Γ ≤ Δ ﹐ T
           ----------
         → Γ ≤ Δ
invert-≤ {Δ} (≤-id e)  = subst (_≤ Δ) (sym e) (≤-ext (≤-id refl))
invert-≤     (≤-ext p) = ≤-ext (invert-≤ p)

mutual
  ≤-antisym : ∀ {Γ Δ : Ctx}
            → Γ ≤ Δ
            → Δ ≤ Γ
              ------
            → Γ ＝ Δ
  ≤-antisym (≤-id e)            _                         = e
  ≤-antisym (≤-ext p1)         (≤-id e)                   = sym e
  ≤-antisym (≤-ext {Γ} {T} p1) (≤-ext {Γ = Δ} {T = S} p2) =
    let Γ=Δ = ≤-antisym (invert-≤ p1) (invert-≤ p2) in
    ap (_﹐ T) Γ=Δ
    ∙ ap (Δ ﹐_) (≤-ext-uniq-T p2 (subst (_≤ Γ ﹐ S) Γ=Δ (subst (λ q → Γ ≤ q ﹐ S) (sym Γ=Δ) p1)))

  Γ≰Γ,T : ∀ {Γ : Ctx} {T : Ty} → ¬ (Γ ≤ Γ ﹐ T)
  Γ≰Γ,T {Γ} {T} Γ≤Γ,T = absurd (Ctx-ne-ext $ ≤-antisym Γ≤Γ,T $ ≤-ext {T = T} (≤-id refl))

  ≤-ext-uniq-T : ∀ {Γ Δ : Ctx} {S T : Ty}
               → Δ ≤ Γ ﹐ T
               → Δ ≤ Γ ﹐ S
                 ----------
               → T ＝ S
  ≤-ext-uniq-T         (≤-id e1)  (≤-id e2)  = ,-inj (sym e1 ∙ e2) .snd
  ≤-ext-uniq-T {Γ} {S} (≤-id e1)  (≤-ext p2) = absurd (Γ≰Γ,T (subst (_≤ Γ ﹐ S) (,-inj e1 .fst) p2))
  ≤-ext-uniq-T {Γ} {T} (≤-ext p1) (≤-id e2)  = absurd (Γ≰Γ,T (subst (_≤ Γ ﹐ T) (,-inj e2 .fst) p1))
  ≤-ext-uniq-T         (≤-ext p1) (≤-ext p2) = ≤-ext-uniq-T p1 p2

≤-is-prop : ∀ Γ Δ → is-prop (Γ ≤ Δ)
≤-is-prop Γ Δ = is-prop-η (go Γ Δ)
  where
  go : ∀ Γ Δ → (p1 p2 : Γ ≤ Δ) → p1 ＝ p2
  go  Γ        Δ (≤-id e1)      (≤-id e2)      = ap ≤-id (is-set-β Ctx-is-set Γ Δ e1 e2)
  go .(Γ ﹐ _) Δ (≤-id e1)      (≤-ext {Γ} p2) = absurd (Γ≰Γ,T (subst (Γ ≤_) (sym e1) p2))
  go .(Γ ﹐ _) Δ (≤-ext {Γ} p1) (≤-id e2)      = absurd (Γ≰Γ,T (subst (Γ ≤_) (sym e2) p1))
  go .(Γ ﹐ _) Δ (≤-ext {Γ} p1) (≤-ext p2)     = ap ≤-ext (go Γ Δ p1 p2)

≤-trans : ∀ {Γ Δ Φ : Ctx}
         → Γ ≤ Δ
         → Δ ≤ Φ
           -------
         → Γ ≤ Φ
≤-trans     (≤-id e1)  (≤-id e2)  = ≤-id (e1 ∙ e2)
≤-trans {Φ} (≤-id e1)  (≤-ext ΔΦ) = subst (_≤ Φ) (sym e1) (≤-ext ΔΦ)
≤-trans {Γ} (≤-ext ΓΔ) (≤-id e2)  = subst (Γ ≤_) e2 (≤-ext ΓΔ)
≤-trans     (≤-ext ΓΔ) (≤-ext ΔΦ) = ≤-ext (≤-trans ΓΔ (≤-ext ΔΦ))

_≤?_ : ∀ (Γ Δ : Ctx) → Dec (Γ ≤ Δ)
∅       ≤?    ∅      = yes (≤-id refl)
∅       ≤?   (Δ ﹐ S) = no ¬∅≤,
(Γ ﹐ T) ≤?    ∅      = yes Γ≤∅
(Γ ﹐ T) ≤? Δ@(Δ₁ ﹐ S) with (Γ ﹐ T) ≟ Δ
... | yes prf = yes (≤-id prf)
... | no ctra with Γ ≤? Δ
...           | yes prf2 = yes (≤-ext prf2)
...           | no ctra2 = no λ where
                                 (≤-id e)  → absurd (ctra e)
                                 (≤-ext p) → ctra2 p

module STLC1.Int.NbE.Soundness where

open import Prelude hiding ([_])
open import Data.Empty
open import Data.Maybe renaming (rec to mrec)

open import STLC1.Int.TyTerm
open import STLC1.Int.NbE.CtxExt
open import STLC1.Int.NbE.Subst
open import STLC1.Int.NbE.Norm
open import STLC1.Int.NbE.DefEq

infix 3 _==^_
infix 3 _==⊤̂_
infix 4 _Ⓡ_

_==^_ : {Γ : Ctx} {T : Ty} → Γ ⊢ T → Ne^ T → 𝒰
_==^_ {Γ} t 𝓊̂ = mrec ⊥ (λ 𝓊-ne → t == 𝓊-ne .fst) (𝓊̂ Γ)

_==⊤̂_ : ∀ {Γ : Ctx} → Γ ⊢ 𝟙 → ⟦ 𝟙 ⟧ᵗ → 𝒰
_==⊤̂_ {Γ} t  unit   = t == 𝓉𝓉
_==⊤̂_ {Γ} t (ne 𝓊̂) = t ==^ 𝓊̂

_Ⓡ_ : ∀ {Γ : Ctx} {T : Ty} → Γ ⊢ T → ⟦ T ⟧ᵗ → 𝒰
_Ⓡ_ {Γ} {T = 𝟙} t 𝓋̂ =
    ∀ {Γ′ : Ctx}
    → (Γ′≤Γ : Γ′ ≤ Γ)
    → Γ′≤Γ ≤⊢ t ==⊤̂ 𝓋̂
_Ⓡ_ {Γ} {S ⇒ T} r f =
    ∀ {Γ′ : Ctx}
    → (Γ′≤Γ : Γ′ ≤ Γ)
    → ∀ {s : Γ′ ⊢ S} {a : ⟦ S ⟧ᵗ}
    → s Ⓡ a
    → (Γ′≤Γ ≤⊢ r) · s Ⓡ f a

==-Ⓡ-trans : ∀ {Γ : Ctx} {T : Ty} {t t′ : Γ ⊢ T} {a : ⟦ T ⟧ᵗ}
           → t == t′
           → t Ⓡ a
             -------
           → t′ Ⓡ a
==-Ⓡ-trans {T = 𝟙}     {t} {t′} {a = unit} t==t′ pf      Γ′≤Γ      =
    begin==
  Γ′≤Γ ≤⊢ t′
    ==⟨ sym⁼⁼ (cong⁼⁼-sub t==t′) ⟩
  Γ′≤Γ ≤⊢ t
    ==⟨ pf Γ′≤Γ ⟩
  𝓉𝓉
    ==∎
==-Ⓡ-trans {T = 𝟙}     {t} {t′} {a = ne 𝓊̂} t==t′ pf {Γ′} Γ′≤Γ     = go (pf Γ′≤Γ)
  where
  go : Γ′≤Γ ≤⊢ t ==^ 𝓊̂ → Γ′≤Γ ≤⊢ t′ ==^ 𝓊̂
  go pf′ with 𝓊̂ Γ′
  ... | just (𝓊 , _) =
           begin==
         Γ′≤Γ ≤⊢ t′
           ==⟨ sym⁼⁼ (cong⁼⁼-sub t==t′) ⟩
         Γ′≤Γ ≤⊢ t
           ==⟨ pf′ ⟩
         𝓊
           ==∎
==-Ⓡ-trans {T = S ⇒ T}          {a}        r==r′ pf      Γ′≤Γ sⓇa =
  ==-Ⓡ-trans r·s==r′·s r·sⓇfa
  where
    r·s==r′·s = app-compat (cong⁼⁼-sub r==r′) refl⁼⁼
    r·sⓇfa = pf Γ′≤Γ sⓇa

module STLC1.Int.NbE.DefEq where

open import Prelude hiding ([_])
open import Data.Empty
open import Data.Dec

open import STLC1.Int.TyTerm
open import STLC1.Int.NbE.CtxExt
open import STLC1.Int.NbE.Subst

infix  3 _==_
infix  8 _[_]₀

_[_]₀ : ∀ {Γ : Ctx} {S T : Ty}
  → Γ ﹐ S ⊢ T
  → Γ ⊢ S
    ---------
  → Γ ⊢ T
_[_]₀ {Γ} {S} t s = t [ idˢ ∷ˢ s ]

η-expand : ∀ {Γ : Ctx} {S T : Ty}
         → Γ ⊢ S ⇒ T
         → Γ ⊢ S ⇒ T
η-expand {S} t = ƛ (S ↥⊢ t) · ` here

data _==_ : ∀ {Γ : Ctx} {T : Ty} → Γ ⊢ T → Γ ⊢ T → 𝒰 where
  -- computation rule: beta reduction
  β : ∀ {Γ : Ctx} {S T : Ty}
        {t : Γ ﹐ S ⊢ T}
        {s : Γ ⊢ S}
       ----------------------
     → (ƛ t) · s == t [ s ]₀

  -- η-expansion / function extensionality, i.e. Γ ⊢ t = Γ ⊢ λx. t x : S ⇒ T
  η : ∀ {Γ : Ctx} {S T : Ty}
        {t : Γ ⊢ S ⇒ T}
      ----------------------
    → t == η-expand t

  -- compatibility rules
  abs-compat : ∀ {Γ : Ctx} {S T : Ty} {t t′ : Γ ﹐ S ⊢ T}
             → t == t′
               -----------
             → ƛ t == ƛ t′

  app-compat : ∀ {Γ : Ctx} {S T : Ty}
                 {r r′ : Γ ⊢ S ⇒ T} {s s′ : Γ ⊢ S}
             → r == r′
             → s == s′
               ----------------
             → r · s == r′ · s′

  -- equivalence rules
  refl⁼⁼ : ∀ {Γ : Ctx} {T : Ty} {t : Γ ⊢ T}
          ------
        → t == t

  sym⁼⁼ : ∀ {Γ : Ctx} {T : Ty} {t t′ : Γ ⊢ T}
       → t == t′
         -------
       → t′ == t

  trans⁼⁼ : ∀ {Γ : Ctx} {T : Ty} {t₁ t₂ t₃ : Γ ⊢ T}
         → t₁ == t₂
         → t₂ == t₃
           --------
         → t₁ == t₃

module ==-Reasoning where

  infix  1 begin==_
  infixr 2 _==⟨_⟩_
  infix  3 _==∎

  begin==_ : ∀ {Γ : Ctx} {T : Ty} {t t′ : Γ ⊢ T}
           → t == t′
             -------
           → t == t′
  begin== pf = pf

  _==⟨_⟩_ : ∀ {Γ : Ctx} {T : Ty} {t₂ t₃ : Γ ⊢ T}
         → (t₁ : Γ ⊢ T)
         → t₁ == t₂
         → t₂ == t₃
           --------
         → t₁ == t₃
  t₁ ==⟨ t₁==t₂ ⟩ t₂==t₃ = trans⁼⁼ t₁==t₂ t₂==t₃

  _==∎ : ∀ {Γ : Ctx} {T : Ty}
       → (t : Γ ⊢ T)
         ------
       → t == t
  t ==∎ = refl⁼⁼

open ==-Reasoning public

＝→== : ∀ {Γ : Ctx} {T : Ty} {t t′ : Γ ⊢ T}
      → t ＝ t′
        -------
      → t == t′
＝→== {t} e = subst (t ==_) e refl⁼⁼

cong⁼⁼-sub : ∀ {Γ Δ : Ctx} {T : Ty} {t t′ : Γ ⊢ T} {σ : Sub Δ Γ}
          → t == t′
          → t [ σ ] == t′ [ σ ]
cong⁼⁼-sub                     {σ} (β {t} {s})              =
  trans⁼⁼ β
    (＝→== (sub-sub {t = t}
            ∙ cong-sub {t = t} (subst-zero-exts-cons ∙ sym sub-dist)
                                refl
            ∙ sym (sub-sub {τ = σ} {idˢ ∷ˢ s} {t})))
cong⁼⁼-sub {Γ} {T = S ⇒ T} {t} {σ}  η                       =
  trans⁼⁼ η
    (abs-compat
      (app-compat
         (＝→== (  sub-sub {τ = ↥} {σ} {t}
                 ∙ cong-sub {t = t} (fun-ext (λ _ → sym rename-shift)) refl
                 ∙ sym (sub-sub {τ = exts σ} {↥ {T = S}} {t})
                 ))
         refl⁼⁼))
cong⁼⁼-sub                         (abs-compat t==t′)       =
  abs-compat (cong⁼⁼-sub t==t′)
cong⁼⁼-sub                         (app-compat r==r′ s==s′) =
  app-compat (cong⁼⁼-sub r==r′) (cong⁼⁼-sub s==s′)
cong⁼⁼-sub                          refl⁼⁼                   =
  refl⁼⁼
cong⁼⁼-sub                         (sym⁼⁼ t′==t)             =
  sym⁼⁼ (cong⁼⁼-sub t′==t)
cong⁼⁼-sub                         (trans⁼⁼ t==t₁ t₁==t′)    =
  trans⁼⁼ (cong⁼⁼-sub t==t₁) (cong⁼⁼-sub t₁==t′)

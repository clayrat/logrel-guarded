module STLC1.Int.NbE.Completeness where

open import Prelude hiding ([_])

open import STLC1.Int.TyTerm
open import STLC1.Int.NbE.CtxExt
open import STLC1.Int.NbE.Subst
open import STLC1.Int.NbE.Norm
open import STLC1.Int.NbE.DefEq

_⊩ʳ_~_ : ∀ {Γ Δ : Ctx} → ⟦ Γ ⟧ᶜ → Ren Γ Δ → ⟦ Δ ⟧ᶜ → 𝒰
_⊩ʳ_~_ {Δ} γ ρ δ = ∀ {T : Ty} (x : Δ ∋ T) → env-lookup (ρ x) γ ＝ env-lookup x δ

rename-preserves-meaning : ∀ {Γ Δ : Ctx} {T : Ty} {γ : ⟦ Γ ⟧ᶜ} {δ : ⟦ Δ ⟧ᶜ}
                             {t : Δ ⊢ T} {ρ : Ren Γ Δ}
                         → γ ⊩ʳ ρ ~ δ
                         → ⟦⊢ t [ ρ ]ʳ ⟧ γ ＝ ⟦⊢ t ⟧ δ
rename-preserves-meaning                     {t = 𝓉𝓉}        pf = refl
rename-preserves-meaning                     {t = ` x}       pf = pf x
rename-preserves-meaning {Δ} {S ⇒ T} {γ} {δ} {t = ƛ t}   {ρ} pf =
  fun-ext λ a → rename-preserves-meaning {t = t} go
  where
  go : {a : ⟦ S ⟧ᵗ} {T : Ty}
     → (x : Δ ﹐ S ∋ T)
     → env-lookup (ext ρ x) (γ , a) ＝ env-lookup x (δ , a)
  go  here     = refl
  go (there x) = pf x
rename-preserves-meaning             {γ} {δ} {t = r · s} {ρ} pf =
    ap (⟦⊢ r [ ρ ]ʳ ⟧ γ) (rename-preserves-meaning {t = s} pf)
  ∙ ap (λ q → q (⟦⊢ s ⟧ δ)) (rename-preserves-meaning {t = r} pf)

_⊩_~_ : ∀ {Γ Δ : Ctx}
      → ⟦ Γ ⟧ᶜ → Sub Γ Δ → ⟦ Δ ⟧ᶜ → 𝒰
_⊩_~_ {Δ} γ σ δ = ∀ {T : Ty} (x : Δ ∋ T) → ⟦⊢ σ x ⟧ γ ＝ env-lookup x δ

subst-exts : ∀ {Γ Δ : Ctx} {S : Ty} {γ : ⟦ Γ ⟧ᶜ} {a : ⟦ S ⟧ᵗ} {σ : Sub Γ Δ}
               {δ : ⟦ Δ ⟧ᶜ}
           → γ ⊩ σ ~ δ
           → (γ , a) ⊩ exts σ ~ (δ , a)
subst-exts     pf  here     = refl
subst-exts {σ} pf (there x) =
  rename-preserves-meaning {t = σ x} (λ _ → refl) ∙ pf x

subst-preserves-meaning : ∀ {Γ Δ : Ctx} {T : Ty} {γ : ⟦ Γ ⟧ᶜ} {δ : ⟦ Δ ⟧ᶜ}
                            {σ : Sub Γ Δ} {t : Δ ⊢ T}
                        → γ ⊩ σ ~ δ
                        → ⟦⊢ t [ σ ] ⟧ γ ＝ ⟦⊢ t ⟧ δ
subst-preserves-meaning             {t = 𝓉𝓉}    pf = refl
subst-preserves-meaning             {t = ` x}   pf = pf x
subst-preserves-meaning             {t = ƛ t}   pf =
  fun-ext λ a → subst-preserves-meaning {t = t} (subst-exts pf)
subst-preserves-meaning {γ} {δ} {σ} {t = r · s} pf =
    ap (⟦⊢ r [ σ ] ⟧ γ) (subst-preserves-meaning {t = s} pf)
  ∙ ap (λ q → q (⟦⊢ s ⟧ δ)) (subst-preserves-meaning {t = r} pf)

β-preserves-meaning : ∀ {Γ : Ctx} {S T : Ty} {γ : ⟦ Γ ⟧ᶜ} {s : Γ ⊢ S}
                        {t : Γ ﹐ S ⊢ T}
                    → ⟦⊢ t ⟧ (γ , ⟦⊢ s ⟧ γ) ＝ ⟦⊢ t [ s ]₀ ⟧ γ
β-preserves-meaning {Γ} {S} {γ} {s} {t}  =
  sym (subst-preserves-meaning {γ = γ} {γ , is} {idˢ ∷ˢ s} {t} go)
  where
  is : ⟦ S ⟧ᵗ
  is = ⟦⊢ s ⟧ γ
  go : ∀ {T : Ty}
     → (x : Γ ﹐ S ∋ T)
     → ⟦⊢ (idˢ ∷ˢ s) x ⟧ γ ＝ env-lookup x (γ , is)
  go  here     = refl
  go (there x) = refl

↥-preserves-meaning : ∀ {Γ : Ctx} {S T : Ty} {t : Γ ⊢ T} {γ : ⟦ Γ ⟧ᶜ}
                        {a : ⟦ S ⟧ᵗ}
                    → ⟦⊢ t ⟧ γ ＝ ⟦⊢ t [ ↥ ] ⟧ (γ , a)
↥-preserves-meaning {t = t} {γ} {a} =
  sym (subst-preserves-meaning {γ = γ , a} {γ} {↥} {t} λ _ → refl)

==→⟦＝⟧ : ∀ {Γ : Ctx} {T : Ty} {t t′ : Γ ⊢ T} {γ : ⟦ Γ ⟧ᶜ}
       → t == t′
       → ⟦⊢ t ⟧ γ ＝ ⟦⊢ t′ ⟧ γ
==→⟦＝⟧ {γ}     (β {t} {s})                       =
  β-preserves-meaning {γ = γ} {s} {t}
==→⟦＝⟧ {t} {γ}  η                                =
  fun-ext λ a → ap (λ q → q a) (↥-preserves-meaning {t = t} {γ})
==→⟦＝⟧         (abs-compat t==t′)                =
  fun-ext λ a → ==→⟦＝⟧ t==t′
==→⟦＝⟧     {γ} (app-compat {r} {s′} r==r′ s==s′) =
    ap (⟦⊢ r ⟧ γ) (==→⟦＝⟧ s==s′)
  ∙ ap (λ q → q (⟦⊢ s′ ⟧ γ)) (==→⟦＝⟧ r==r′)
==→⟦＝⟧          refl⁼⁼                            =
  refl
==→⟦＝⟧         (sym⁼⁼ t==t′)                      =
  sym (==→⟦＝⟧ t==t′)
==→⟦＝⟧         (trans⁼⁼ t==t₁ t₁==t′)             =
  ==→⟦＝⟧ t==t₁ ∙ ==→⟦＝⟧ t₁==t′

completeness : ∀ {Γ : Ctx} {T : Ty} {t t′ : Γ ⊢ T}
             → t == t′
             → nf t ＝ nf t′
completeness {Γ} t==t′ =
  ap (λ q → ↓ᵀ q Γ .fst) (==→⟦＝⟧ {γ = ↑ᶜ Γ} t==t′)

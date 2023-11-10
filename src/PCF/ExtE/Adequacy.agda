{-# OPTIONS --guarded #-}
module PCF.ExtE.Adequacy where

open import Prelude hiding (_⊆_)
open import Data.Empty
open import Data.Dec
open import Data.Nat hiding (_·_)
open import Data.List
open import Data.String

open import Later
open import Interlude
open import Guarded.Partial
open import PCF.ExtE.TyTerm
open import PCF.ExtE.TyDeriv
open import PCF.ExtE.Bigstep
open import PCF.ExtE.Smallstep
open import PCF.ExtE.SmallstepTy
open import PCF.ExtE.Correspondence
open import PCF.ExtE.Denot

𝓡𝓝-case : (▹ Part ℕ → Term → ▹ 𝒰) → Part ℕ → Term → 𝒰
𝓡𝓝-case 𝓡▹ (now v)    M = M ⇓⁅ 0 ⁆ᵛ v-＃ v
𝓡𝓝-case 𝓡▹ (later r▹) M = Σ[ M′ ꞉ Term ] (Σ[ M″ ꞉ Term ] (M —↠⁰ M′) × (M′ —→⁅ s¹ ⁆ M″) × ▸ 𝓡▹ r▹ M″)

𝓡𝓝-body : ▹ (Part ℕ → Term → 𝒰) → Part ℕ → Term → 𝒰
𝓡𝓝-body 𝓡▹ = 𝓡𝓝-case (λ r▹ M → 𝓡▹ ⊛ r▹ ⊛ next M)

𝓡𝓝 : Part ℕ → Term → 𝒰
𝓡𝓝 = fix 𝓡𝓝-body

𝓡𝓝-now : ∀ {M v}
        → M ⇓⁅ 0 ⁆ᵛ v-＃ v
        → 𝓡𝓝 (now v) M
𝓡𝓝-now = id

𝓡𝓝-⇉later : ∀ {M r▹} (M′ M″ : Term)
            → (M —↠⁰ M′)
            → (M′ —→⁅ s¹ ⁆ M″)
            → ▸ (▹map 𝓡𝓝 r▹ ⊛ next M″)
            → 𝓡𝓝 (later r▹) M
𝓡𝓝-⇉later {M} {r▹} M′ M″ S1 S2 S▹ =
  M′ , M″ , S1 , S2 , transport (λ i → ▹[ α ] pfix 𝓡𝓝-body (~ i) α (r▹ α) M″) S▹

𝓡𝓝-later⇉ : ∀ {M r▹}
            → 𝓡𝓝 (later r▹) M
            → Σ[ M′ ꞉ Term ] (Σ[ M″ ꞉ Term ] (M —↠⁰ M′) × (M′ —→⁅ s¹ ⁆ M″) × ▸ (▹map 𝓡𝓝 r▹ ⊛ next M″))
𝓡𝓝-later⇉ {M} {r▹} (M′ , M″ , S1 , S2 , S▹) =
  M′ , M″ , S1 , S2 , transport (λ i → ▹[ α ] pfix 𝓡𝓝-body i α (r▹ α) M″) S▹

𝓡 : (τ : Ty) → 𝒯⟦ τ ⟧ → Term → 𝒰
𝓡 (S ⇒ T)  f         M = (σ : 𝒯⟦ S ⟧) → (N : Term) → 𝓡 S σ N → 𝓡 T (f σ) (M · N)
𝓡 𝓝                   = 𝓡𝓝

-- 2.25

-- 2.26

-- 2.27.1

step-𝓡 : ∀ {M N T σ}
        → M —→⁅ s⁰ ⁆ N
        → 𝓡 T σ N
        → 𝓡 T σ M
step-𝓡 {M} {N} {T = 𝓝}    {σ = now v}    st R         =
  small⁰-big M N (λ w l → (l ＝ 0) × (w ＝ v-＃ v)) st R
step-𝓡 {M}     {T = 𝓝}    {σ = later r▹} st R         =
  let (M′ , M″ , S1 , S2 , S▹) = 𝓡𝓝-later⇉ R in
  𝓡𝓝-⇉later M′ M″ (M —→⟨ st ⟩ S1) S2 S▹
step-𝓡 {M} {N} {T = S ⇒ T} {σ = ϕ}        st Rf σ P RP =
  step-𝓡 {M = M · P} {N = N · P} {T} {σ = ϕ σ} (ξ-· st) (Rf σ P RP)

-- 2.27.2

step-𝓡-rev : ∀ {M N T σ}
        → M —→⁅ s⁰ ⁆ N
        → 𝓡 T σ M
        → 𝓡 T σ N
step-𝓡-rev         {T = 𝓝}    {σ = now v}    st R         =
  {!!}
step-𝓡-rev         {T = 𝓝}    {σ = later r▹} st R         =
  let (M′ , M″ , S1 , S2 , S▹) = 𝓡𝓝-later⇉ R in
  𝓡𝓝-⇉later M′ M″ {!!} S2 S▹
step-𝓡-rev {M} {N} {T = S ⇒ T} {σ = ϕ}        st Rf σ P RP =
  step-𝓡-rev {M = M · P} {N = N · P} {T} {σ = ϕ σ} (ξ-· st) (Rf σ P RP)


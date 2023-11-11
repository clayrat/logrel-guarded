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

𝓡 : (T : Ty) → 𝒯⟦ T ⟧ → Term → 𝒰
𝓡 (S ⇒ T)  f         M = (σ : 𝒯⟦ S ⟧) → (N : Term) → 𝓡 S σ N → 𝓡 T (f σ) (M · N)
𝓡 𝓝                   = 𝓡𝓝

-- 2.25

-- 2.26

-- 2.27.1

step-𝓡 : ∀ {M N T τ}
        → M —→⁅ s⁰ ⁆ N
        → 𝓡 T τ N
        → 𝓡 T τ M
step-𝓡 {M} {N} {T = 𝓝}    {τ = now v}    st R         =
  small⁰-big M N (λ w l → (l ＝ 0) × (w ＝ v-＃ v)) st R
step-𝓡 {M}     {T = 𝓝}    {τ = later r▹} st R         =
  let (M′ , M″ , S1 , S2 , S▹) = 𝓡𝓝-later⇉ R in
  𝓡𝓝-⇉later M′ M″ (M —→⟨ st ⟩ S1) S2 S▹
step-𝓡 {M} {N} {T = S ⇒ T} {τ = ϕ}        st Rf σ P RP =
  step-𝓡 {M = M · P} {N = N · P} {T} {τ = ϕ σ} (ξ-· st) (Rf σ P RP)

-- 2.27.2

step-𝓡-rev : ∀ {M N T τ}
            → M —→⁅ s⁰ ⁆ N
            → 𝓡 T τ M
            → 𝓡 T τ N
step-𝓡-rev {M} {N} {T = 𝓝}    {τ = now v}    st R         with big→small-rtc-v M (＃ v) (v-＃ v) is-＃ R
... | M , (.M ∎ᵣ)         , isV = absurd (¬#—→ (subst (λ q → q —→⁅ s⁰ ⁆ N) isV st))
... | V , (.M —→⟨ S ⟩ MV) , isV =
        small-rtc→big-v N (＃ v) (v-＃ v) is-＃
                        (V , subst (λ q -> q —↠⁰ V) (snd (step-det M s⁰ _ s⁰ N S st)) MV , isV)
step-𝓡-rev {M} {N} {T = 𝓝}    {τ = later r▹} st R         with 𝓡𝓝-later⇉ R
... | .M , M″ , (.M ∎ᵣ)           , S2 , S▹ = absurd (s⁰≠s¹ (fst (step-det M s⁰ N s¹ M″ st S2)))
... | M′ , M″ , (.M —→⟨ S1 ⟩ S1′) , S2 , S▹ =
         𝓡𝓝-⇉later M′ M″
                    (subst (λ q → q —↠⁰ M′) (snd (step-det M s⁰ _ s⁰ N S1 st)) S1′) S2 S▹
step-𝓡-rev {M} {N} {T = S ⇒ T} {τ = ϕ}        st Rf σ P RP =
  step-𝓡-rev {M = M · P} {N = N · P} {T} {τ = ϕ σ} (ξ-· st) (Rf σ P RP)

-- 2.28

-- multisubstitution

Env : 𝒰
Env = List (Id × Term)

msubst : Env → Term → Term
msubst []             t = t
msubst ((x , s) ∷ ss) t = msubst ss (t [ x := s ])

-- lemmas

msubst-＃ : ∀ {E n}
          → msubst E (＃ n) ＝ ＃ n
msubst-＃ {E = []}    = refl
msubst-＃ {E = x ∷ E} = msubst-＃ {E}

msubst-𝓈 : ∀ {E M}
          → msubst E (𝓈 M) ＝ 𝓈 (msubst E M)
msubst-𝓈 {E = []}              = refl
msubst-𝓈 {E = (x , N) ∷ E} {M} = msubst-𝓈 {E} {M = M [ x := N ]}

msubst-𝓅 : ∀ {E M}
          → msubst E (𝓅 M) ＝ 𝓅 (msubst E M)
msubst-𝓅 {E = []}              = refl
msubst-𝓅 {E = (x , N) ∷ E} {M} = msubst-𝓅 {E} {M = M [ x := N ]}

data Inst : Ctx → Env → 𝒰 where
  I-nil  : Inst ∅ []
  I-cons : ∀ {x T N Γ E}
         → (τ : 𝒯⟦ T ⟧)
         → 𝓡 T τ N
         → Inst Γ E
         → Inst (Γ , x ⦂ T) ((x , N) ∷ E)

Inst-𝒞 : ∀ {Γ E}
       → Inst Γ E
       → 𝒞⟦ Γ ⟧
Inst-𝒞 (I-cons τ _ i) = Inst-𝒞 i ＆ τ

Inst-𝒞-nil : Inst-𝒞 I-nil ＝ 𝒞∅
Inst-𝒞-nil = fun-ext λ S → fun-ext λ y → fun-ext λ ()

𝓡𝓝𝓈 : (T : Part ℕ) → (M : Term) → 𝓡𝓝 T M → 𝓡𝓝 (mapᵖ suc T) (𝓈 M)
𝓡𝓝𝓈 = fix λ ih▹ → λ where
  (now v) M RT →
    ⇓-covariant (λ w l → (l ＝ 0) × (w ＝ v-＃ v)) (Q𝓈 (λ w l → (l ＝ 0) × (w ＝ v-＃ (suc v))))
                (λ w n e → v , snd e , fst e , refl)
                M 0 RT
  (later r▹) M RT →
     let (M′ , M″ , S1 , S2 , S▹) = 𝓡𝓝-later⇉ RT in
     𝓡𝓝-⇉later (𝓈 M′) (𝓈 M″) (—↠⁰-𝓈 S1) (ξ-𝓈 S2)
                 (λ α → ih▹ α (r▹ α) M″ (S▹ α))  -- ⊛ fails

𝓡𝓝𝓅 : (T : Part ℕ) → (M : Term) → 𝓡𝓝 T M → 𝓡𝓝 (mapᵖ pred T) (𝓅 M)
𝓡𝓝𝓅 = fix λ ih▹ → λ where
  (now v) M RT →
    ⇓-covariant (λ w l → (l ＝ 0) × (w ＝ v-＃ v)) (Q𝓅 (λ w l → (l ＝ 0) × (w ＝ v-＃ (pred v))))
                (λ w n e → v , snd e , fst e , refl)
                M 0 RT
  (later r▹) M RT →
     let (M′ , M″ , S1 , S2 , S▹) = 𝓡𝓝-later⇉ RT in
     𝓡𝓝-⇉later (𝓅 M′) (𝓅 M″) (—↠⁰-𝓅 S1) (ξ-𝓅 S2)
                 (λ α → ih▹ α (r▹ α) M″ (S▹ α))  -- ⊛ fails

fundamental-lemma : ∀ {Γ E M T}
                  → (I : Inst Γ E)
                  → (⊢M : Γ ⊢ M ⦂ T)
                  → 𝓡 T (ℰ⟦ ⊢M ⟧ (Inst-𝒞 I)) (msubst E M)
fundamental-lemma     {M = .(` x)}          I (⊢` {x} ix)     = {!!}
fundamental-lemma     {M = .(ƛ _ ⦂ _ ⇒ _)}   I (⊢ƛ x ⊢M)      = {!!}
fundamental-lemma     {M = .(_ · _)}        I (⊢M ⊢· ⊢N)     = {!!}
fundamental-lemma     {M = .(Y _)}          I (⊢Y ⊢M)         = {!!}
fundamental-lemma {E} {M = .(＃ n)}         I  (⊢＃ {n})        =
  let ＃⇓ : (＃ n) ⇓⁅ 0 ⁆ᵛ v-＃ n
      ＃⇓ = refl , refl
    in
  subst (λ q → q ⇓⁅ 0 ⁆ᵛ v-＃ n) (sym (msubst-＃ {E})) ＃⇓
fundamental-lemma {E} {M = .(𝓈 M)}          I (⊢𝓈 {M} ⊢M)      =
  subst (𝓡𝓝 (mapᵖ suc (ℰ⟦ ⊢M ⟧ (Inst-𝒞 I)))) (sym (msubst-𝓈 {E})) $
  𝓡𝓝𝓈 (ℰ⟦ ⊢M ⟧ (Inst-𝒞 I)) (msubst E M) $
  fundamental-lemma I ⊢M
fundamental-lemma {E} {M = .(𝓅 M)}          I (⊢𝓅 {M} ⊢M)     =
  subst (𝓡𝓝 (mapᵖ pred (ℰ⟦ ⊢M ⟧ (Inst-𝒞 I)))) (sym (msubst-𝓅 {E})) $
  𝓡𝓝𝓅 (ℰ⟦ ⊢M ⟧ (Inst-𝒞 I)) (msubst E M) $
  fundamental-lemma I ⊢M
fundamental-lemma     {M = .(?⁰ _ ↑ _ ↓ _)} I (⊢?⁰ ⊢L ⊢M ⊢N) = {!!}


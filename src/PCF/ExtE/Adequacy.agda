{-# OPTIONS --guarded #-}
module PCF.ExtE.Adequacy where

open import Prelude hiding (_⊆_)
open import Data.Empty
open import Data.Dec
open import Data.Nat hiding (_·_)
open import Data.Maybe
open import Data.List
open import Data.List.Correspondences.Unary.All
open import Data.String

open import Later
open import Interlude
open import Guarded.Partial
open import PCF.ExtE.TyTerm
open import PCF.ExtE.Subst
open import PCF.ExtE.TyDeriv
open import PCF.ExtE.Bigstep
open import PCF.ExtE.Smallstep
open import PCF.ExtE.SmallstepTy
open import PCF.ExtE.Correspondence
open import PCF.ExtE.Denot
open import PCF.ExtE.Soundness

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
𝓡 (S ⇒ T) ϕ M = (σ : 𝒯⟦ S ⟧) → (N : Term) → ∅ ⊢ N ⦂ S → 𝓡 S σ N → 𝓡 T (ϕ σ) (M · N)
𝓡 𝓝          = 𝓡𝓝

-- 2.25

ap-𝓡 : ∀ {S T M L f▹ r▹}
     → ∅ ⊢ L ⦂ S
     → ▸ (▹map (𝓡 (S ⇒ T)) f▹ ⊛ next M)
     → ▸ (▹map (𝓡 S) r▹ ⊛ next L)
     → ▸ (▹map (𝓡 T) (f▹ ⊛ r▹) ⊛ next (M · L))
ap-𝓡 {L} {r▹} ⊢L Rf Rr =
  λ α → Rf α (r▹ α) L ⊢L (Rr α)

-- 2.26

lift-𝓡𝓝 : ∀ {M N T}
          → (σ▹ : ▹ 𝒯⟦ T ⟧)
          → M —→⁅ s¹ ⁆ N
          → ▸ (▹map (𝓡 T) σ▹ ⊛ next N)
          → 𝓡 T (θ σ▹) M
lift-𝓡𝓝 {M} {N} {T = S ⇒ T} σ▹ S1 R▹ β P ⊢P RP =
  lift-𝓡𝓝 (σ▹ ⊛ next β) (ξ-· S1) $
  ap-𝓡 {T = T} ⊢P R▹ (next RP)
lift-𝓡𝓝 {M} {N} {T = 𝓝}    σ▹ S1 R▹            =
  𝓡𝓝-⇉later M N (M ∎ᵣ) S1 R▹

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
step-𝓡 {M} {N} {T = S ⇒ T} {τ = ϕ}        st Rf σ P cP RP =
  step-𝓡 {M = M · P} {N = N · P} {T} {τ = ϕ σ} (ξ-· st) (Rf σ P cP RP)

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
step-𝓡-rev {M} {N} {T = S ⇒ T} {τ = ϕ}        st Rf σ P cP RP =
  step-𝓡-rev {M = M · P} {N = N · P} {T} {τ = ϕ σ} (ξ-· st) (Rf σ P cP RP)

-- 2.28

-- instantiations

data Inst : Ctx → Env → 𝒰 where
  I-nil  : Inst ∅ []
  I-cons : ∀ {x T N Γ E}
         → (τ : 𝒯⟦ T ⟧)
         → ∅ ⊢ N ⦂ T
         → 𝓡 T τ N
         → Inst Γ E
         → Inst (Γ , x ⦂ T) ((x , N) ∷ E)

Inst-closed : ∀ {Γ E}
            → Inst Γ E
            → closed-env E
Inst-closed  I-nil            = []
Inst-closed (I-cons _ ⊢N _ I) = ∅⊢-closed ⊢N ∷ Inst-closed I

Inst-closed-msubst : ∀ {Γ E M A}
                   → Inst Γ E
                   → Γ ⊢ M ⦂ A
                   → ∅ ⊢ msubst E M ⦂ A
Inst-closed-msubst      I-nil                    ⊢M = ⊢M
Inst-closed-msubst {M} (I-cons {x} {N} τ ⊢N R I) ⊢M =
  Inst-closed-msubst {M = M [ x := N ]} I (subst-ty ⊢N ⊢M)

Inst-𝒞 : ∀ {Γ E}
       → Inst Γ E
       → 𝒞⟦ Γ ⟧
Inst-𝒞 (I-cons τ _ _ i) = Inst-𝒞 i ＆ τ

Inst-𝒞-nil : Inst-𝒞 I-nil ＝ 𝒞∅
Inst-𝒞-nil = fun-ext λ S → fun-ext λ y → fun-ext λ ()

Inst→Term : ∀ {Γ E x T}
          → Inst Γ E
          → Γ ∋ x ⦂ T
          → Σ[ N ꞉ Term ] (lup x E ＝ just N)
Inst→Term (I-cons {x = y} {N} _ _ _ _) (here {x} ei _) with (x ≟ y)
... | yes prf = N , refl
... | no ctra = absurd (ctra ei)
Inst→Term (I-cons {x = y} τ c R I)     (there {x} ne ix) with (x ≟ y)
... | yes prf = absurd (ne prf)
... | no ctra = Inst→Term I ix

Inst-R : ∀ {Γ E x T}
       → (I : Inst Γ E)
       → (ix : Γ ∋ x ⦂ T)
       → 𝓡 T (Inst-𝒞 I T x ix) (Inst→Term I ix .fst)
Inst-R {T} (I-cons {x = y} {T = S} {N} τ c R I) (here {x} ei et) with (x ≟ y)
... | yes prf = J (λ S′ e → (τ′ : 𝒯⟦ S′ ⟧)
                          → 𝓡 S′ τ′ N
                          → 𝓡 T (subst 𝒯⟦_⟧ (sym e) τ′) N)
                  (λ τ′ R′ → subst (λ q → 𝓡 T q N) (sym $ subst-refl {B = 𝒯⟦_⟧} τ′) R′)
                  et τ R
... | no ctra = absurd (ctra ei)
Inst-R     (I-cons {x = y}         τ c R I) (there {x} ne ix) with (x ≟ y)
... | yes prf = absurd (ne prf)
... | no ctra = Inst-R I ix

-- 𝓡𝓝 lemmas

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
fundamental-lemma     {M = .(` x)} {T}         I (⊢` {x} ix)     =
  let N , eN = Inst→Term I ix in
  subst (𝓡 T (Inst-𝒞 I T x ix))
        (sym (msubst-` (Inst-closed I) x ∙ ap (extract (` x)) eN))
        (Inst-R I ix)
fundamental-lemma {E} {M = .(ƛ x ⦂ T ⇒ M)}  I (⊢ƛ {x} {N = M} {A} {B} {T} e ⊢M) σ N ⊢N RA =
  subst (λ q → 𝓡 B (ℰ⟦ ⊢M ⟧ (Inst-𝒞 I ＆ σ)) (q · N)) (sym $ msubst-ƛ E x T M) $
  step-𝓡 {T = B} β-ƛ $
  subst (𝓡 B (ℰ⟦ ⊢M ⟧ (Inst-𝒞 I ＆ σ)))
                 (subst-msubst (∅⊢-closed ⊢N) (Inst-closed I) x M) $
  fundamental-lemma (I-cons σ ⊢N RA I) ⊢M
fundamental-lemma {E} {M = .(L · M)} {T}  I (_⊢·_ {L} {M} ⊢L ⊢M)     =
  subst (𝓡 T (ℰ⟦ ⊢L ⟧ (Inst-𝒞 I) (ℰ⟦ ⊢M ⟧ (Inst-𝒞 I))))
        (sym (msubst-· E L M)) $
  fundamental-lemma I ⊢L
        (ℰ⟦ ⊢M ⟧ (Inst-𝒞 I))
        (msubst E M)
        (Inst-closed-msubst I ⊢M) $
  fundamental-lemma I ⊢M
fundamental-lemma {E} {M = .(Y M)} {T}         I (⊢Y {M} ⊢M)         =
  fix λ ih▹ →
    subst (λ q → 𝓡 T (fix (θ ∘ ▹map (ℰ⟦ ⊢M ⟧ (Inst-𝒞 I)))) q) (sym $ msubst-Y E M) $
    subst (λ q → 𝓡 T q (Y (msubst E M))) (sym $ happly (Y-δ ⊢M) (Inst-𝒞 I)) $
    lift-𝓡𝓝 (next (ℰ⟦ ⊢M ⊢· ⊢Y ⊢M ⟧ (Inst-𝒞 I))) Ｙ $
    subst (λ q → ▹ 𝓡 T (ℰ⟦ ⊢M ⟧ (Inst-𝒞 I) (fix (θ ∘ ▹map (ℰ⟦ ⊢M ⟧ (Inst-𝒞 I))))) (msubst E M · q)) (msubst-Y E M) $
    ▹map (fundamental-lemma I ⊢M (fix (θ ∘ ▹map (ℰ⟦ ⊢M ⟧ (Inst-𝒞 I))))
                                         (msubst E (Y M))
                                         (Inst-closed-msubst I (⊢Y ⊢M))) ih▹
fundamental-lemma {E} {M = .(＃ n)}         I  (⊢＃ {n})        =
  subst (λ q → q ⇓⁅ 0 ⁆ᵛ v-＃ n) (sym (msubst-＃ {E})) (refl , refl)
fundamental-lemma {E} {M = .(𝓈 M)}          I (⊢𝓈 {M} ⊢M)      =
  subst (𝓡𝓝 (mapᵖ suc (ℰ⟦ ⊢M ⟧ (Inst-𝒞 I)))) (sym (msubst-𝓈 {E})) $
  𝓡𝓝𝓈 (ℰ⟦ ⊢M ⟧ (Inst-𝒞 I)) (msubst E M) $
  fundamental-lemma I ⊢M
fundamental-lemma {E} {M = .(𝓅 M)}          I (⊢𝓅 {M} ⊢M)     =
  subst (𝓡𝓝 (mapᵖ pred (ℰ⟦ ⊢M ⟧ (Inst-𝒞 I)))) (sym (msubst-𝓅 {E})) $
  𝓡𝓝𝓅 (ℰ⟦ ⊢M ⟧ (Inst-𝒞 I)) (msubst E M) $
  fundamental-lemma I ⊢M
fundamental-lemma     {M = .(?⁰ _ ↑ _ ↓ _)} I (⊢?⁰ ⊢L ⊢M ⊢N) =
  {!!}

-- 2.28

adequacy-body : ∀ {N V}
              → IsVal N V
              → (⊢N : ∅ ⊢ N ⦂ 𝓝)
              → ▹ (  (k : ℕ)
                   → (M : Term)
                   → 𝓡𝓝 (iter k δ (ℰ⟦ ⊢N ⟧ 𝒞∅)) M
                   → M ⇓⁅ k ⁆ᵛ V)
              → (k : ℕ)
              → (M : Term)
              → 𝓡𝓝 (iter k δ (ℰ⟦ ⊢N ⟧ 𝒞∅)) M
              → M ⇓⁅ k ⁆ᵛ V
adequacy-body     is-＃ ⊢＃ ih▹  zero   M RN = RN
adequacy-body {V} is-＃ ⊢＃ ih▹ (suc k) M RN =
  let (M′ , M″ , S1 , S2 , S▹) = 𝓡𝓝-later⇉ RN in
  small-rtc-big-v M M′ V S1 $
  small¹-big M′ M″ (λ v l → (l ＝ 0) × (v ＝ V)) S2
             (ih▹ ⊛ next k ⊛ next M″ ⊛ S▹)

adequacy : ∀ {M N V k}
         → IsVal N V
         → (⊢M : ∅ ⊢ M ⦂ 𝓝)
         → (⊢N : ∅ ⊢ N ⦂ 𝓝)
         → ℰ⟦ ⊢M ⟧ 𝒞∅ ＝ (iter k δ) (ℰ⟦ ⊢N ⟧ 𝒞∅)
         → M ⇓⁅ k ⁆ᵛ V
adequacy {M} {k} iV ⊢M ⊢N e =
  fix (adequacy-body iV ⊢N) k M $
  subst (λ q → 𝓡𝓝 q M) (ap (ℰ⟦ ⊢M ⟧) Inst-𝒞-nil ∙ e) $
  fundamental-lemma I-nil ⊢M

adequacy-rev : ∀ {M N V k}
             → IsVal N V
             → (⊢M : ∅ ⊢ M ⦂ 𝓝)
             → (⊢N : ∅ ⊢ N ⦂ 𝓝)
             → M ⇓⁅ k ⁆ᵛ V
             → ℰ⟦ ⊢M ⟧ 𝒞∅ ＝ (iter k δ) (ℰ⟦ ⊢N ⟧ 𝒞∅)
adequacy-rev iV ⊢M ⊢N M⇓ = soundness iV M⇓ ⊢M ⊢N

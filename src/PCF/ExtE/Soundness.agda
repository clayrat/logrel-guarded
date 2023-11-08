{-# OPTIONS --guarded #-}
module PCF.ExtE.Soundness where

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

-- Soundness

private variable
  Γ Δ : Ctx
  T : Ty

δ-ap : ∀ {L M A B k Γ γ}
        → (⊢L : Γ ⊢ L ⦂ A ⇒ B)
        → (⊢M : Γ ⊢ M ⦂ A)
        → (δ ⁽ k ⁾) (ℰ⟦ ⊢L ⟧ γ) (ℰ⟦ ⊢M ⟧ γ) ＝
          (δ ⁽ k ⁾) (ℰ⟦ ⊢L ⟧ γ (ℰ⟦ ⊢M ⟧ γ))
δ-ap {k = s⁰} ⊢L ⊢M = refl
δ-ap {k = s¹} ⊢L ⊢M = refl

δ-map : ∀ {M k Γ γ}
      → (⊢M : Γ ⊢ M ⦂ 𝓝)
      → (f : ℕ → ℕ)
      → mapᵖ f ((δ ⁽ k ⁾) (ℰ⟦ ⊢M ⟧ γ)) ＝
        (δ ⁽ k ⁾) (mapᵖ f (ℰ⟦ ⊢M ⟧ γ))
δ-map {k = s⁰} ⊢M f = refl
δ-map {k = s¹} ⊢M f = refl

δ-ifz : ∀ {L L′ M N Γ γ k}
       → (⊢L  : Γ ⊢ L  ⦂ 𝓝)
       → (⊢L′ : Γ ⊢ L′ ⦂ 𝓝)
       → (⊢M : Γ ⊢ M ⦂ T)
       → (⊢N : Γ ⊢ N ⦂ T)
       → (ℰ⟦ ⊢L ⟧ γ ＝ (δ ⁽ k ⁾) (ℰ⟦ ⊢L′ ⟧ γ))
       → ℰ⟦ ⊢?⁰ ⊢L ⊢M ⊢N ⟧ γ ＝ (δ ⁽ k ⁾) (ℰ⟦ ⊢?⁰ ⊢L′ ⊢M ⊢N ⟧ γ)
δ-ifz {γ} {k = s⁰} ⊢L ⊢L′ ⊢M ⊢N eq = ap (ifz^ (ℰ⟦ ⊢M ⟧ γ) (ℰ⟦ ⊢N ⟧ γ)) eq
δ-ifz     {k = s¹} ⊢L ⊢L′ ⊢M ⊢N eq = ifz-δ ⊢L ⊢L′ ⊢M ⊢N eq

-- 2.17 (simplified for Δ = ∅)

weaken-𝒞 : ∀ {Γ Δ}
         → Γ ⊆ Δ
         → 𝒞⟦ Δ ⟧ → 𝒞⟦ Γ ⟧
weaken-𝒞 sub 𝒞Δ T x ix = 𝒞Δ T x (sub T x ix)

weaken-lemma : ∀ {Γ Δ M T}
           → (sub : Γ ⊆ Δ)
           → (𝒞Δ : 𝒞⟦ Δ ⟧)
           → (⊢M : Γ ⊢ M ⦂ T)
           → ℰ⟦ weaken sub ⊢M ⟧ 𝒞Δ ＝ ℰ⟦ ⊢M ⟧ (weaken-𝒞 sub 𝒞Δ)
weaken-lemma {M = .(` _)} sub 𝒞Δ (⊢` x) = refl
weaken-lemma {M = .(ƛ _ ⦂ _ ⇒ _)} sub 𝒞Δ (⊢ƛ x ⊢M) =
  fun-ext λ ta →
      weaken-lemma (⊆-ext sub) (𝒞Δ ＆ ta) ⊢M
    ∙ ap ℰ⟦ ⊢M ⟧ (fun-ext λ S →          -- TODO extract into `weaken-𝒞 (⊆-ext sub) (𝒞Δ ＆ ta) ＝ (weaken-𝒞 sub 𝒞Δ ＆ ta)`
                  fun-ext λ x →
                  fun-ext λ where
                              (here x x₁) → refl
                              (there x ix) → refl)
weaken-lemma {M = .(_ · _)} sub 𝒞Δ (⊢M ⊢· ⊢N) = ap² (λ q w → q w) (weaken-lemma sub 𝒞Δ ⊢M) (weaken-lemma sub 𝒞Δ ⊢N)
weaken-lemma {M = .(Y _)} sub 𝒞Δ (⊢Y ⊢M) = ap (λ q → fix (λ x → θ (▹map q x))) (weaken-lemma sub 𝒞Δ ⊢M)
weaken-lemma {M = .(＃ _)} sub 𝒞Δ ⊢＃ = refl
weaken-lemma {M = .(𝓈 _)} sub 𝒞Δ (⊢𝓈 ⊢M) = ap (mapᵖ suc) (weaken-lemma sub 𝒞Δ ⊢M)
weaken-lemma {M = .(𝓅 _)} sub 𝒞Δ (⊢𝓅 ⊢M) = ap (mapᵖ pred) (weaken-lemma sub 𝒞Δ ⊢M)
weaken-lemma {M = .(?⁰ _ ↑ _ ↓ _)} sub 𝒞Δ (⊢?⁰ ⊢L ⊢M ⊢N) = ap³-simple ifz^ (weaken-lemma sub 𝒞Δ ⊢M) (weaken-lemma sub 𝒞Δ ⊢N) (weaken-lemma sub 𝒞Δ ⊢L)

subst-lemma : ∀ {M} {x} {S} {T} {N} {Γ}
            → (𝒞Γ : 𝒞⟦ Γ ⟧)
            → (⊢N : ∅ ⊢ N ⦂ S)
            → (⊢M : Γ , x ⦂ S ⊢ M ⦂ T)
            → ℰ⟦ subst-ty ⊢N ⊢M ⟧ 𝒞Γ ＝ ℰ⟦ ⊢M ⟧ (𝒞Γ ＆ ℰ⟦ ⊢N ⟧ 𝒞∅)
subst-lemma {.(` _)} {x = y} {S} {N} 𝒞Γ ⊢N (⊢` (here {x} ei eT)) with x ≟ y
... | yes prf = J (λ T₁ e₁ → (⊢N₁ : ∅ ⊢ N ⦂ S)
                            → ℰ⟦ weaken ⊆-∅ (subst (∅ ⊢ N ⦂_) e₁ ⊢N₁) ⟧ 𝒞Γ ＝ subst (𝒯⟦_⟧) e₁ (ℰ⟦ ⊢N₁ ⟧ 𝒞∅))
                  (λ ⊢N₁ →   ap (λ q → ℰ⟦ weaken ⊆-∅ q ⟧ 𝒞Γ) (subst-refl {B = (∅ ⊢ N ⦂_)} ⊢N₁)
                           ∙ weaken-lemma ⊆-∅ 𝒞Γ ⊢N₁
                           ∙ ap ℰ⟦ ⊢N₁ ⟧ (fun-ext λ S →  -- TODO extract into `weaken-𝒞 ⊆-∅ 𝒞Γ ＝ 𝒞∅`
                                            fun-ext λ x →
                                            fun-ext λ ())

                           ∙ sym (subst-refl {B = 𝒯⟦_⟧} (ℰ⟦ ⊢N₁ ⟧ 𝒞∅)))
                  (sym eT)
                  ⊢N
... | no ctra = absurd (ctra ei)
subst-lemma {.(` _)} {x = y} 𝒞Γ ⊢N (⊢` (there {x} ne ix)) with x ≟ y
... | yes prf = absurd (ne prf)
... | no ctra = refl
subst-lemma {.(ƛ _ ⦂ _ ⇒ _)} {x = y} {S} {Γ} 𝒞Γ ⊢N (⊢ƛ {x} {N} {A} {B} e ⊢M) with x ≟ y
... | yes prf = fun-ext λ ta → J (λ y₁ ey → (⊢M₁ : Γ , y₁ ⦂ S , x ⦂ A ⊢ N ⦂ B)
                                          → ℰ⟦ weaken ⊆-shadow (subst (λ q → (Γ , q ⦂ S , x ⦂ A) ⊢ N ⦂ B) (sym ey) ⊢M₁) ⟧ (𝒞Γ ＆ ta) ＝ ℰ⟦ ⊢M₁ ⟧ ((𝒞Γ ＆ ℰ⟦ ⊢N ⟧ 𝒞∅) ＆ ta)
                                            )
                                 (λ ⊢M₁ → ap (λ q → ℰ⟦ weaken ⊆-shadow q ⟧ (𝒞Γ ＆ ta)) (subst-refl {B = λ q → (Γ , q ⦂ S , x ⦂ A) ⊢ N ⦂ B} ⊢M₁)
                                        ∙ weaken-lemma ⊆-shadow (𝒞Γ ＆ ta) ⊢M₁
                                        -- TODO extract into `weaken-𝒞 ⊆-shadow (𝒞Γ ＆ ta) ＝ ((𝒞Γ ＆ ℰ⟦ ⊢N ⟧ 𝒞∅) ＆ ta)`
                                        ∙ ap (ℰ⟦ ⊢M₁ ⟧) (fun-ext λ S →
                                                         fun-ext λ x →
                                                         fun-ext λ where
                                                            (here x x₁) → refl
                                                            (there x (here x₁ x₂)) → absurd (x x₁)
                                                            (there x (there x₁ p)) → refl)
                                 )
                                 prf ⊢M
... | no ctra = fun-ext λ ta → subst-lemma (𝒞Γ ＆ ta) ⊢N (weaken (⊆-exch ctra) ⊢M)
                               ∙ weaken-lemma (⊆-exch ctra) ((𝒞Γ ＆ ta) ＆ ℰ⟦ ⊢N ⟧ 𝒞∅) ⊢M
                               ∙ ap ℰ⟦ ⊢M ⟧ (fun-ext λ S →  -- TODO extract into smth?
                                            fun-ext λ x →
                                            fun-ext λ where
                                                        (here x x₁) → refl
                                                        (there x (here x₁ x₂)) → refl
                                                        (there x (there x₁ p)) → refl)
subst-lemma {.(_ · _)} 𝒞Γ ⊢N (MM ⊢· MM₁) = ap² (λ q w → q w) (subst-lemma 𝒞Γ ⊢N MM) (subst-lemma 𝒞Γ ⊢N MM₁)
subst-lemma {.(Y _)} 𝒞Γ ⊢N (⊢Y MM) = ap (λ q → fix (λ x → θ (▹map q x))) (subst-lemma 𝒞Γ ⊢N MM)
subst-lemma {.(＃ _)} 𝒞Γ ⊢N ⊢＃ = refl
subst-lemma {.(𝓈 _)} 𝒞Γ ⊢N (⊢𝓈 MM) = ap (mapᵖ suc) (subst-lemma 𝒞Γ ⊢N MM)
subst-lemma {.(𝓅 _)} 𝒞Γ ⊢N (⊢𝓅 MM) = ap (mapᵖ pred) (subst-lemma 𝒞Γ ⊢N MM)
subst-lemma {.(?⁰ _ ↑ _ ↓ _)} 𝒞Γ ⊢N (⊢?⁰ MM MM₁ MM₂) = ap³-simple ifz^ (subst-lemma 𝒞Γ ⊢N MM₁) (subst-lemma 𝒞Γ ⊢N MM₂) (subst-lemma 𝒞Γ ⊢N MM)

-- multisubstitution

Env : 𝒰
Env = List (Id × Term)

msubst : Env → Term → Term
msubst []             t = t
msubst ((x , s) ∷ ss) t = msubst ss (t [ x := s ])

-- TODO force Δ = ∅
data Inst (Δ : Ctx) : Ctx → Env → 𝒰 where
  I-nil  : Inst Δ ∅ []
  I-cons : ∀ {x T N Γ E}
         → Δ ⊢ N ⦂ T
         → Inst Δ Γ E
         → Inst Δ (Γ , x ⦂ T) ((x , N) ∷ E)

-- TODO redefine as Inst-𝒞 (I-cons ⊢N I) 𝒞∅ = (Inst-𝒞 I 𝒞∅ ＆ ℰ⟦ ⊢N ⟧ 𝒞∅) !!
Inst-𝒞 : ∀ {Δ E}
       → Inst Δ Γ E
       → 𝒞⟦ Δ ⟧ → 𝒞⟦ Γ ⟧
Inst-𝒞 {E = .((x , N) ∷ E)} (I-cons {x} {T} {N} {E} ⊢N I) 𝒞Δ S y (here ex eT)  =
  subst (𝒯⟦_⟧) (sym eT) (ℰ⟦ ⊢N ⟧ 𝒞Δ)
Inst-𝒞 {E = .((x , N) ∷ E)} (I-cons {x} {T} {N} {E} ⊢N I) 𝒞Δ S y (there ne ix) =
  Inst-𝒞 I 𝒞Δ S y ix

msubst-lemma : ∀ {M E}
             → (i : Inst ∅ Γ E)
             → (⊢M : Γ ⊢ M ⦂ T)
             → (⊢MN : ∅ ⊢ msubst E M ⦂ T)
             → ℰ⟦ ⊢MN ⟧ 𝒞∅ ＝ ℰ⟦ ⊢M ⟧ (Inst-𝒞 i 𝒞∅)
msubst-lemma {M} {E = .[]} I-nil tM tMN = ap² (λ q w → ℰ⟦ q ⟧ w) (is-prop-β ⊢-is-prop tMN tM)
                                                                 (fun-ext λ S → fun-ext λ x → fun-ext λ ix →  -- TODO extract into smth
                                                                   absurd (∅-empty ix))
msubst-lemma {E = .((_ , _) ∷ _)} (I-cons {x} {T} {N} {E} ⊢N I) ⊢M ⊢MN =
    msubst-lemma {E = E} I (subst-ty ⊢N ⊢M) ⊢MN
  ∙ subst-lemma (Inst-𝒞 I 𝒞∅) ⊢N ⊢M
  ∙ ap ℰ⟦ ⊢M ⟧ (fun-ext λ S →    -- TODO extract into `(Inst-𝒞 I 𝒞∅ ＆ ℰ⟦ ⊢N ⟧ 𝒞∅) ＝ Inst-𝒞 (I-cons ⊢N I) 𝒞∅` (redundant after refactor)
                fun-ext λ x →
                fun-ext λ where
                            (here x x₁) → refl
                            (there x p) → refl)

-- 2.18

step-sound : ∀ {k M N}
           → M —→⁅ k ⁆ N
           → (⊢M : ∅ ⊢ M ⦂ T)
           → (⊢N : ∅ ⊢ N ⦂ T)
           → ℰ⟦ ⊢M ⟧ 𝒞∅ ＝ (δ ⁽ k ⁾) (ℰ⟦ ⊢N ⟧ 𝒞∅)
step-sound {T}       {.s⁰} {.((ƛ x ⦂ A ⇒ M) · N)}   {.(M [ x := N ])}  (β-ƛ {x} {M} {N} {A})         (⊢ƛ e ⊢M ⊢· ⊢N)       ⊢MN                 =
  ap (ℰ⟦ ⊢M ⟧)           -- TODO will be redundant after refactor
     (fun-ext λ S →
      fun-ext λ y →
      fun-ext λ where
         (here ei et) → refl)
  ∙ sym (msubst-lemma (I-cons ⊢N I-nil) ⊢M ⊢MN)
step-sound {T}       {.s¹} {.(Y M)}                {.(M · Y M)}        (Ｙ {M})                      (⊢Y ⊢M)               (⊢M₁ ⊢· ⊢Y ⊢M₂)    =
  happly (Y-δ ⊢M) 𝒞∅
  ∙ ap (λ q → δ (q 𝒞∅))
       (J (λ S eS → (⊢M¹ : ∅ ⊢ M ⦂ S ⇒ T)
                  → (⊢M² : ∅ ⊢ M ⦂ S ⇒ S)
                  → ℰ⟦ ⊢M ⊢· ⊢Y ⊢M ⟧ ＝ ℰ⟦ ⊢M¹ ⊢· ⊢Y ⊢M² ⟧)
          (λ ⊢M¹ ⊢M² → ap² (λ x y → ℰ⟦ x ⊢· ⊢Y y ⟧)
                            (is-prop-β ⊢-is-prop ⊢M ⊢M¹)
                            (is-prop-β ⊢-is-prop ⊢M ⊢M²))
          (fst $ ⇒-inj $ ⊢-unique ⊢M ⊢M₁)
          ⊢M₁ ⊢M₂)
step-sound {T}       {.s⁰} {.(𝓈 (＃ n))}            {.(＃ suc n)}       (β-𝓈 {n})                    (⊢𝓈 (⊢＃ {n}))         (⊢＃ {n = suc n})    = refl
step-sound {T}       {.s⁰} {.(𝓅 (＃ 0))}            {.(＃ 0)}           β-𝓅⁰                        (⊢𝓅 (⊢＃ {n = 0}))     (⊢＃ {n = 0})        = refl
step-sound {T}       {.s⁰} {.(𝓅 (＃ suc n))}        {.(＃ n)}           (β-𝓅ˢ {n})                  (⊢𝓅 (⊢＃ {n = suc n})) (⊢＃ {n})            = refl
step-sound {T}       {.s⁰} {.(?⁰ ＃ 0 ↑ M ↓ N)}     {N = M}            (β-?⁰ {M} {N})               (⊢?⁰ ⊢＃ ⊢M ⊢N)        ⊢M₁                =
  ap (λ q → ℰ⟦ q ⟧ 𝒞∅) (is-prop-β ⊢-is-prop ⊢M ⊢M₁)
step-sound {T}       {.s⁰} {.(?⁰ ＃ suc n ↑ M ↓ N)} {N}                (β-?ˢ {M} {N} {n})           (⊢?⁰ ⊢＃ ⊢M ⊢N)        ⊢N₁                =
  ap (λ q → ℰ⟦ q ⟧ 𝒞∅) (is-prop-β ⊢-is-prop ⊢N ⊢N₁)
step-sound {T}       {.k}  {.(M · N)}               {.(M′ · N)}        (ξ-· {M} {M′} {k} {N} s)     (⊢M ⊢· ⊢N)             (⊢M′ ⊢· ⊢N₁)      =
  J (λ A¹ eA → (⊢M¹ : ∅ ⊢ M′ ⦂ A¹ ⇒ T)
             → (⊢N¹ : ∅ ⊢ N ⦂ A¹)
             → ℰ⟦ ⊢M ⟧ 𝒞∅ (ℰ⟦ ⊢N ⟧ 𝒞∅) ＝ (δ ⁽ k ⁾) (ℰ⟦ ⊢M¹ ⟧ 𝒞∅ (ℰ⟦ ⊢N¹ ⟧ 𝒞∅)))
    (λ ⊢M¹ ⊢N¹ → ap (λ q → q (ℰ⟦ ⊢N ⟧ 𝒞∅)) (step-sound s ⊢M ⊢M¹)
                ∙ ap (λ q → (δ ⁽ k ⁾) (ℰ⟦ ⊢M¹ ⟧ 𝒞∅) (ℰ⟦ q ⟧ 𝒞∅)) (is-prop-β ⊢-is-prop ⊢N ⊢N¹)
                ∙ δ-ap {k = k} ⊢M¹ ⊢N¹)
    (⊢-unique ⊢N ⊢N₁)
    ⊢M′ ⊢N₁
step-sound {T = .𝓝} {.k}  {.(𝓈 M)}                 {.(𝓈 M′)}          (ξ-𝓈 {M} {M′} {k} s)         (⊢𝓈 ⊢M)                (⊢𝓈 ⊢M′)           =
    ap (mapᵖ suc) (step-sound s ⊢M ⊢M′)
  ∙ δ-map {k = k} ⊢M′ suc
step-sound {T = .𝓝} {.k}  {.(𝓅 M)}                 {.(𝓅 M′)}          (ξ-𝓅 {M} {M′} {k} s)        (⊢𝓅 ⊢M)                (⊢𝓅 ⊢M′)           =
    ap (mapᵖ pred) (step-sound s ⊢M ⊢M′)
  ∙ δ-map {k = k} ⊢M′ pred
step-sound {T}       {.k}  {.(?⁰ L ↑ M ↓ N)}        {.(?⁰ L′ ↑ M ↓ N)} (ξ-? {L} {L′} {M} {N} {k} s) (⊢?⁰ ⊢L ⊢M ⊢N)       (⊢?⁰ ⊢L′ ⊢M₁ ⊢N₁) =
  ap² (λ q w → ifz^ (ℰ⟦ q ⟧ 𝒞∅) (ℰ⟦ w ⟧ 𝒞∅) (ℰ⟦ ⊢L ⟧ 𝒞∅))
      (is-prop-β ⊢-is-prop ⊢M ⊢M₁)
      (is-prop-β ⊢-is-prop ⊢N ⊢N₁)
  ∙ δ-ifz {k = k} ⊢L ⊢L′ ⊢M₁ ⊢N₁ (step-sound s ⊢L ⊢L′)

-- 2.19

rtc0-sound : ∀ {M N}
           → M —↠⁰ N
           → (⊢M : ∅ ⊢ M ⦂ T)
           → (⊢N : ∅ ⊢ N ⦂ T)
           → ℰ⟦ ⊢M ⟧ 𝒞∅ ＝ ℰ⟦ ⊢N ⟧ 𝒞∅
rtc0-sound {M} {.M} (.M ∎ᵣ)         ⊢M ⊢N =
  ap (λ q → ℰ⟦ q ⟧ 𝒞∅) (is-prop-β ⊢-is-prop ⊢M ⊢N)
rtc0-sound {M} {N}  (.M —→⟨ S ⟩ MS) ⊢M ⊢N =
  let ⊢M₁ = preserve S ⊢M in
  step-sound S ⊢M ⊢M₁ ∙ rtc0-sound MS ⊢M₁ ⊢N

-- 2.20

rtc-sound : ∀ {M N k}
          → M =⇒⁅ k ⁆ᵗ N
          → (⊢M : ∅ ⊢ M ⦂ T)
          → (⊢N : ∅ ⊢ N ⦂ T)
          → ℰ⟦ ⊢M ⟧ 𝒞∅ ＝ (iter k δ) (ℰ⟦ ⊢N ⟧ 𝒞∅)
rtc-sound {T} {M} {k = zero}  (P , sP , eP)          ⊢M ⊢N =
  J (λ Q eQ → (sQ : M —↠⁰ Q)
            → ℰ⟦ ⊢M ⟧ 𝒞∅ ＝ ℰ⟦ ⊢N ⟧ 𝒞∅)
    (λ sQ → rtc0-sound sQ ⊢M ⊢N)
    (sym eP) sP
rtc-sound         {k = suc k} (P , R , sP , sR , S▹) ⊢M ⊢N =
  let ⊢P = rtc-preserve sP ⊢M
      ⊢R = preserve sR ⊢P
    in
    rtc0-sound sP ⊢M ⊢P
  ∙ step-sound sR ⊢P ⊢R
  ∙ ap θ (▹-ext $ ▹map (λ q → rtc-sound q ⊢R ⊢N) S▹)

-- 2.21

soundness : ∀ {M N V k}
          → IsVal N V
          → M ⇓⁅ k ⁆ᵛ V
          → (⊢M : ∅ ⊢ M ⦂ T)
          → (⊢N : ∅ ⊢ N ⦂ T)
          → ℰ⟦ ⊢M ⟧ 𝒞∅ ＝ (iter k δ) (ℰ⟦ ⊢N ⟧ 𝒞∅)
soundness {M} {N} {V} iV M⇓ ⊢M ⊢N =
  rtc-sound (big→small-rtc-v M N V iV M⇓) ⊢M ⊢N


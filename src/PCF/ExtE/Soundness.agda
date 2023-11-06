{-# OPTIONS --guarded #-}
module PCF.ExtE.Soundness where

open import Prelude
open import Data.Empty
open import Data.Nat hiding (_·_)
open import Data.List

open import Later
open import Interlude
open import Guarded.Partial
open import PCF.ExtE.TyTerm
open import PCF.ExtE.TyDeriv
open import PCF.ExtE.Smallstep
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

-- multisubstitution

Env : 𝒰
Env = List (Id × Term)

msubst : Env → Term → Term
msubst []             t = t
msubst ((x , s) ∷ ss) t = msubst ss (t [ x := s ])

-- 2.17

msubst-lemma : ∀ {M Δ E}
             → (⊢M : Γ ⊢ M ⦂ T)
             → (sub : ∀ x S → Γ ∋ x ⦂ S → Σ[ N ꞉ Term ] (Δ ⊢ N ⦂ S))
             → (⊢MN : Δ ⊢ msubst E M ⦂ T)
             → (𝒞Δ : 𝒞⟦ Δ ⟧)
             → ℰ⟦ ⊢MN ⟧ 𝒞Δ ＝ ℰ⟦ ⊢M ⟧ (λ S y xs → ℰ⟦ sub y S xs .snd ⟧ 𝒞Δ)
msubst-lemma = {!!}

-- 2.18

step-sound : ∀ {k M N}
           → M —→⁅ k ⁆ N
           → (⊢M : ∅ ⊢ M ⦂ T)
           → (⊢N : ∅ ⊢ N ⦂ T)
           → ℰ⟦ ⊢M ⟧ 𝒞∅ ＝ (δ ⁽ k ⁾) (ℰ⟦ ⊢N ⟧ 𝒞∅)
step-sound {T}       {.s⁰} {.((ƛ x ⦂ A ⇒ M) · N)}   {.(M [ x := N ])}  (β-ƛ {x} {M} {N} {A})         (⊢ƛ e ⊢M ⊢· ⊢N)       ⊢MN                 =
  ap (ℰ⟦ ⊢M ⟧)
     (fun-ext λ S →
      fun-ext λ y →
      fun-ext λ where
                  (here ei et) →
                     J (λ T e → subst 𝒯⟦_⟧ e (ℰ⟦ ⊢N ⟧ 𝒞∅) ＝ ℰ⟦ subst (_⊢_⦂_ ∅ N) e ⊢N ⟧ 𝒞∅)
                       (subst-refl {B = 𝒯⟦_⟧} (ℰ⟦ ⊢N ⟧ 𝒞∅)
                        ∙ ap (λ q → ℰ⟦ q ⟧ 𝒞∅) (sym $ subst-refl {B = _⊢_⦂_ ∅ N} ⊢N))
                       (sym et)
                       )
  ∙ sym (msubst-lemma {E = (x , N) ∷ []} ⊢M
           (λ y S → λ where
                       (here ei et) → N , subst (λ q → ∅ ⊢ N ⦂ q) (sym et) ⊢N)
           ⊢MN 𝒞∅)
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

{-# OPTIONS --guarded #-}
module PCF.Ext.All.Soundness where

open import Prelude hiding (_⊆_)
open import Data.Empty
open import Data.Dec
open import Data.Nat hiding (_·_)
open import Data.List
open import Data.String

open import Later
open import Interlude
open import Guarded.Partial

open import PCF.Ty
open import PCF.Ext.TyTerm
open import PCF.Ext.Subst
open import PCF.Ext.TyDeriv
open import PCF.Ext.All.Bigstep
open import PCF.Ext.All.Smallstep
open import PCF.Ext.All.Correspondence
open import PCF.Ext.All.Eval
open import PCF.Ext.All.Denot

-- Soundness

private variable
  Γ Δ : Ctx
  T : Ty

𝒮 : (T : Ty) → (t : Term) → ∅ ⊢ t  ⦂ T → Part (TVal T)
𝒮 (S ⇒ T) t ⊢t = Eval (S ⇒ T) t ⊢t
𝒮  𝓝     t ⊢t = mapᵖ ℕVal (ℰ⟦ ⊢t ⟧ 𝒞∅)

𝒮-Φ-body : ▹ ((T : Ty) → (M : Term) → (⊢M : ∅ ⊢ M ⦂ T)
               → Φ (next 𝒮) T M ⊢M ＝ 𝒮 T M ⊢M)
         → (T : Ty) → (M : Term) → (⊢M : ∅ ⊢ M ⦂ T)
         → Φ (next 𝒮) T M ⊢M ＝ 𝒮 T M ⊢M
𝒮-Φ-body ih▹ .(_ ⇒ _) .(ƛ _ ⦂ _ ⇒ _) (⊢ƛ x tM) = refl
𝒮-Φ-body ih▹ T .(_ · _) (tM ⊢· tM₁) =
  {!!}
𝒮-Φ-body ih▹ T .(Y M) (⊢Y {M} tM) =
  let qq = ih▹ ⊛ next T ⊛ next (M · Y M) ⊛ next (tM ⊢· ⊢Y tM) in
  ap later (▹-ext λ α → sym (qq α)) ∙ go
  where
  go : δᵖ (Φ (next 𝒮) T (M · Y M) (tM ⊢· ⊢Y tM)) ＝ 𝒮 T (Y M) (⊢Y tM)
  go with (Φ (next 𝒮) (T ⇒ T) M tM)
  ... | now (.(ƛ _ ⦂ _ ⇒ _) , .(v-ƛ _ _ _) , (is-ƛ {x} {A} {t}) , ⊢ƛ e tm) =
          let ww = ih▹ ⊛ next T ⊛ next (t [ x := Y M ]) ⊛ next (subst-ty (⊢Y tM) tm) in
          {!!}
  ... | later p▹ = {!!}
  zz : Φ (next 𝒮) (T ⇒ T) M tM ＝ 𝒮 (T ⇒ T) M tM
  zz = 𝒮-Φ-body ih▹ (T ⇒ T) M tM

𝒮-Φ-body ih▹ .𝓝 .(＃ _) ⊢＃ = refl
𝒮-Φ-body ih▹ .𝓝 .(𝓈 M) (⊢𝓈 {M} tM) =
  ap (δᵖ ∘ mapᵖ Φ-𝓈) (𝒮-Φ-body ih▹ 𝓝 M tM)
  ∙ ap δᵖ (mapᵖ-comp (ℰ⟦ tM ⟧ 𝒞∅)
           ∙ ap (λ q → mapᵖ q (ℰ⟦ tM ⟧ 𝒞∅))
              (fun-ext λ x → refl)
           ∙ sym (mapᵖ-comp (ℰ⟦ tM ⟧ 𝒞∅)))
𝒮-Φ-body ih▹ .𝓝 .(𝓅 _) (⊢𝓅 tM) = {!!}
𝒮-Φ-body ih▹ T .(?⁰ _ ↑ _ ↓ _) (⊢?⁰ tM tM₁ tM₂) = {!!}

{-
𝒮-Φ : ∀ {M}
    → (⊢M : ∅ ⊢ M ⦂ T)
    → Φ (next 𝒮) T M ⊢M ＝ 𝒮 T M ⊢M
𝒮-Φ (⊢ƛ x tM) = refl
𝒮-Φ (tM ⊢· tM₁) =
  let qq = 𝒮-Φ tM in
  {!!}
𝒮-Φ (⊢Y tM) =
  let qq = 𝒮-Φ (tM ⊢· ⊢Y tM) in
  ap δᵖ (sym qq) ∙ {!!}
  {!!}
𝒮-Φ ⊢＃ = refl
𝒮-Φ (⊢𝓈 tM) =
  ap (δᵖ ∘ mapᵖ Φ-𝓈) (𝒮-Φ tM)
  ∙ ap δᵖ (mapᵖ-comp (ℰ⟦ tM ⟧ 𝒞∅)
           ∙ ap (λ q → mapᵖ q (ℰ⟦ tM ⟧ 𝒞∅))
              (fun-ext λ x → refl)
           ∙ sym (mapᵖ-comp (ℰ⟦ tM ⟧ 𝒞∅)))
𝒮-Φ (⊢𝓅 tM) =
   ap (δᵖ ∘ mapᵖ Φ-𝓅) (𝒮-Φ tM)
  ∙ ap δᵖ (mapᵖ-comp (ℰ⟦ tM ⟧ 𝒞∅)
           ∙ ap (λ q → mapᵖ q (ℰ⟦ tM ⟧ 𝒞∅))
              (fun-ext λ x → refl)
           ∙ sym (mapᵖ-comp (ℰ⟦ tM ⟧ 𝒞∅)))
𝒮-Φ (⊢?⁰ tM tM₁ tM₂) =
  let qq = 𝒮-Φ tM in
  {!!}
-}

--S-Eval : 𝒮 ＝ Eval
--S-Eval = fix-unique {f▹ = Φ} (fun-ext λ T → fun-ext λ t → fun-ext λ tT → sym $ 𝒮-Φ tT)

{-
δ-comm : ∀ {k T}
        → (τ : 𝒯⟦ T ⟧)
        → (δ ⁽ k ⁾) (δ τ) ＝ δ ((δ ⁽ k ⁾) τ)
δ-comm {k = s⁰} τ = refl
δ-comm {k = s¹} τ = refl

δ-ap : ∀ {k A B}
        → (φ : 𝒯⟦ A ⇒ B ⟧)
        → (α : 𝒯⟦ A ⟧)
        → (δ ⁽ k ⁾) φ α ＝ (δ ⁽ k ⁾) (φ α)
δ-ap {k = s⁰} φ α = refl
δ-ap {k = s¹} φ α = refl

δ-map : ∀ {k}
      → (ν : 𝒯⟦ 𝓝 ⟧)
      → (f : ℕ → ℕ)
      → mapᵖ f ((δ ⁽ k ⁾) ν) ＝ (δ ⁽ k ⁾) (mapᵖ f ν)
δ-map {k = s⁰} ν f = refl
δ-map {k = s¹} ν f = refl

δ-ifz : ∀ {L L′ M N Γ γ k}
       → (⊢L  : Γ ⊢ L  ⦂ 𝓝)
       → (⊢L′ : Γ ⊢ L′ ⦂ 𝓝)
       → (⊢M : Γ ⊢ M ⦂ T)
       → (⊢N : Γ ⊢ N ⦂ T)
       → (ℰ⟦ ⊢L ⟧ γ ＝ (δ ⁽ k ⁾) (ℰ⟦ ⊢L′ ⟧ γ))
       → ℰ⟦ ⊢?⁰ ⊢L ⊢M ⊢N ⟧ γ ＝ (δ ⁽ k ⁾) (ℰ⟦ ⊢?⁰ ⊢L′ ⊢M ⊢N ⟧ γ)
δ-ifz {γ} {k = s⁰} ⊢L ⊢L′ ⊢M ⊢N eq = ap (δ ∘ ifz^ (ℰ⟦ ⊢M ⟧ γ) (ℰ⟦ ⊢N ⟧ γ)) eq
δ-ifz     {k = s¹} ⊢L ⊢L′ ⊢M ⊢N eq = ifz-δ ⊢L ⊢L′ ⊢M ⊢N eq

-- 2.17 (simplified for Δ = ∅ and a single substitution)

weaken-𝒞 : ∀ {Γ Δ}
         → Γ ⊆ Δ
         → 𝒞⟦ Δ ⟧ → 𝒞⟦ Γ ⟧
weaken-𝒞 sub 𝒞Δ T x ix = 𝒞Δ T x (sub T x ix)

weaken-𝒞-∅ : ∀ {Γ}
            → (𝒞Γ : 𝒞⟦ Γ ⟧)
            → weaken-𝒞 ⊆-∅ 𝒞Γ ＝ 𝒞∅
weaken-𝒞-∅ 𝒞Γ = fun-ext λ S → fun-ext λ x → fun-ext λ ()

weaken-𝒞-ext : ∀ {Γ Δ A x}
             → (sub : Γ ⊆ Δ)
             → (𝒞Δ : 𝒞⟦ Δ ⟧)
             → (ta : 𝒯⟦ A ⟧)
             → weaken-𝒞 (⊆-ext {x = x} sub) (𝒞Δ ＆ ta) ＝ (weaken-𝒞 sub 𝒞Δ ＆ ta)
weaken-𝒞-ext sub 𝒞Δ ta =
  fun-ext λ T → fun-ext λ x → fun-ext λ where
    (here ei et) → refl
    (there ne ix) → refl

weaken-𝒞-shadow : ∀ {Γ A B x}
                → (𝒞Γ : 𝒞⟦ Γ ⟧)
                → (ta : 𝒯⟦ A ⟧)
                → (tb : 𝒯⟦ B ⟧)
                → weaken-𝒞 (⊆-shadow {x = x}) (𝒞Γ ＆ ta) ＝ ((𝒞Γ ＆ tb) ＆ ta)
weaken-𝒞-shadow 𝒞Γ ta tb =
  fun-ext λ T → fun-ext λ x → fun-ext λ where
    (here ei et) → refl
    (there ne (here ei et)) → absurd (ne ei)
    (there ne₁ (there ne₂ p)) → refl

weaken-𝒞-exch : ∀ {Γ A B x y}
                → (ctra : x ≠ y)
                → (𝒞Γ : 𝒞⟦ Γ ⟧)
                → (ta : 𝒯⟦ A ⟧)
                → (tb : 𝒯⟦ B ⟧)
                → weaken-𝒞 (⊆-exch ctra) ((𝒞Γ ＆ ta) ＆ tb) ＝ ((𝒞Γ ＆ tb) ＆ ta)
weaken-𝒞-exch ctra 𝒞Γ ta tb =
  fun-ext λ T → fun-ext λ x → fun-ext λ where
    (here ei et) → refl
    (there ne (here ei et)) → refl
    (there ne₁ (there ne₂ p)) → refl

weaken-lemma : ∀ {Γ Δ M T}
           → (sub : Γ ⊆ Δ)
           → (𝒞Δ : 𝒞⟦ Δ ⟧)
           → (⊢M : Γ ⊢ M ⦂ T)
           → ℰ⟦ weaken sub ⊢M ⟧ 𝒞Δ ＝ ℰ⟦ ⊢M ⟧ (weaken-𝒞 sub 𝒞Δ)
weaken-lemma sub 𝒞Δ (⊢` x)           = refl
weaken-lemma sub 𝒞Δ (⊢ƛ x ⊢M)       =
  fun-ext λ ta →
      weaken-lemma (⊆-ext sub) (𝒞Δ ＆ ta) ⊢M
    ∙ ap ℰ⟦ ⊢M ⟧ (weaken-𝒞-ext sub 𝒞Δ ta)
weaken-lemma sub 𝒞Δ (⊢M ⊢· ⊢N)     =
  ap δ $
  ap² _$_ (weaken-lemma sub 𝒞Δ ⊢M)
          (weaken-lemma sub 𝒞Δ ⊢N)
weaken-lemma sub 𝒞Δ (⊢Y ⊢M)         =
  ap (λ q → fix (θ ∘ ▹map q)) (weaken-lemma sub 𝒞Δ ⊢M)
weaken-lemma sub 𝒞Δ ⊢＃              = refl
weaken-lemma sub 𝒞Δ (⊢𝓈 ⊢M)         =
  ap (stall ∘ mapᵖ suc) (weaken-lemma sub 𝒞Δ ⊢M)
weaken-lemma sub 𝒞Δ (⊢𝓅 ⊢M)         =
  ap (stall ∘ mapᵖ pred) (weaken-lemma sub 𝒞Δ ⊢M)
weaken-lemma sub 𝒞Δ (⊢?⁰ ⊢L ⊢M ⊢N) =
  ap δ $
  ap³-simple ifz^ (weaken-lemma sub 𝒞Δ ⊢M)
                  (weaken-lemma sub 𝒞Δ ⊢N)
                  (weaken-lemma sub 𝒞Δ ⊢L)

subst-lemma : ∀ {M} {x} {S} {T} {N} {Γ}
            → (𝒞Γ : 𝒞⟦ Γ ⟧)
            → (⊢N : ∅ ⊢ N ⦂ S)
            → (⊢M : Γ , x ⦂ S ⊢ M ⦂ T)
            → ℰ⟦ subst-ty ⊢N ⊢M ⟧ 𝒞Γ ＝ ℰ⟦ ⊢M ⟧ (𝒞Γ ＆ ℰ⟦ ⊢N ⟧ 𝒞∅)
subst-lemma {x = y} {S} {N} 𝒞Γ ⊢N (⊢` (here {x} ei eT)) with x ≟ y
... | yes prf =
        J (λ T₁ e₁ → (⊢N₁ : ∅ ⊢ N ⦂ S)
                   → ℰ⟦ weaken-∅ _ (subst (∅ ⊢ N ⦂_) e₁ ⊢N₁) ⟧ 𝒞Γ
                   ＝ subst (𝒯⟦_⟧) e₁ (ℰ⟦ ⊢N₁ ⟧ 𝒞∅))
          (λ ⊢N₁ →   ap (λ q → ℰ⟦ weaken-∅ _ q ⟧ 𝒞Γ)
                         (subst-refl {B = (∅ ⊢ N ⦂_)} ⊢N₁)
                    ∙ weaken-lemma ⊆-∅ 𝒞Γ ⊢N₁
                    ∙ ap ℰ⟦ ⊢N₁ ⟧ (weaken-𝒞-∅ 𝒞Γ)
                    ∙ sym (subst-refl {B = 𝒯⟦_⟧} (ℰ⟦ ⊢N₁ ⟧ 𝒞∅)))
          (sym eT) ⊢N
... | no ctra = absurd (ctra ei)
subst-lemma {x = y}         𝒞Γ ⊢N (⊢` (there {x} ne ix)) with x ≟ y
... | yes prf = absurd (ne prf)
... | no ctra = refl
subst-lemma {x = y} {S} {Γ} 𝒞Γ ⊢N (⊢ƛ {x} {N} {A} {B} e ⊢M) with x ≟ y
... | yes prf =
        fun-ext λ ta →
          J (λ y₁ ey → (⊢M₁ : Γ , y₁ ⦂ S , x ⦂ A ⊢ N ⦂ B)
                      → ℰ⟦ drop (subst (λ q → (Γ , q ⦂ S , x ⦂ A) ⊢ N ⦂ B) (sym ey) ⊢M₁) ⟧ (𝒞Γ ＆ ta)
                      ＝ ℰ⟦ ⊢M₁ ⟧ ((𝒞Γ ＆ ℰ⟦ ⊢N ⟧ 𝒞∅) ＆ ta))
            (λ ⊢M₁ →   ap (λ q → ℰ⟦ drop q ⟧ (𝒞Γ ＆ ta))
                           (subst-refl {B = λ q → (Γ , q ⦂ S , x ⦂ A) ⊢ N ⦂ B} ⊢M₁)
                      ∙ weaken-lemma ⊆-shadow (𝒞Γ ＆ ta) ⊢M₁
                      ∙ ap (ℰ⟦ ⊢M₁ ⟧) (weaken-𝒞-shadow 𝒞Γ ta (ℰ⟦ ⊢N ⟧ 𝒞∅)))
            prf ⊢M
... | no ctra =
        fun-ext λ ta →
            subst-lemma (𝒞Γ ＆ ta) ⊢N (swap ctra ⊢M)
          ∙ weaken-lemma (⊆-exch ctra) ((𝒞Γ ＆ ta) ＆ ℰ⟦ ⊢N ⟧ 𝒞∅) ⊢M
          ∙ ap ℰ⟦ ⊢M ⟧ (weaken-𝒞-exch ctra 𝒞Γ ta (ℰ⟦ ⊢N ⟧ 𝒞∅))
subst-lemma                 𝒞Γ ⊢N (⊢M ⊢· ⊢M₁)              =
  ap δ $
  ap² _$_ (subst-lemma 𝒞Γ ⊢N ⊢M)
          (subst-lemma 𝒞Γ ⊢N ⊢M₁)
subst-lemma                 𝒞Γ ⊢N (⊢Y ⊢M)                   =
  ap (λ q → fix (θ ∘ ▹map q)) (subst-lemma 𝒞Γ ⊢N ⊢M)
subst-lemma                 𝒞Γ ⊢N  ⊢＃                       = refl
subst-lemma                 𝒞Γ ⊢N (⊢𝓈 ⊢M)                   =
  ap (stall ∘ mapᵖ suc) (subst-lemma 𝒞Γ ⊢N ⊢M)
subst-lemma                 𝒞Γ ⊢N (⊢𝓅 ⊢M)                   =
  ap (stall ∘ mapᵖ pred) (subst-lemma 𝒞Γ ⊢N ⊢M)
subst-lemma                 𝒞Γ ⊢N (⊢?⁰ ⊢M ⊢M₁ ⊢M₂)         =
  ap δ $
  ap³-simple ifz^ (subst-lemma 𝒞Γ ⊢N ⊢M₁)
                  (subst-lemma 𝒞Γ ⊢N ⊢M₂)
                  (subst-lemma 𝒞Γ ⊢N ⊢M)

-- 2.18

step-sound : ∀ {k M N}
           → M —→⁅ k ⁆ N
           → (⊢M : ∅ ⊢ M ⦂ T)
           → (⊢N : ∅ ⊢ N ⦂ T)
           → ℰ⟦ ⊢M ⟧ 𝒞∅ ＝ (δ ⁽ k ⁾) (ℰ⟦ ⊢N ⟧ 𝒞∅)
step-sound {T}       {.s¹} {.((ƛ x ⦂ A ⇒ M) · N)}   {.(M [ x := N ])}  (β-ƛ {x} {M} {N} {A})         (⊢ƛ e ⊢M ⊢· ⊢N)       ⊢MN                 =
  ap δ $
  sym (ap (λ q → ℰ⟦ q ⟧ 𝒞∅) (is-prop-β ⊢-is-prop ⊢MN (subst-ty ⊢N ⊢M))
     ∙ subst-lemma 𝒞∅ ⊢N ⊢M)
step-sound {T}       {.s¹} {.(Y M)}                {.(M · Y M)}        (Ｙ {M})                      (⊢Y ⊢M)               (⊢M₁ ⊢· ⊢Y ⊢M₂)    =
  {!!}
--    happly (Y-· ⊢M) 𝒞∅
--  ∙ ap δ (ap (ℰ⟦ ⊢M ⟧ 𝒞∅) (happly (Y-· ⊢M) 𝒞∅) ∙ {!!})
{-
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
-}
step-sound {T}       {.s¹} {.(𝓈 (＃ n))}            {.(＃ suc n)}       (β-𝓈 {n})                    (⊢𝓈 (⊢＃ {n}))         (⊢＃ {n = suc n})    = refl
step-sound {T}       {.s¹} {.(𝓅 (＃ 0))}            {.(＃ 0)}           β-𝓅⁰                        (⊢𝓅 (⊢＃ {n = 0}))     (⊢＃ {n = 0})        = refl
step-sound {T}       {.s¹} {.(𝓅 (＃ suc n))}        {.(＃ n)}           (β-𝓅ˢ {n})                  (⊢𝓅 (⊢＃ {n = suc n})) (⊢＃ {n})            = refl
step-sound {T}       {.s¹} {.(?⁰ ＃ 0 ↑ M ↓ N)}     {N = M}            (β-?⁰ {M} {N})               (⊢?⁰ ⊢＃ ⊢M ⊢N)        ⊢M₁                =
  ap (λ q → δ (ℰ⟦ q ⟧ 𝒞∅)) (is-prop-β ⊢-is-prop ⊢M ⊢M₁)
step-sound {T}       {.s¹} {.(?⁰ ＃ suc n ↑ M ↓ N)} {N}                (β-?ˢ {M} {N} {n})           (⊢?⁰ ⊢＃ ⊢M ⊢N)        ⊢N₁                =
  ap (λ q → δ (ℰ⟦ q ⟧ 𝒞∅)) (is-prop-β ⊢-is-prop ⊢N ⊢N₁)
step-sound {T}       {.k}  {.(M · N)}               {.(M′ · N)}        (ξ-· {M} {M′} {k} {N} s)     (⊢M ⊢· ⊢N)             (⊢M′ ⊢· ⊢N₁)      =
  ap δ (J (λ A¹ eA → (⊢M¹ : ∅ ⊢ M′ ⦂ A¹ ⇒ T)
                   → (⊢N¹ : ∅ ⊢ N ⦂ A¹)
                   → ℰ⟦ ⊢M ⟧ 𝒞∅ (ℰ⟦ ⊢N ⟧ 𝒞∅) ＝ (δ ⁽ k ⁾) (ℰ⟦ ⊢M¹ ⟧ 𝒞∅ (ℰ⟦ ⊢N¹ ⟧ 𝒞∅)))
          (λ ⊢M¹ ⊢N¹ → ap (λ q → q (ℰ⟦ ⊢N ⟧ 𝒞∅)) (step-sound s ⊢M ⊢M¹)
                      ∙ ap (λ q → (δ ⁽ k ⁾) (ℰ⟦ ⊢M¹ ⟧ 𝒞∅) (ℰ⟦ q ⟧ 𝒞∅)) (is-prop-β ⊢-is-prop ⊢N ⊢N¹)
                      ∙ δ-ap {k = k} (ℰ⟦ ⊢M¹ ⟧ 𝒞∅) (ℰ⟦ ⊢N¹ ⟧ 𝒞∅))
          (⊢-unique ⊢N ⊢N₁)
           ⊢M′ ⊢N₁)
  ∙ sym (δ-comm {k} (ℰ⟦ ⊢M′ ⟧ 𝒞∅ (ℰ⟦ ⊢N₁ ⟧ 𝒞∅)))
step-sound {T = .𝓝} {.k}  {.(𝓈 M)}                 {.(𝓈 M′)}          (ξ-𝓈 {M} {M′} {k} s)         (⊢𝓈 ⊢M)                (⊢𝓈 ⊢M′)           =
  ap (stall ∘ mapᵖ suc) (step-sound s ⊢M ⊢M′)
  ∙ ap stall (δ-map {k = k} (ℰ⟦ ⊢M′ ⟧ 𝒞∅) suc)
  ∙ sym (δ-comm {k = k} (mapᵖ suc (ℰ⟦ ⊢M′ ⟧ 𝒞∅)))
step-sound {T = .𝓝} {.k}  {.(𝓅 M)}                 {.(𝓅 M′)}          (ξ-𝓅 {M} {M′} {k} s)        (⊢𝓅 ⊢M)                (⊢𝓅 ⊢M′)           =
  ap (stall ∘ mapᵖ pred) (step-sound s ⊢M ⊢M′)
  ∙ ap stall (δ-map {k = k} (ℰ⟦ ⊢M′ ⟧ 𝒞∅) pred)
  ∙ sym (δ-comm {k = k} (mapᵖ pred (ℰ⟦ ⊢M′ ⟧ 𝒞∅)))
step-sound {T}       {.k}  {.(?⁰ L ↑ M ↓ N)}        {.(?⁰ L′ ↑ M ↓ N)} (ξ-? {L} {L′} {M} {N} {k} s) (⊢?⁰ ⊢L ⊢M ⊢N)       (⊢?⁰ ⊢L′ ⊢M₁ ⊢N₁) =
  ap δ (ap² (λ q w → ifz^ (ℰ⟦ q ⟧ 𝒞∅) (ℰ⟦ w ⟧ 𝒞∅) (ℰ⟦ ⊢L ⟧ 𝒞∅))
            (is-prop-β ⊢-is-prop ⊢M ⊢M₁)
            (is-prop-β ⊢-is-prop ⊢N ⊢N₁))
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
  let ⊢P = rtc0-preserve sP ⊢M
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
soundness {M} {N} {V} {k} iV M⇓ ⊢M ⊢N =
  rtc-sound (big→small-rtc-v {k = k} {M = M} iV M⇓) ⊢M ⊢N
-}

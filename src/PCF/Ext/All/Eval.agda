{-# OPTIONS --guarded #-}
module PCF.Ext.All.Eval where

open import Prelude hiding (_⊆_)
open import Data.Empty
open import Data.Dec
open import Data.Nat hiding (_·_)
open import Data.List
open import Data.String

open import Later
open import Interlude
open import Guarded.Partial
open import PCF.Ext.TyTerm
open import PCF.Ext.Subst
open import PCF.Ext.TyDeriv
open import PCF.Ext.All.Bigstep
open import PCF.Ext.All.Smallstep
open import PCF.Ext.All.Correspondence

private variable
  Γ Δ : Ctx
  T : Ty

δᵖ-comm : ∀ {k A} {x : Part A}
        → (δᵖ ⁽ k ⁾) (δᵖ x) ＝ δᵖ ((δᵖ ⁽ k ⁾) x)
δᵖ-comm {k = s⁰} = refl
δᵖ-comm {k = s¹} = refl

δᵖ-map : ∀ {k A B} {f : A → B} {x : Part A}
       → mapᵖ f ((δᵖ ⁽ k ⁾) x) ＝ (δᵖ ⁽ k ⁾) (mapᵖ f x)
δᵖ-map {k = s⁰} = refl
δᵖ-map {k = s¹} = refl

δᵖ-bind : ∀ {k A B} {f : A → Part B} {x : Part A}
        → ((δᵖ ⁽ k ⁾) x >>=ᵖ f) ＝ (δᵖ ⁽ k ⁾) (x >>=ᵖ f)
δᵖ-bind {k = s⁰} = refl
δᵖ-bind {k = s¹} = refl

-- typed value : `∅ ⊢ v ⦂ T`
TVal : Ty → 𝒰
TVal T = Σ[ q ꞉ Term ] (Σ[ v ꞉ Val ] (IsVal q v) × (∅ ⊢ q ⦂ T))

ℕVal : ℕ → TVal 𝓝
ℕVal n = ＃ n , v-＃ n , is-＃ {n} , ⊢＃

-- Escardo'99 calls this a "contractive endomap of a suitable complete metric space"
-- it's a guarded bigstep evaluator
Φ-· : ▹ ((T : Ty) → (t : Term) → ∅ ⊢ t  ⦂ T → Part (TVal T))
    → (A : Ty) → (T : Ty)
    → (M : Term) → (tM : ∅ ⊢ M ⦂ A)
    → TVal (A ⇒ T) → Part (TVal T)
Φ-· ih▹ A T M tM (.(ƛ x ⦂ S ⇒ N) , .(v-ƛ x S N) , is-ƛ {x} {A = S} {t = N} , ⊢ƛ e vt) =
  later (ih▹ ⊛ next T ⊛ next (N [ x := M ]) ⊛ next (subst-ty tM vt))

Φ-𝓈 : TVal 𝓝 → TVal 𝓝
Φ-𝓈 (.(＃ n) , .(v-＃ n) , is-＃ {n} , ⊢＃) = ℕVal (suc n)

Φ-𝓅 : TVal 𝓝 → TVal 𝓝
Φ-𝓅 (.(＃ n) , .(v-＃ n) , is-＃ {n} , ⊢＃) = ℕVal (pred n)

Φ-? : ▹ ((T : Ty) → (t : Term) → ∅ ⊢ t  ⦂ T → Part (TVal T))
    → (T : Ty)
    → (M : Term) → (tM : ∅ ⊢ M ⦂ T)
    → (N : Term) → (tN : ∅ ⊢ N ⦂ T)
    → TVal 𝓝 → Part (TVal T)
Φ-? ih▹ T M tM N tN (.(＃ zero)  , .(v-＃ zero)    , is-＃ {(zero)} , ⊢＃) =
  later (ih▹ ⊛ next T ⊛ next M ⊛ next tM)
Φ-? ih▹ T M tM N tN (.(＃ suc n) , .(v-＃ (suc n)) , is-＃ {suc n}  , ⊢＃) =
  later (ih▹ ⊛ next T ⊛ next N ⊛ next tN)

Φ : ▹ ((T : Ty) → (t : Term) → ∅ ⊢ t  ⦂ T → Part (TVal T))
  → (T : Ty) → (t : Term) → ∅ ⊢ t  ⦂ T → Part (TVal T)
Φ ih▹ .(A ⇒ B) .(ƛ x ⦂ T ⇒ N) (⊢ƛ {x} {N} {A} {B} {T} e tT) =
  now (ƛ x ⦂ T ⇒ N , v-ƛ x T N , is-ƛ , ⊢ƛ e tT)
Φ ih▹ T .(L · M) (_⊢·_ {L} {M} {A} {B} tL tM) =
  Φ ih▹ (A ⇒ B) L tL >>=ᵖ (Φ-· ih▹ A T M tM)
Φ ih▹ T .(Y M) (⊢Y {M} tT) =
  later $ ih▹ ⊛ next T ⊛ next (M · Y M) ⊛ next (tT ⊢· ⊢Y tT)
Φ ih▹ .𝓝 .(＃ n) (⊢＃ {n}) =
  now (＃ n , v-＃ n , is-＃ {n} , ⊢＃)
Φ ih▹ .𝓝 .(𝓈 M) (⊢𝓈 {M} tT) =
  δᵖ $ mapᵖ Φ-𝓈 (Φ ih▹ 𝓝 M tT)
Φ ih▹ .𝓝 .(𝓅 M) (⊢𝓅 {M} tT) =
  δᵖ $ mapᵖ Φ-𝓅 (Φ ih▹ 𝓝 M tT)
Φ ih▹ T .(?⁰ L ↑ M ↓ N) (⊢?⁰ {L} {M} {N} tL tM tN) =
  Φ ih▹ 𝓝 L tL >>=ᵖ (Φ-? ih▹ T M tM N tN)

Eval : (T : Ty) → (t : Term) → ∅ ⊢ t  ⦂ T → Part (TVal T)
Eval = fix Φ

Eval-· : (A : Ty) → (T : Ty) → (M : Term) → (tM : ∅ ⊢ M ⦂ A)
       → TVal (A ⇒ T) → Part (TVal T)
Eval-· = Φ-· (dfix Φ)

Eval-? : (T : Ty) → (M : Term) → (tM : ∅ ⊢ M ⦂ T) → (N : Term) → (tN : ∅ ⊢ N ⦂ T)
       → TVal 𝓝 → Part (TVal T)
Eval-? = Φ-? (dfix Φ)

Eval-val : ∀ {N V}
          → (iV : IsVal N V)
          → (⊢N : ∅ ⊢ N ⦂ T)
          → Eval T N ⊢N ＝ now (N , V , iV , ⊢N)
Eval-val is-＃ ⊢＃       = refl
Eval-val is-ƛ (⊢ƛ e ⊢N) = refl

-- Escardo'99 8.2

step-sound : ∀ {k M N}
           → M —→⁅ k ⁆ N
           → (⊢M : ∅ ⊢ M ⦂ T)
           → (⊢N : ∅ ⊢ N ⦂ T)
           → Eval T M ⊢M ＝ (δᵖ ⁽ k ⁾) (Eval T N ⊢N)
step-sound {T} (β-ƛ {x} {M} {N} {A}) (⊢ƛ e ⊢M ⊢· ⊢N)  ⊢MN              =
  ap later (▹-ext λ α i → pfix Φ i α T (M [ x := N ]) (subst-ty ⊢N ⊢M))  -- TODO rewrite
  ∙ ap (δᵖ ∘ Eval T (M [ x := N ])) (is-prop-β ⊢-is-prop (subst-ty ⊢N ⊢M) ⊢MN)
step-sound {T}  Ｙ                    (⊢Y {M} ⊢M)     (⊢M₁ ⊢· ⊢Y ⊢M₂) =
  ap later (▹-ext λ α i → pfix Φ i α T (M · Y M) (⊢M ⊢· ⊢Y ⊢M))  -- TODO rewrite
  ∙ J (λ S eS → (⊢M¹ : ∅ ⊢ M ⦂ S ⇒ T)
              → (⊢M² : ∅ ⊢ M ⦂ S ⇒ S)
              → δᵖ (Eval T (M · Y M) (⊢M ⊢· ⊢Y ⊢M)) ＝ δᵖ (Eval T (M · Y M) (⊢M¹ ⊢· ⊢Y ⊢M²)))
      (λ ⊢M¹ ⊢M² → ap² (λ q w → δᵖ (Eval T (M · Y M) (q ⊢· ⊢Y w)))
                        (is-prop-β ⊢-is-prop ⊢M ⊢M¹)
                        (is-prop-β ⊢-is-prop ⊢M ⊢M²)
                        )
      (fst $ ⇒-inj $ ⊢-unique ⊢M ⊢M₁)
       ⊢M₁ ⊢M₂
step-sound      β-𝓈 (⊢𝓈 ⊢＃) ⊢＃ = refl
step-sound      β-𝓅⁰ (⊢𝓅 ⊢＃) ⊢＃ = refl
step-sound      β-𝓅ˢ (⊢𝓅 ⊢＃) ⊢＃ = refl
step-sound {T}  β-?⁰ (⊢?⁰ {M} ⊢＃ ⊢M ⊢N) ⊢M₀ =
  ap later (▹-ext λ α i → pfix Φ i α T M ⊢M)  -- TODO rewrite
  ∙ ap (λ q → δᵖ (Eval T M q)) (is-prop-β ⊢-is-prop ⊢M ⊢M₀)
step-sound {T}  β-?ˢ (⊢?⁰ {N} ⊢＃ ⊢M ⊢N) ⊢N₀ =
  ap later (▹-ext λ α i → pfix Φ i α T N ⊢N)  -- TODO rewrite
  ∙ ap (λ q → δᵖ (Eval T N q)) (is-prop-β ⊢-is-prop ⊢N ⊢N₀)
step-sound {T} (ξ-· {M} {M′} {k} {N} s) (_⊢·_ {A} ⊢M ⊢N) (⊢M₁ ⊢· ⊢N₁) =
  J (λ A¹ eA → (⊢M¹ : ∅ ⊢ M′ ⦂ A¹ ⇒ T)
             → (⊢N¹ : ∅ ⊢ N ⦂ A¹)
             →  Eval T (M · N) (⊢M ⊢· ⊢N) ＝ (δᵖ ⁽ k ⁾) (Eval T (M′ · N) (⊢M¹ ⊢· ⊢N¹)))
    (λ ⊢M¹ ⊢N¹ → ap (_>>=ᵖ Eval-· A T N ⊢N) (step-sound s ⊢M ⊢M¹)
                  ∙ δᵖ-bind {k = k}
                  ∙ ap (λ q → (δᵖ ⁽ k ⁾) (Eval T (M′ · N) (⊢M¹ ⊢· q))) (is-prop-β ⊢-is-prop ⊢N ⊢N¹))
    (⊢-unique ⊢N ⊢N₁)
    ⊢M₁ ⊢N₁
step-sound     (ξ-𝓈 {k} s) (⊢𝓈 ⊢M) (⊢𝓈 ⊢N) =
  ap (δᵖ ∘ mapᵖ Φ-𝓈) (step-sound s ⊢M ⊢N)
  ∙ ap δᵖ (δᵖ-map {k = k})
  ∙ sym (δᵖ-comm {k = k})
step-sound     (ξ-𝓅 {k} s) (⊢𝓅 ⊢M) (⊢𝓅 ⊢N) =
  ap (δᵖ ∘ mapᵖ Φ-𝓅) (step-sound s ⊢M ⊢N)
  ∙ ap δᵖ (δᵖ-map {k = k})
  ∙ sym (δᵖ-comm {k = k})
step-sound {T} (ξ-? {L} {L′} {M} {N} {k} s) (⊢?⁰ ⊢L ⊢M ⊢N) (⊢?⁰ ⊢L′ ⊢M₁ ⊢N₁) =
  ap (_>>=ᵖ Eval-? T M ⊢M N ⊢N) (step-sound s ⊢L ⊢L′)
  ∙ δᵖ-bind {k = k}
  ∙ ap² (λ q w → (δᵖ ⁽ k ⁾) (Eval 𝓝 L′ ⊢L′ >>=ᵖ Eval-? T M q N w))
        (is-prop-β ⊢-is-prop ⊢M ⊢M₁)
        (is-prop-β ⊢-is-prop ⊢N ⊢N₁)

rtc0-sound : ∀ {M N}
           → M —↠⁰ N
           → (⊢M : ∅ ⊢ M ⦂ T)
           → (⊢N : ∅ ⊢ N ⦂ T)
           → Eval T M ⊢M ＝ Eval T N ⊢N
rtc0-sound {T} {M} {.M} (.M ∎ᵣ)         ⊢M ⊢N =
  ap (Eval T M) (is-prop-β ⊢-is-prop ⊢M ⊢N)
rtc0-sound {M} {N}  (.M —→⟨ S ⟩ MS) ⊢M ⊢N =
  let ⊢M₁ = preserve S ⊢M in
  step-sound S ⊢M ⊢M₁ ∙ rtc0-sound MS ⊢M₁ ⊢N

rtc-sound : ∀ {M N k}
          → M =⇒⁅ k ⁆ᵗ N
          → (⊢M : ∅ ⊢ M ⦂ T)
          → (⊢N : ∅ ⊢ N ⦂ T)
          → Eval T M ⊢M ＝ (iter k δᵖ) (Eval T N ⊢N)
rtc-sound {T} {M} {N} {k = zero}  (P , sP , eP)          ⊢M ⊢N =
  J (λ Q eQ → M —↠⁰ Q
            → Eval T M ⊢M ＝ Eval T N ⊢N)
    (λ sQ → rtc0-sound sQ ⊢M ⊢N)
    (sym eP) sP
rtc-sound             {k = suc k} (P , R , sP , sR , S▹) ⊢M ⊢N =
  let ⊢P = rtc0-preserve sP ⊢M
      ⊢R = preserve sR ⊢P
    in
    rtc0-sound sP ⊢M ⊢P
  ∙ step-sound sR ⊢P ⊢R
  ∙ ap later (▹-ext $ ▹map (λ q → rtc-sound q ⊢R ⊢N) S▹)

soundness : ∀ {M N V k}
          → (iV : IsVal N V)
          → M ⇓⁅ k ⁆ᵛ V
          → (⊢M : ∅ ⊢ M ⦂ T)
          → (⊢N : ∅ ⊢ N ⦂ T)
          → Eval T M ⊢M ＝ delay-by k (N , V , iV , ⊢N)
soundness {M} {k} iV M⇓ ⊢M ⊢N =
  rtc-sound (big→small-rtc-v {k = k} {M = M} iV M⇓) ⊢M ⊢N
  ∙ ap (iter k δᵖ) (Eval-val iV ⊢N)

{-
completeness-body : ▹ (∀ M k Q m N V iV
                       → (⊢M : ∅ ⊢ M ⦂ T)
                       → (⊢N : ∅ ⊢ N ⦂ T)
                       → Q V m
                       → Eval T M ⊢M ＝ delay-by (m + k) (N , V , iV , ⊢N)
                       → M ⇓⁅ k ⁆ Q)
                  → ∀ M k Q m N V iV
                  → (⊢M : ∅ ⊢ M ⦂ T)
                  → (⊢N : ∅ ⊢ N ⦂ T)
                  → Q V m
                  → Eval T M ⊢M ＝ delay-by (m + k) (N , V , iV , ⊢N)
                  → M ⇓⁅ k ⁆ Q
completeness-body ih▹ .(ƛ _ ⦂ _ ⇒ _) k Q m N V iV (⊢ƛ x₂ tM) ⊢N x x₁ = {!!}
completeness-body ih▹ .(_ · _) k Q m N V iV (tM ⊢· tM₁) ⊢N x x₁ = {!!}
completeness-body ih▹ .(Y _) k Q m N V iV (⊢Y tM) ⊢N x x₁ = {!!}
completeness-body ih▹ .(＃ _) k Q m N V iV ⊢＃ ⊢N x x₁ = {!!}
completeness-body ih▹ .(𝓈 M) k Q m .(＃ n) .(v-＃ n) (is-＃ {n}) (⊢𝓈 {M = M} tM) ⊢N x x₁ =
  completeness-body ih▹ M k (Q𝓈 Q) (suc m) (＃ n) (v-＃ n) (is-＃ {n}) tM ⊢N {!!} {!!}
completeness-body ih▹ .(𝓅 _) k Q m N V iV (⊢𝓅 tM) ⊢N x x₁ = {!!}
completeness-body ih▹ .(?⁰ _ ↑ _ ↓ _) k Q m N V iV (⊢?⁰ tM tM₁ tM₂) ⊢N x x₁ = {!!}
-}
{-
rtc0-complete : ∀ {M N V}
             → (iV : IsVal N V)
             → (⊢M : ∅ ⊢ M ⦂ T)
             → (⊢N : ∅ ⊢ N ⦂ T)
             → Eval T M ⊢M ＝ now (N , V , iV , ⊢N)
             → M —↠⁰ N
rtc0-complete is-＃ (tM ⊢· tM₁)             ⊢＃ eq = {!!}
rtc0-complete is-＃ (⊢Y tM)                 ⊢＃ eq = absurd (now≠later (sym eq))
rtc0-complete is-＃ (⊢＃ {n})               ⊢＃ eq =
  let en = v-＃-inj $ ap (fst ∘ snd) (now-inj eq) in
  subst (λ q → ＃ n —↠⁰ ＃ q) en (＃ n ∎ᵣ)
rtc0-complete is-＃ (⊢𝓈 tM)                ⊢＃ eq = absurd (now≠later (sym eq))
rtc0-complete is-＃ (⊢𝓅 tM)                ⊢＃ eq = absurd (now≠later (sym eq))
rtc0-complete is-＃ (⊢?⁰ tM tM₁ tM₂)       ⊢＃ eq = {!!}
rtc0-complete is-ƛ  (⊢ƛ {x} {N} {T} e tM) (⊢ƛ {x = x₁} {N = N₁} {T = T₁} e₁ tN) eq =
  let el = v-ƛ-inj $ ap (fst ∘ snd) (now-inj eq) in
  subst (λ q → ƛ x ⦂ T ⇒ N —↠⁰ ƛ q ⦂ T₁ ⇒ N₁) (fst el) $
  subst (λ q → ƛ x ⦂ T ⇒ N —↠⁰ ƛ x ⦂ q ⇒ N₁) (fst $ snd el) $
  subst (λ q → ƛ x ⦂ T ⇒ N —↠⁰ ƛ x ⦂ T ⇒ q) (snd $ snd el) (ƛ x ⦂ T ⇒ N ∎ᵣ)
rtc0-complete is-ƛ  (tM ⊢· tM₁)           (⊢ƛ e tN) eq = {!!}
rtc0-complete is-ƛ  (⊢Y tM)               (⊢ƛ e tN) eq = absurd (now≠later (sym eq))
rtc0-complete is-ƛ  (⊢?⁰ tM tM₁ tM₂)      (⊢ƛ e tN) eq = {!!}

rtc-complete-v : ∀ {M N V k}
             → (iV : IsVal N V)
             → (⊢M : ∅ ⊢ M ⦂ T)
             → (⊢N : ∅ ⊢ N ⦂ T)
             → Eval T M ⊢M ＝ delay-by k (N , V , iV , ⊢N)
             → M =⇒⁅ k ⁆ᵗ N
rtc-complete-v {N} {k = zero}  iV ⊢M ⊢N eq = N , (rtc0-complete iV ⊢M ⊢N eq) , refl
rtc-complete-v {k = suc k} iV (⊢ƛ x tM) ⊢N eq = absurd (now≠later eq)
rtc-complete-v {k = suc k} iV (tM ⊢· tM₁) ⊢N eq = {!!}
rtc-complete-v {k = suc k} iV (⊢Y tM) ⊢N eq = {!!}
rtc-complete-v {k = suc k} iV ⊢＃ ⊢N eq = absurd (now≠later eq)
rtc-complete-v {k = suc k} iV (⊢𝓈 tM) ⊢N eq = {!!}
rtc-complete-v {k = suc k} iV (⊢𝓅 tM) ⊢N eq = {!!}
rtc-complete-v {k = suc k} iV (⊢?⁰ tM tM₁ tM₂) ⊢N eq = {!!}

completeness-body : ∀ {N V}
                  → (iV : IsVal N V)
                  → (⊢N : ∅ ⊢ N ⦂ T)
                  → ▹ (∀ M k
                       → (⊢M : ∅ ⊢ M ⦂ T)
                       → Eval T M ⊢M ＝ delay-by k (N , V , iV , ⊢N)
                       → M ⇓⁅ k ⁆ᵛ V)
                  → ∀ M k
                  → (⊢M : ∅ ⊢ M ⦂ T)
                  → Eval T M ⊢M ＝ delay-by k (N , V , iV , ⊢N)
                  → M ⇓⁅ k ⁆ᵛ V
completeness-body iV ⊢N ih▹ .(ƛ _ ⦂ _ ⇒ _) zero (⊢ƛ x tM) eq = refl , {!!}
completeness-body iV ⊢N ih▹ .(ƛ _ ⦂ _ ⇒ _) (suc k) (⊢ƛ x tM) eq = {!!}
completeness-body iV ⊢N ih▹ .(_ · _) k (tM ⊢· tM₁) eq = {!!}
completeness-body iV ⊢N ih▹ .(Y _) k (⊢Y tM) eq = {!!}
completeness-body iV ⊢N ih▹ .(＃ _) zero ⊢＃ eq = {!!}
completeness-body iV ⊢N ih▹ .(＃ _) (suc k) ⊢＃ eq = {!!}
completeness-body iV ⊢N ih▹ .(𝓈 M) zero (⊢𝓈 {M = M} tM) eq = {!!}
completeness-body iV ⊢N ih▹ .(𝓈 M) (suc k) (⊢𝓈 {M = M} tM) eq =
  let qq = completeness-body iV ⊢N ih▹ M k tM {!!} in
  {!!}
completeness-body iV ⊢N ih▹ .(𝓅 _) k (⊢𝓅 tM) eq = {!!}
completeness-body iV ⊢N ih▹ .(?⁰ _ ↑ _ ↓ _) k (⊢?⁰ tM tM₁ tM₂) eq = {!!}

completeness : ∀ {N V}
             → (iV : IsVal N V)
             → (⊢N : ∅ ⊢ N ⦂ T)
             → ∀ M k
             → (⊢M : ∅ ⊢ M ⦂ T)
             → Eval T M ⊢M ＝ delay-by k (N , V , iV , ⊢N)
             → M ⇓⁅ k ⁆ᵛ V
completeness iV ⊢N M k ⊢M e = {!!}
--  small-rtc→big-v {k = k} {M = M} iV (rtc-complete-v iV ⊢M ⊢N e)
-}

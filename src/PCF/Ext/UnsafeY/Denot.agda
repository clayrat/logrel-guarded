{-# OPTIONS --guarded #-}
module PCF.Ext.UnsafeY.Denot where

open import Prelude
open import Data.Empty
open import Data.Nat

open import Later
open import Interlude
open import Guarded.Partial
open import PCF.Ext.TyTerm
open import PCF.Ext.TyDeriv

private variable
  Γ Δ : Ctx
  T : Ty

-- Denotation of types
𝒯⟦_⟧ : Ty → 𝒰
𝒯⟦ 𝓝 ⟧    = Part ℕ
𝒯⟦ S ⇒ T ⟧ = 𝒯⟦ S ⟧ → 𝒯⟦ T ⟧

θ : ▹Alg (𝒯⟦ T ⟧)
θ {T = 𝓝} x▹     = later x▹
θ {S ⇒ T}  tf▹ ts = θ (tf▹ ⊛ next ts)

δ : 𝒯⟦ T ⟧ → 𝒯⟦ T ⟧
δ = θ ∘ next

^-body : ∀ {A}
       → (A → 𝒯⟦ T ⟧)
       → ▹ (Part A → 𝒯⟦ T ⟧)
       → Part A → 𝒯⟦ T ⟧
^-body f f^▹ (now x)    = f x
^-body f f^▹ (later p▹) = θ (f^▹ ⊛ p▹)

_^ : ∀ {A}
   → (A → 𝒯⟦ T ⟧)
   → Part A → 𝒯⟦ T ⟧
(f ^) = fix (^-body f)

-- Denotation of contexts
𝒞⟦_⟧ : Ctx → 𝒰
𝒞⟦ Γ ⟧ = ∀ T x → Γ ∋ x ⦂ T → 𝒯⟦ T ⟧

𝒞∅ : 𝒞⟦ ∅ ⟧
𝒞∅ T x i = absurd (∅-empty i)

-- Extending denoted contexts
_＆_ : ∀ {i}
     → 𝒞⟦ Γ ⟧ → 𝒯⟦ T ⟧ → 𝒞⟦ Γ , i ⦂ T ⟧
(_ ＆ a) _ _ (here ei et) = subst 𝒯⟦_⟧ (sym et) a
(ρ ＆ _) T x (there ne i) = ρ T x i

-- Denotation of terms
ifz : 𝒯⟦ T ⟧ → 𝒯⟦ T ⟧ → ℕ → 𝒯⟦ T ⟧
ifz x y  zero   = x
ifz x y (suc n) = y

ifz^ : 𝒯⟦ T ⟧ → 𝒯⟦ T ⟧ → 𝒯⟦ 𝓝 ⟧ → 𝒯⟦ T ⟧
ifz^ x y = (ifz x y) ^

ℰ⟦_⟧ : ∀ {t}
     → Γ ⊢ t ⦂ T → 𝒞⟦ Γ ⟧ → 𝒯⟦ T ⟧
ℰ⟦ ⊢` i ⟧          γ = γ _ _ i
ℰ⟦ ⊢ƛ e ⊢t ⟧       γ = λ ta → ℰ⟦ ⊢t ⟧ (γ ＆ ta)
ℰ⟦ ⊢r ⊢· ⊢s ⟧     γ = ℰ⟦ ⊢r ⟧ γ (ℰ⟦ ⊢s ⟧ γ)
ℰ⟦ ⊢Y ⊢t ⟧        γ = fix $ θ ∘ ▹map (ℰ⟦ ⊢t ⟧ γ)
ℰ⟦ ⊢＃ {n} ⟧        γ = now n
ℰ⟦ ⊢𝓈 ⊢t ⟧         γ = mapᵖ suc (ℰ⟦ ⊢t ⟧ γ)
ℰ⟦ ⊢𝓅 ⊢t ⟧         γ = mapᵖ pred (ℰ⟦ ⊢t ⟧ γ)
ℰ⟦ ⊢?⁰ ⊢r ⊢s ⊢t ⟧ γ = ifz^ (ℰ⟦ ⊢s ⟧ γ) (ℰ⟦ ⊢t ⟧ γ) (ℰ⟦ ⊢r ⟧ γ)

-- 2.15

Y-δ : ∀ {t}
    → (⊢t : Γ ⊢ t ⦂ T ⇒ T)
    → ℰ⟦ ⊢Y ⊢t ⟧ ＝ δ ∘ ℰ⟦ ⊢t ⊢· (⊢Y ⊢t) ⟧
Y-δ ⊢t = fun-ext λ γ → fix-path (λ ta▹ → θ (▹map (ℰ⟦ ⊢t ⟧ γ) ta▹))

-- 2.16

ifz-δ : ∀ {L L′ M N γ}
       → (⊢L  : Γ ⊢ L  ⦂ 𝓝)
       → (⊢L′ : Γ ⊢ L′ ⦂ 𝓝)
       → (⊢M : Γ ⊢ M ⦂ T)
       → (⊢N : Γ ⊢ N ⦂ T)
       → (ℰ⟦ ⊢L ⟧ γ ＝ δ (ℰ⟦ ⊢L′ ⟧ γ))
       → ℰ⟦ ⊢?⁰ ⊢L ⊢M ⊢N ⟧ γ ＝ δ (ℰ⟦ ⊢?⁰ ⊢L′ ⊢M ⊢N ⟧ γ)
ifz-δ {γ} ⊢L ⊢L′ ⊢M ⊢N eq =
  (ℰ⟦ ⊢?⁰ ⊢L ⊢M ⊢N ⟧ γ)
    ＝⟨⟩
  ifz^ (ℰ⟦ ⊢M ⟧ γ) (ℰ⟦ ⊢N ⟧ γ) (ℰ⟦ ⊢L ⟧ γ)
    ＝⟨ ap (ifz^ (ℰ⟦ ⊢M ⟧ γ) (ℰ⟦ ⊢N ⟧ γ)) eq ⟩
  ifz^ (ℰ⟦ ⊢M ⟧ γ) (ℰ⟦ ⊢N ⟧ γ) (δ (ℰ⟦ ⊢L′ ⟧ γ))
    ＝⟨⟩
  θ (dfix (^-body (ifz (ℰ⟦ ⊢M ⟧ γ) (ℰ⟦ ⊢N ⟧ γ))) ⊛ next (ℰ⟦ ⊢L′ ⟧ γ))
    ＝⟨ ap (λ q → θ (q ⊛ next ((ℰ⟦ ⊢L′ ⟧ γ)))) (pfix (^-body (ifz (ℰ⟦ ⊢M ⟧ γ) (ℰ⟦ ⊢N ⟧ γ)))) ⟩
  θ (next (ifz^ (ℰ⟦ ⊢M ⟧ γ) (ℰ⟦ ⊢N ⟧ γ)) ⊛ next (ℰ⟦ ⊢L′ ⟧ γ))
    ＝⟨⟩
  (δ (ℰ⟦ ⊢?⁰ ⊢L′ ⊢M ⊢N ⟧ γ))
    ∎

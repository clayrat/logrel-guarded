module STLC1.Ext.Bigstep.Semantics where

open import Prelude
open import Data.Empty
open import Data.List

open import STLC1.Ext.Term
open import STLC1.Ext.Ty

infix 4 _∣_⇓_
infix 5 ⟨ƛ_⇒_⟩_

-- big-step / natural

private variable
  Γ : Ctx
  T : Ty

mutual
  -- Environments + domains
  data Env : 𝒰 where
    ∅ₑ : Env 
    _﹐_↦_ : Env → Id → Domain → Env
    
  -- Domain of evaluation
  data Domain : 𝒰 where
   ⟨𝓉𝓉⟩ : Domain
  -- Closures
   ⟨ƛ_⇒_⟩_ : Id → Term → Env → Domain 

{-
Domain-code : ∀ {T : Ty} → Domain T → Domain T → 𝒰
Domain-code  ⟨𝓉⟩                           ⟨𝓉⟩                    = ⊤
Domain-code  ⟨𝓉⟩                            ⟨𝒻⟩                   = ⊥
Domain-code  ⟨𝒻⟩                           ⟨𝓉⟩                    = ⊥
Domain-code  ⟨𝒻⟩                           ⟨𝒻⟩                   = ⊤
Domain-code (⟨ƛ_⟩_ {Γ = Γ₁} {S} {T} t₁ γ₁) (⟨ƛ_⟩_ {Γ = Γ₂} t₂ γ₂) =
  Σ[ Γe ꞉ Γ₁ ＝ Γ₂ ] (＜ t₁ ／ (λ i → Γe i ﹐ S ⊢ T) ＼ t₂ ＞ × ＜ γ₁ ／ (λ i → Env (Γe i)) ＼ γ₂ ＞)

Domain-code-refl : ∀ {T : Ty} → (d : Domain T) → Domain-code d d
Domain-code-refl {.𝟚}        ⟨𝓉⟩       = tt
Domain-code-refl {.𝟚}        ⟨𝒻⟩       = tt
Domain-code-refl {.(S ⇒ T)} (⟨ƛ_⟩_ {S} {T} t γ) = refl , refl , refl

Domain-encode : {T : Ty} {d1 d2 : Domain T} → d1 ＝ d2 → Domain-code d1 d2
Domain-encode {T} {d1} {d2} e = subst (Domain-code d1) e (Domain-code-refl d1)

⟨𝓉⟩≠⟨𝒻⟩ : ⟨𝓉⟩ ≠ ⟨𝒻⟩
⟨𝓉⟩≠⟨𝒻⟩ = Domain-encode

⟨ƛ⟩-inj : ∀ {Γ₁ Γ₂ S T} {t₁ : Γ₁ ﹐ S ⊢ T} {γ₁ : Env Γ₁}
                       {t₂ : Γ₂ ﹐ S ⊢ T} {γ₂ : Env Γ₂}
       → ⟨ƛ t₁ ⟩ γ₁ ＝ ⟨ƛ t₂ ⟩ γ₂
       → Σ[ Γe ꞉ Γ₁ ＝ Γ₂ ] (＜ t₁ ／ (λ i → Γe i ﹐ S ⊢ T) ＼ t₂ ＞ × ＜ γ₁ ／ (λ i → Env (Γe i)) ＼ γ₂ ＞)
⟨ƛ⟩-inj = Domain-encode
-}

-- lookup and context inclusion

data _∋_↦_ : Env → Id → Domain → 𝒰 where

  hereₑ : ∀ {γ x a}
      ------------------
       → (γ ﹐ x ↦ a) ∋ x ↦ a 

  thereₑ : ∀ {γ x y a b}
        → x ≠ y
        → γ ∋ x ↦ a
          ------------------
        → (γ ﹐ y ↦ b) ∋ x ↦ a

{-
-- Extending an environment
_＋＋_ : ∀ {Γ T}
      → Env Γ → Domain T → Env (Γ ﹐ T)
(_ ＋＋ a) T  here     = a
(γ ＋＋ _) T (there i) = γ T i
-}

-- Evaluation
data _∣_⇓_ : Env → Term → Domain → 𝒰 where
  ⇓𝓉𝓉 : ∀ {γ}
      → γ ∣ 𝓉𝓉 ⇓ ⟨𝓉𝓉⟩
  ⇓`  : ∀ {γ} {i} {a}
      → γ ∋ i ↦ a
      → γ ∣ ` i ⇓ a
  ⇓ƛ  : ∀ {γ} {x} {t}
      → γ ∣ (ƛ x ⇒ t) ⇓ (⟨ƛ x ⇒ t ⟩ γ)
  ⇓·  : ∀ {γ} {r s} {x} {δ} {t} {a b}
      → γ ∣ r ⇓ ⟨ƛ x ⇒ t ⟩ δ
      → γ ∣ s ⇓ a
      → δ ﹐ x ↦ a ∣ t ⇓ b
      → γ ∣ r · s ⇓ b

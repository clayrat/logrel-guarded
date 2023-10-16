module STLC2.Int.OpSem where

open import Prelude
open import Data.Empty
open import Data.List

open import STLC2.Int.TyTerm

-- big-step / natural

private variable
  Γ : Ctx
  T : Ty

infix 4 _∣_⇓_
infix 5 ⟨ƛ_⟩_
infix 6 _＋＋_

mutual
  -- Environments
  Env : Ctx → 𝒰
  Env Γ = ∀ T → Γ ∋ T → Domain T

  -- Domain of evaluation
  data Domain : Ty → 𝒰 where
  -- Booleans
   ⟨𝓉⟩ ⟨𝒻⟩ : Domain 𝟚
  -- Closures
   ⟨ƛ_⟩_ : ∀ {Γ S T}
        → Γ ﹐ S ⊢ T → Env Γ → Domain (S ⇒ T)

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

empty : Env ∅
empty T i = absurd (∅-empty i)

-- Extending an environment
_＋＋_ : ∀ {Γ T}
      → Env Γ → Domain T → Env (Γ ﹐ T)
(_ ＋＋ a) T  here     = a
(γ ＋＋ _) T (there i) = γ T i

-- Evaluation of terms
data _∣_⇓_ : Env Γ → Γ ⊢ T → Domain T → 𝒰 where
  ⇓𝓉  : ∀ {γ : Env Γ}
      → γ ∣ 𝓉 ⇓ ⟨𝓉⟩
  ⇓𝒻  : ∀ {γ : Env Γ}
      → γ ∣ 𝒻 ⇓ ⟨𝒻⟩
  ⇓`  : ∀ {T} {γ : Env Γ} {i : Γ ∋ T}
      → γ ∣ ` i ⇓ γ T i
  ⇓ƛ  : ∀ {γ : Env Γ} {A} {t : Γ ﹐ A ⊢ T}
      → γ ∣ ƛ t ⇓ ⟨ƛ t ⟩ γ
  ⇓·  : ∀ {γ : Env Γ} {A r s} {Δ} {δ : Env Δ} {t : Δ ﹐ A ⊢ T} {a b}
      → γ ∣ r ⇓ ⟨ƛ t ⟩ δ
      → γ ∣ s ⇓ a
      → δ ＋＋ a ∣ t ⇓ b
      → γ ∣ r · s ⇓ b
  ⇓⁇↑ : ∀ {γ : Env Γ} {r} {s : Γ ⊢ T} {t a}
      → γ ∣ r ⇓ ⟨𝓉⟩
      → γ ∣ s ⇓ a
      → γ ∣ ⁇ r ↑ s ↓ t ⇓ a
  ⇓⁇↓ : ∀ {γ : Env Γ} {r s} {t : Γ ⊢ T} {b}
      → γ ∣ r ⇓ ⟨𝒻⟩
      → γ ∣ t ⇓ b
      → γ ∣ ⁇ r ↑ s ↓ t ⇓ b

⇓-well-defined : ∅ ⊢ T → 𝒰
⇓-well-defined {T} t = Σ[ a ꞉ Domain T ] (empty ∣ t ⇓ a)

-- Natural semantics is deterministic
⇓-uniq : ∀ {Γ T} {γ : Env Γ} {t} {a b : Domain T}
       → γ ∣ t ⇓ a → γ ∣ t ⇓ b
       → a ＝ b
⇓-uniq  ⇓𝓉                                                               ⇓𝓉                                                  = refl
⇓-uniq  ⇓𝒻                                                               ⇓𝒻                                                 = refl
⇓-uniq  ⇓`                                                               ⇓`                                                  = refl
⇓-uniq  ⇓ƛ                                                               ⇓ƛ                                                  = refl
⇓-uniq {T} {b} (⇓· {A} {Δ = Δ₁} {δ = δ₁} {t = t₁} {a = d₁} r⇓₁ s⇓₁ t⇓₁) (⇓· {Δ = Δ₂} {δ = δ₂} {t = t₂} {a = d₂} r⇓₂ s⇓₂ t⇓₂) =
  let eΔ , et , eγ = ⟨ƛ⟩-inj $ ⇓-uniq r⇓₁ r⇓₂
      ed = ⇓-uniq s⇓₁ s⇓₂
    in ⇓-uniq t⇓₁ $
       subst (λ q → δ₁ ＋＋ q ∣ t₁ ⇓ b) (sym ed) $
       J (λ Δ′ e → (δ′ : Env Δ′) → (t′ : Δ′ ﹐ A ⊢ T)
                 → ＜ t₂ ／ (λ i → e i ﹐ A ⊢ T) ＼ t′ ＞
                 → ＜ δ₂ ／ (λ i → Env (e i)) ＼ δ′ ＞
                 → δ′ ＋＋ d₂ ∣ t′ ⇓ b)
         (λ δ′ t′ et′ eδ′ → subst (λ q → q ＋＋ d₂ ∣ t′ ⇓ b) eδ′ $
                            subst (λ q → δ₂ ＋＋ d₂ ∣ q ⇓ b) et′ t⇓₂)
         (sym eΔ) δ₁ t₁ (symP et) (symP eγ)
⇓-uniq (⇓⁇↑ r⇓₁ s⇓₁)                                                    (⇓⁇↑ r⇓₂ s⇓₂)                                        =
  ⇓-uniq s⇓₁ s⇓₂
⇓-uniq (⇓⁇↑ r⇓₁ s⇓₁)                                                    (⇓⁇↓ r⇓₂ t⇓₂)                                        =
  absurd (⟨𝓉⟩≠⟨𝒻⟩ (⇓-uniq r⇓₁ r⇓₂))
⇓-uniq (⇓⁇↓ r⇓₁ t⇓₁)                                                    (⇓⁇↑ r⇓₂ s⇓₂)                                        =
  absurd (⟨𝓉⟩≠⟨𝒻⟩ (sym $ ⇓-uniq r⇓₁ r⇓₂))
⇓-uniq (⇓⁇↓ r⇓₁ t⇓₁)                                                    (⇓⁇↓ r⇓₂ t⇓₂)                                        =
  ⇓-uniq t⇓₁ t⇓₂

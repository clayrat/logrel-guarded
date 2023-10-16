module STLC2.Int.Soundness where

open import Prelude
open import Data.Empty
open import Data.Bool
open import Data.Sum

open import Interlude
open import STLC2.Int.TyTerm
open import STLC2.Int.OpSem
open import STLC2.Int.Readback
open import STLC2.Int.DenSem
--open import STLC2.Int.Total

private variable
  Γ Δ : Ctx
  T : Ty

denote-＆-＋＋ : ∀ {Γ T S} {δ : Env Γ} {a : Domain T}
              → 𝒢⟦ δ ⟧ ＆ 𝒟⟦ a ⟧ ＝ 𝒢⟦ δ ＋＋ a ⟧ {S}
denote-＆-＋＋ {Γ} {T} {S} {δ} {a} = fun-ext go
  where
  go : (i : Γ ﹐ T ∋ S) → (𝒢⟦ δ ⟧ ＆ 𝒟⟦ a ⟧) i ＝ 𝒢⟦ δ ＋＋ a ⟧ i
  go  here     = refl
  go (there _) = refl

⇓-sound : ∀ {Γ T} {γ : Env Γ} {t} {a : Domain T}
        → γ ∣ t ⇓ a → ℰ⟦ t ⟧ 𝒢⟦ γ ⟧ ＝ 𝒟⟦ a ⟧
⇓-sound ⇓𝓉                                                = refl
⇓-sound ⇓𝒻                                                = refl
⇓-sound ⇓`                                                = refl
⇓-sound ⇓ƛ                                                = refl
⇓-sound (⇓· {γ} {A} {r} {s} {Δ} {δ} {t} {a} {b} r⇓ s⇓ t⇓) =
  ℰ⟦ r ⟧ 𝒢⟦ γ ⟧ (ℰ⟦ s ⟧ 𝒢⟦ γ ⟧)
    ＝⟨ ap (ℰ⟦ r ⟧ 𝒢⟦ γ ⟧) (⇓-sound s⇓) ⟩
  ℰ⟦ r ⟧ 𝒢⟦ γ ⟧ (𝒟⟦ a ⟧)
    ＝⟨ ap (λ q → q 𝒟⟦ a ⟧) (⇓-sound r⇓) ⟩
  ℰ⟦ t ⟧ (𝒢⟦ δ ⟧ ＆ 𝒟⟦ a ⟧)
    ＝⟨ ap ℰ⟦ t ⟧ (fun-ext-implicit λ {a = S} → denote-＆-＋＋ {Δ} {A} {S} {δ} {a}) ⟩
  ℰ⟦ t ⟧ (𝒢⟦ δ ＋＋ a ⟧)
    ＝⟨ ⇓-sound t⇓ ⟩
  𝒟⟦ b ⟧
    ∎
⇓-sound (⇓⁇↑ {γ} {s} {t} r⇓ s⇓)                           =
    ap (λ q → (if q then ℰ⟦ s ⟧ 𝒢⟦ γ ⟧ else ℰ⟦ t ⟧ 𝒢⟦ γ ⟧)) (⇓-sound r⇓)
  ∙ ⇓-sound s⇓
⇓-sound (⇓⁇↓ {γ} {s} {t} r⇓ t⇓)                           =
    ap (λ q → (if q then ℰ⟦ s ⟧ 𝒢⟦ γ ⟧ else ℰ⟦ t ⟧ 𝒢⟦ γ ⟧)) (⇓-sound r⇓)
  ∙ ⇓-sound t⇓

-- Evaluation of a term injected to an extended context
-- is equivalent
-- TODO fix ?
{-# TERMINATING #-}
ℰ-inject : (t : Γ ⊢ T) (p : 𝒞⟦ Γ ⟧) (q : 𝒞⟦ Δ ⟧)
         → ℰ⟦ t ⟧ p ＝ ℰ⟦ inject t ⟧ (q ＆＆ p)
ℰ-inject (` here)      p q = refl
ℰ-inject (` there i)   p q = ℰ-inject (` i) (p ∘ there) q
ℰ-inject (ƛ t)         p q = fun-ext λ ta → ℰ-inject t (p ＆ ta) q
ℰ-inject (r · s)       p q =
   -- this is problematic
   ap (ℰ⟦ r ⟧ p) (ℰ-inject s p q)
   ∙ happly (ℰ-inject r p q) (ℰ⟦ inject s ⟧ (q ＆＆ p))
ℰ-inject  𝓉            p q = refl
ℰ-inject  𝒻            p q = refl
ℰ-inject (⁇ r ↑ s ↓ t) p q with (ℰ-inject r p q)
...                        | e with ℰ⟦ r ⟧ p
...                            | true  with ℰ⟦ inject r ⟧ (q ＆＆ p)
...                                    | true  = ℰ-inject s p q
...                                    | false = absurd (true≠false e)
ℰ-inject (⁇ r ↑ s ↓ t) p q | e | false with ℰ⟦ inject r ⟧ (q ＆＆ p)
...                                    | true  = absurd (true≠false (sym e))
...                                    | false = ℰ-inject t p q


-- Splitting variable into left context
split-left : ∀ {x : Γ ◇ Δ ∋ T} {y : Γ ∋ T} {p : 𝒞⟦ Γ ⟧} {q : 𝒞⟦ Δ ⟧}
           → split x ＝ inl y
           → (p ＆＆ q) x ＝ p y
split-left {Δ = ∅}     {x} {p}           e = ap p (inl-inj e)
split-left {Δ = Δ ﹐ S} {x = here}        e = absurd (⊎-disjoint (sym e))
split-left {Δ = Δ ﹐ S} {x = there i} {y} e with inspect (split {Δ = Δ} i)
... | inl x , ee =
  let e′ = inl-inj $ subst (λ q → [ inl , inr ∘ there ]ᵤ q ＝ inl y) ee e in
  split-left (ee ∙ ap inl e′)
... | inr x , ee =
  let e′ = subst (λ q → [ inl , inr ∘ there ]ᵤ q ＝ inl y) ee e in
  absurd (⊎-disjoint (sym e′))

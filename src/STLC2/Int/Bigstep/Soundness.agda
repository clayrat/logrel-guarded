module STLC2.Int.Bigstep.Soundness where

open import Prelude
open import Data.Empty
open import Data.Bool
open import Data.Sum

open import Interlude
open import STLC2.Int.TyTerm
open import STLC2.Int.Bigstep.OpSem
open import STLC2.Int.Bigstep.Norm
open import STLC2.Int.Bigstep.DenSem

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
{-# TERMINATING #-}  -- TODO something is fishy
ℰ-inject : (t : Γ ⊢ T) (p : 𝒞⟦ Γ ⟧) (q : 𝒞⟦ Δ ⟧)
         → ℰ⟦ t ⟧ p ＝ ℰ⟦ inject t ⟧ (q ＆＆ p)
ℰ-inject (` here)      p q = refl
ℰ-inject (` there i)   p q = ℰ-inject (` i) (p ∘ there) q
ℰ-inject (ƛ t)         p q = fun-ext λ ta → ℰ-inject t (p ＆ ta) q
ℰ-inject (r · s)       p q =
  subst (λ z → ℰ⟦ r ⟧ p (ℰ⟦ s ⟧ p) ＝ z (ℰ⟦ inject s ⟧ (q ＆＆ p))) (ℰ-inject r p q) $
  subst (λ z → ℰ⟦ r ⟧ p (ℰ⟦ s ⟧ p) ＝ (ℰ⟦ r ⟧ p) z) (ℰ-inject s p q) $
  refl
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

-- Splitting variable into right context
split-right : ∀ {x : Γ ◇ Δ ∋ T} {y : Δ ∋ T} {p : 𝒞⟦ Γ ⟧} {q : 𝒞⟦ Δ ⟧}
            → split x ＝ inr y
            → (p ＆＆ q) x ＝ q y
split-right {Δ = Δ ﹐ S} {x = here} {q}    e = ap q (inr-inj e)
split-right {Δ = Δ ﹐ S} {x = there i} {y} {q} e with inspect (split {Δ = Δ} i)
... | inl x , ee =
  let e′ = subst (λ q → [ inl , inr ∘ there ]ᵤ q ＝ inr y) ee e in
  absurd (⊎-disjoint e′)
... | inr x , ee =
  let e′ = inr-inj $ subst (λ q → [ inl , inr ∘ there ]ᵤ q ＝ inr y) ee e in
  split-right ee ∙ ap q e′

mutual
-- Evaluation of a term is equivalent to evaluation
-- of its closed self
  ℰ-close : ∀ (t : Γ ◇ Δ ⊢ T) (γ : Env Γ) (q : 𝒞⟦ Δ ⟧)
          → ℰ⟦ t ⟧ (𝒢⟦ γ ⟧ ＆＆ q) ＝ ℰ⟦ close γ t ⟧ q
  ℰ-close {Δ} {T} (` i)         γ q with inspect (split {Δ = Δ} i)
  ... | inl x , ee = split-left {p = 𝒢⟦ γ ⟧} {q = q} ee
                   ∙ ⇑-sound {ρ = λ e → absurd (∅-empty e)} (γ T x)
                   ∙ ℰ-inject (γ T x ⇑) (λ e → absurd (∅-empty e)) q
                   ∙ sym (ap (λ z → ℰ⟦ [ (λ j → inject (γ T j ⇑)) , `_ ]ᵤ z ⟧ q) ee)
  ... | inr x , ee = split-right {p = 𝒢⟦ γ ⟧} ee
                   ∙ sym (ap (λ z → ℰ⟦ [ (λ j → inject (γ T j ⇑)) , `_ ]ᵤ z ⟧ q) ee)
  ℰ-close     (ƛ t)         γ q = fun-ext λ ta → ℰ-close t γ (q ＆ ta)
  ℰ-close     (r · s)       γ q =
    subst (λ z → z (ℰ⟦ s ⟧ (𝒢⟦ γ ⟧ ＆＆ q)) ＝ ℰ⟦ close γ r ⟧ q (ℰ⟦ close γ s ⟧ q)) (sym $ ℰ-close r γ q) $
    subst (λ z → (ℰ⟦ close γ r ⟧ q) z ＝ ℰ⟦ close γ r ⟧ q (ℰ⟦ close γ s ⟧ q)) (sym $ ℰ-close s γ q) $
    refl
  ℰ-close      𝓉            γ q = refl
  ℰ-close      𝒻            γ q = refl
  ℰ-close     (⁇ r ↑ s ↓ t) γ q with (ℰ-close r γ q)
  ...                           | e with ℰ⟦ r ⟧ (𝒢⟦ γ ⟧ ＆＆ q)
  ...                               | true  with ℰ⟦ close γ r ⟧ q
  ...                                       | true  = ℰ-close s γ q
  ...                                       | false = absurd (true≠false e)
  ℰ-close     (⁇ r ↑ s ↓ t) γ q | e | false with ℰ⟦ close γ r ⟧ q
  ...                                       | true  = absurd (true≠false (sym e))
  ...                                       | false = ℰ-close t γ q

-- Reading back a normal form from an evaluated term
-- preserves meaning
  ⇑-sound : ∀ {ρ : 𝒞⟦ ∅ ⟧} (a : Domain T)
          → 𝒟⟦ a ⟧ ＝ ℰ⟦ a ⇑ ⟧ ρ
  ⇑-sound {ρ} ⟨𝓉⟩        = refl
  ⇑-sound {ρ} ⟨𝒻⟩       = refl
  ⇑-sound {ρ} (⟨ƛ t ⟩ γ) = fun-ext λ ta → ℰ-close t γ (ρ ＆ ta)

-- Use the fact that reading back a normal form is sound
-- w.r.t. denotational semantics to prove normalization
-- is sound
normalization-sound : (t v : ∅ ⊢ T)
                    → t normalizes-to v
                    → t ℰ≡ v
normalization-sound t v (v′ , t⇓ , ev) {ρ} =
  let _ , _ , t⇓′ , _ = normalization t in
   ℰ⟦ t ⟧ ρ
     ＝⟨ ap (ℰ⟦ t ⟧) (fun-ext-implicit λ {S} → fun-ext λ i → absurd (∅-empty i)) ⟩
   ℰ⟦ t ⟧ 𝒢⟦ empty ⟧
     ＝⟨ ⇓-sound t⇓ ⟩
   𝒟⟦ v′ ⟧
     ＝⟨ ⇑-sound v′ ⟩
   ℰ⟦ v′ ⇑ ⟧ ρ
     ＝⟨ ap (λ q → ℰ⟦ q ⟧ ρ) ev ⟩
   ℰ⟦ v ⟧ ρ
     ∎

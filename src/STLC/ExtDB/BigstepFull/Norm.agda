module STLC.ExtDB.BigstepFull.Norm where

open import Prelude
open import Data.Empty
open import Data.Nat hiding (_·_ ; _^_)
open import Data.List

open import Interlude
open import STLC.ExtDB.Term
open import STLC.ExtDB.Ty
open import STLC.ExtDB.BigstepFull.OpSem
open import STLC.ExtDB.BigstepFull.Readback
open import STLC.ExtDB.BigstepFull.Logrel

-- Normalization of STLC

idx→lvl : ℕ → ℕ → ℕ
idx→lvl i n = n ∸ suc i

env : ℕ → Env
env n i = ⟨ lvl (idx→lvl i n) ⟩ⁿᵉ

_has-normal-form<_>_ : Term → ℕ → Term → 𝒰
t has-normal-form< n > v = Σ[ a ꞉ Domain ] (env n ∣ t ⇓ a) × (n ∣ a ⇑ v)

∥_∥ : Ctx → ℕ
∥ ∅ ∥      = zero
∥ Γ ﹐ _ ∥ = suc ∥ Γ ∥

⊨env∥_∥ : ∀ Γ → Γ ⊨ env ∥ Γ ∥
⊨env∥_∥ Γ {x} {T} _ = 𝔹⊆⟦ T ⟧ (lvl∈𝔹 (idx→lvl x ∥ Γ ∥))

normalization : ∀ {Γ t T}
              → Γ ⊢ t ⦂ T → Σ[ v ꞉ Term ] (t has-normal-form< ∥ Γ ∥ > v)
normalization {Γ} {T} ⊢t =
  let a , t⇓a , st = fundamental-lemma ⊢t ⊨env∥ Γ ∥
      v , a⇑v = ⟦ T ⟧⊆𝕋 st ∥ Γ ∥
    in
  v , a , t⇓a , a⇑v

-- Normal and neutral terms
mutual
  data Normal : Term → 𝒰 where
    normƛ : ∀ {t}
          → Normal t → Normal (ƛ t)
    neu   : ∀ {t}
          → Neutral t → Normal t

  data Neutral : Term → 𝒰 where
    neu` : ∀ {x}
         → Neutral (` x)
    neu· : ∀ {r s}
         → Neutral r → Normal s → Neutral (r · s)

-- Read back produces a normal term
mutual
  ⇑-normal : ∀ {n a v}
           → n ∣ a ⇑ v → Normal v
  ⇑-normal (⇑⟨ƛ⟩ _ a⇑v) = normƛ (⇑-normal a⇑v)
  ⇑-normal (⇑ne e⇑u)   = neu (⇑ⁿᵉ-neutral e⇑u)

  ⇑ⁿᵉ-neutral : ∀ {n e u}
              → n ∣ e ⇑ⁿᵉ u → Neutral u
  ⇑ⁿᵉ-neutral  ⇑lvl          = neu`
  ⇑ⁿᵉ-neutral (⇑app e⇑u d⇑v) = neu· (⇑ⁿᵉ-neutral e⇑u) (⇑-normal d⇑v)

-- Normal form is truly a normal term
nf-normal : ∀ {t n v}
          → t has-normal-form< n > v → Normal v
nf-normal (_ , _ , ⇑v) = ⇑-normal ⇑v

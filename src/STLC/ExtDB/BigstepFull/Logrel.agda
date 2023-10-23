module STLC.ExtDB.BigstepFull.Logrel where

open import Prelude
open import Data.Empty
open import Data.Nat hiding (_·_ ; _^_)

open import Interlude
open import STLC.ExtDB.Term
open import STLC.ExtDB.Ty
open import STLC.ExtDB.BigstepFull.OpSem
open import STLC.ExtDB.BigstepFull.Readback

LogPred : 𝒰 (ℓsuc 0ℓ)
LogPred = Domain → 𝒰

-- Bottom of candidate space
-- (neutral term can be read back)
𝔹 : LogPred
𝔹 ⟨ e ⟩ⁿᵉ    = ∀ n → Σ[ u ꞉ Term ] (n ∣ e ⇑ⁿᵉ u)
𝔹 (⟨ƛ _ ⟩ _) = ⊥

-- Top of candidate space
-- (normal term can be read back)
𝕋 : LogPred
𝕋 d = ∀ n → Σ[ u ꞉ Term ] (n ∣ d ⇑ u)

-- Bottom of space is a subset of top
𝔹⊆𝕋 : ∀ d → d ∈ₚ 𝔹 → d ∈ₚ 𝕋
--𝔹⊆𝕋 ⟨𝓉𝓉⟩     _  n = 𝓉𝓉 , ⇑⟨𝓉𝓉⟩
𝔹⊆𝕋 ⟨ dn ⟩ⁿᵉ eb n =
  let u , e⇑u = eb n in
  u , ⇑ne e⇑u

-- Semantic function space
_−→_ : LogPred → LogPred → LogPred
(A −→ B) f = ∀ {a} → a ∈ₚ A → Σ[ b ꞉ Domain ] (f · a ⇓ b) × (b ∈ₚ B)

-- Semantic types (logical relation)
⟦_⟧ : Ty → LogPred
⟦ 𝟙 ⟧     = 𝔹
⟦ S ⇒ T ⟧ = ⟦ S ⟧ −→ ⟦ T ⟧

_⊨_ : Ctx → Env → 𝒰
Γ ⊨ γ = ∀ {x} {T} → Γ ∋ x ⦂ T → γ x ∈ₚ ⟦ T ⟧

_⊨_⦂_ : Ctx → Term → Ty → 𝒰
Γ ⊨ t ⦂ T = ∀ {γ} → Γ ⊨ γ → Σ[ a ꞉ Domain ] (γ ∣ t ⇓ a) × (a ∈ₚ ⟦ T ⟧)

_^_ : ∀ {Γ γ a S}
    → Γ ⊨ γ → a ∈ₚ ⟦ S ⟧ → (Γ ﹐ S) ⊨ (γ ＋＋ a)
(⊨γ ^ sa)  here     = sa
(⊨γ ^ sa) (there i) = ⊨γ i

fundamental-lemma : ∀ {Γ t T}
                  → Γ ⊢ t ⦂ T → Γ ⊨ t ⦂ T
fundamental-lemma              (⊢` {x} i)      {γ} ⊨γ =
  γ x , ⇓` , ⊨γ i
fundamental-lemma {t = .(ƛ t)} (⊢ƛ {N = t} ⊢t) {γ} ⊨γ =
  (⟨ƛ t ⟩ γ) , ⇓ƛ , λ sa →
    let b , ec , sb = fundamental-lemma ⊢t (⊨γ ^ sa) in
    b , ·⇓ƛ ec , sb
fundamental-lemma              (⊢r ⊢· ⊢s)         ⊨γ =
  let f , r⇓ , sf = fundamental-lemma ⊢r ⊨γ
      a , s⇓ , sa = fundamental-lemma ⊢s ⊨γ
      b , ae , sb = sf sa
    in
  b , ⇓· r⇓ s⇓ ae , sb

-- First property of candidate space
𝔹⊆𝕋−→𝔹 : ∀ {d}
         → d ∈ₚ 𝔹 → d ∈ₚ (𝕋 −→ 𝔹)
𝔹⊆𝕋−→𝔹 {⟨ e ⟩ⁿᵉ} eb {a} at =
  ⟨ e ·ⁿᵉ a ⟩ⁿᵉ , ·⇓ⁿᵉ , λ n →
   let u , e⇑u = eb n
       v , d⇑v = at n
     in
   u · v , ⇑app e⇑u d⇑v

-- Any de Bruijn level can be read back
-- to its corresponding de Bruijn index
lvl∈𝔹 : ∀ k → ⟨ lvl k ⟩ⁿᵉ ∈ₚ 𝔹
lvl∈𝔹 k n = (` (lvl→idx k n)) , ⇑lvl

-- Second property of candidate space
𝔹−→𝕋⊆𝕋 : ∀ {d} → d ∈ₚ (𝔹 −→ 𝕋) → d ∈ₚ 𝕋
𝔹−→𝕋⊆𝕋 {⟨ƛ t ⟩ γ} dbt n with dbt (lvl∈𝔹 n)
... | a , ·⇓ƛ ec , dt = let v , d⇑v = dt n in
                        ƛ v , ⇑⟨ƛ⟩ ec d⇑v
𝔹−→𝕋⊆𝕋 {⟨ ne ⟩ⁿᵉ} dbt n with dbt (lvl∈𝔹 n)
... | .(⟨ ne ·ⁿᵉ ⟨ lvl n ⟩ⁿᵉ ⟩ⁿᵉ) , ·⇓ⁿᵉ , et with et n
... | .(u · _) , ⇑ne (⇑app {u} e⇑u _) = u , (⇑ne e⇑u)

mutual
  𝕋−→𝔹⊆⟦_⇒_⟧ : ∀ S T {f} → f ∈ₚ (𝕋 −→ 𝔹) → f ∈ₚ ⟦ S ⇒ T ⟧
  𝕋−→𝔹⊆⟦ S ⇒ T ⟧ tbf sa =
    let d , ev , eb = tbf (⟦ S ⟧⊆𝕋 sa) in
    d , ev , 𝔹⊆⟦ T ⟧ eb

  ⟦_⇒_⟧⊆𝔹−→𝕋 : ∀ S T {f} → f ∈ₚ ⟦ S ⇒ T ⟧ → f ∈ₚ (𝔹 −→ 𝕋)
  ⟦ S ⇒ T ⟧⊆𝔹−→𝕋 stf ab =
    let d , ev , sd = stf (𝔹⊆⟦ S ⟧ ab) in
    d , ev , ⟦ T ⟧⊆𝕋 sd

  -- Any object that can have a neutral form read back
  -- is semantically typed
--  𝔹⊆⟦_⟧ : ∀ T {e} → ⟨ e ⟩ⁿᵉ ∈ₚ 𝔹 → ⟨ e ⟩ⁿᵉ ∈ₚ ⟦ T ⟧
  𝔹⊆⟦_⟧ : ∀ T {d} → d ∈ₚ 𝔹 → d ∈ₚ ⟦ T ⟧
  𝔹⊆⟦ 𝟙 ⟧     eb = eb
  𝔹⊆⟦ S ⇒ T ⟧    = 𝕋−→𝔹⊆⟦ S ⇒ T ⟧ ∘ 𝔹⊆𝕋−→𝔹

  -- Semantic typing implies a normal form can be read
  -- back
  ⟦_⟧⊆𝕋 : ∀ T {d} → d ∈ₚ ⟦ T ⟧ → d ∈ₚ 𝕋
  ⟦ 𝟙 ⟧⊆𝕋     {d} = 𝔹⊆𝕋 d
  ⟦ S ⇒ T ⟧⊆𝕋     = 𝔹−→𝕋⊆𝕋 ∘ ⟦ S ⇒ T ⟧⊆𝔹−→𝕋

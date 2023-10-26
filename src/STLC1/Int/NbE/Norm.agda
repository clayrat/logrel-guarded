module STLC1.Int.NbE.Norm where

open import Prelude hiding ([_])
open import Data.Empty
open import Data.Dec
open import Data.Maybe

open import STLC1.Int.TyTerm
open import STLC1.Int.NbE.CtxExt
open import STLC1.Int.NbE.Subst

mutual
  -- Normal terms
  data Nf : (T : Ty) → (Γ : Ctx) → Γ ⊢ T → 𝒰 where
    nf-𝓉𝓉 : ∀ {Γ : Ctx}
            → Nf 𝟙 Γ 𝓉𝓉

    nf-ƛ : ∀ {S T : Ty} {Γ : Ctx} {𝓋 : Γ ﹐ S ⊢ T}
           → Nf T (Γ ﹐ S) 𝓋
             ------------------
           → Nf (S ⇒ T) Γ (ƛ 𝓋)

    nf-ne : ∀ {T : Ty} {Γ : Ctx} {𝓊 : Γ ⊢ T}
          → Ne T Γ 𝓊
            --------
          → Nf T Γ 𝓊

  -- Neutral terms
  data Ne (T : Ty) (Γ : Ctx) : Γ ⊢ T → 𝒰 where
    ne-` : (x : Γ ∋ T)
           ------------
         → Ne T Γ (` x)

    ne-· : ∀ {S : Ty} {𝓊 : Γ ⊢ S ⇒ T} {𝓋 : Γ ⊢ S}
         → Ne (S ⇒ T) Γ 𝓊
         → Nf S Γ 𝓋
           --------------
         → Ne T Γ (𝓊 · 𝓋)

-- Liftable neutral term
Ne^ : Ty → 𝒰
Ne^ T = ∀ (Γ : Ctx) → Maybe (Σ[ t ꞉ Γ ⊢ T ] Ne T Γ t)

-- Liftable normal term
Nf^ : Ty → 𝒰
Nf^ T = ∀ (Γ : Ctx) → Σ[ t ꞉ Γ ⊢ T ] Nf T Γ t

_·^_ : ∀ {S T : Ty} → Ne^ (S ⇒ T) → Nf^ S → Ne^ T
(𝓊̂ ·^ 𝓋̂) Γ with 𝓊̂ Γ
... | just (𝓊 , pf𝓊) = let 𝓋 , pf𝓋 = 𝓋̂ Γ in
                        just (𝓊 · 𝓋 , ne-· pf𝓊 pf𝓋)
... | nothing = nothing

data ⊤̂ : 𝒰 where
  unit : ⊤̂
  ne   : Ne^ 𝟙 → ⊤̂

⟦_⟧ᵗ : Ty → 𝒰
⟦ 𝟙 ⟧ᵗ = ⊤̂
⟦ S ⇒ T ⟧ᵗ = ⟦ S ⟧ᵗ → ⟦ T ⟧ᵗ

⟦_⟧ᶜ : Ctx → 𝒰
⟦ ∅ ⟧ᶜ     = ⊤
⟦ Γ ﹐ T ⟧ᶜ = ⟦ Γ ⟧ᶜ × ⟦ T ⟧ᵗ

env-lookup : ∀ {Γ : Ctx} {T : Ty} → Γ ∋ T → ⟦ Γ ⟧ᶜ → ⟦ T ⟧ᵗ
env-lookup  here     (_ , a) = a
env-lookup (there x) (γ , _) = env-lookup x γ

⟦⊢_⟧ : ∀ {Γ : Ctx} {T : Ty} → Γ ⊢ T → ⟦ Γ ⟧ᶜ → ⟦ T ⟧ᵗ
⟦⊢ 𝓉𝓉    ⟧ _   = unit
⟦⊢ ` x   ⟧ γ   = env-lookup x γ
⟦⊢ ƛ t   ⟧ γ a = ⟦⊢ t ⟧ (γ , a)
⟦⊢ r · s ⟧ γ   = ⟦⊢ r ⟧ γ (⟦⊢ s ⟧ γ)

↓⊤̂ : ⟦ 𝟙 ⟧ᵗ → Nf^ 𝟙
↓⊤̂  unit   _ = 𝓉𝓉 , nf-𝓉𝓉
↓⊤̂ (ne 𝓊̂) Γ with 𝓊̂ Γ
... | just (𝓊 , pf) = 𝓊 , nf-ne pf
... | nothing        = 𝓉𝓉 , nf-𝓉𝓉

𝓍̂ : (S : Ty) → Ctx → Ne^ S
𝓍̂ S Γ Γ′ with Γ′ ≤? (Γ ﹐ S)
...  | no _   = nothing
...  | yes pf = let x = ρ-≤ pf here in
                just (` x , ne-` x)

mutual
  ↑ᵀ : {T : Ty} → Ne^ T → ⟦ T ⟧ᵗ
  ↑ᵀ {T = 𝟙}     𝓊̂   = ne 𝓊̂
  ↑ᵀ {T = S ⇒ T} 𝓊̂ a = ↑ᵀ (𝓊̂ ·^ (↓ᵀ a))

  ↓ᵀ : {T : Ty} → ⟦ T ⟧ᵗ → Nf^ T
  ↓ᵀ {T = 𝟙}         = ↓⊤̂
  ↓ᵀ {T = S ⇒ T} f Γ =
    let (𝓋 , pf) = ↓ᵀ (f (↑ᵀ (𝓍̂ S Γ))) (Γ ﹐ S) in
    ƛ 𝓋 , nf-ƛ pf

↑ᶜ : ∀ (Γ : Ctx) → ⟦ Γ ⟧ᶜ
↑ᶜ  ∅      = tt
↑ᶜ (Γ ﹐ T) = ↑ᶜ Γ  , ↑ᵀ (𝓍̂ T Γ)

nbe : ∀ {Γ : Ctx} {T : Ty}
    → Γ ⊢ T → Σ[ t ꞉ Γ ⊢ T ] Nf T Γ t
nbe {Γ} t = ↓ᵀ (⟦⊢ t ⟧ (↑ᶜ Γ)) Γ

nf : ∀ {Γ : Ctx} {T : Ty} → Γ ⊢ T → Γ ⊢ T
nf t = nbe t .fst

module AlgorithmExample where
  -- (λx. (λy. y) x) 𝓉𝓉
  ex : ∅ ⊢ 𝟙
  ex = (ƛ (ƛ ` here) · ` here) · 𝓉𝓉

  -- normal form is unit
  nf-ex : nf ex ＝ 𝓉𝓉
  nf-ex = refl

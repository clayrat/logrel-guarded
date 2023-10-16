module STLC2.Int.Readback where

open import Prelude
open import Data.Sum

open import Interlude
open import STLC2.Int.TyTerm
open import STLC2.Int.OpSem

private variable
  Γ Δ : Ctx
  T : Ty

-- Context append
_◇_ : Ctx → Ctx → Ctx
Δ ◇ ∅       = Δ
Δ ◇ (Γ ﹐ S) = Δ ◇ Γ ﹐ S

-- Inject de Brujin index into larger context
inject-var : Γ ∋ T → Δ ◇ Γ ∋ T
inject-var  here     = here
inject-var (there x) = there (inject-var x)

-- Inject term into larger context (similar to weakening)
inject : Γ ⊢ T → Δ ◇ Γ ⊢ T
inject (` i)         = ` inject-var i
inject (ƛ t)         = ƛ inject t
inject (r · s)       = inject r · inject s
inject 𝓉             = 𝓉
inject 𝒻             = 𝒻
inject (⁇ r ↑ s ↓ t) = ⁇ inject r ↑ inject s ↓ inject t

-- If we have a variable in a injected context
-- we can determine where it came from
split : Γ ◇ Δ ∋ T → (Γ ∋ T) ⊎ (Δ ∋ T)
split {Δ = ∅}      i        = inl i
split {Δ = Δ ﹐ _}  here     = inr here
split {Δ = Δ ﹐ _} (there i) = [ inl , inr ∘ there ]ᵤ (split {Δ = Δ} i)

-- Reading back a normal form from the evaluation of
-- a term. We truly "close" a closure in reading it
-- back to a normal form by replacing every variable
-- in its context using its environment
mutual
  _⇑ : Domain T → ∅ ⊢ T
  ⟨𝓉⟩ ⇑        = 𝓉
  ⟨𝒻⟩ ⇑        = 𝒻
  (⟨ƛ t ⟩ γ) ⇑ = ƛ (close γ t)
-- Note that this operation is essentially a
-- substitution
  close : Env Γ → Γ ◇ Δ ⊢ T → Δ ⊢ T
  close {Γ} {T} γ (` i)         with split {Γ} i
  ...                           | inl j with γ T j ⇑
  ...                                   | t = inject t
  close         γ (` i)         | inr k = ` k
  close         γ (ƛ t)         = ƛ close γ t
  close         γ (r · s)       = close γ r · close γ s
  close         γ  𝓉            = 𝓉
  close         γ  𝒻            = 𝒻
  close         γ (⁇ r ↑ s ↓ t) = ⁇ close γ r ↑ close γ s ↓ close γ t

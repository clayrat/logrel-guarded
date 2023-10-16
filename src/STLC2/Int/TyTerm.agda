module STLC2.Int.TyTerm where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.List
open import Structures.IdentitySystem

infix  4  _∋_
infix  4  _⊢_
infixl 5 _﹐_
infixr 7 _⇒_
infix  5 ƛ_
infix  5 ⁇_↑_↓_
infixl 7 _·_
infix  9 `_

-- types

data Ty : 𝒰 where
  𝟚   : Ty
  _⇒_ : Ty → Ty → Ty

module Ty-path-code where

  Ty-code : Ty → Ty → 𝒰
  Ty-code  𝟚         𝟚        = ⊤
  Ty-code  𝟚        (_ ⇒ _)   = ⊥
  Ty-code (_ ⇒ _)    𝟚        = ⊥
  Ty-code (S₁ ⇒ T₁) (S₂ ⇒ T₂) = Ty-code S₁ S₂ × Ty-code T₁ T₂

  Ty-code-refl : (t : Ty) → Ty-code t t
  Ty-code-refl  𝟚      = tt
  Ty-code-refl (S ⇒ T) = Ty-code-refl S , Ty-code-refl T

  Ty-decode : ∀ {t₁ t₂} → Ty-code t₁ t₂ → t₁ ＝ t₂
  Ty-decode {t₁ = 𝟚}  {t₂ = 𝟚}   _        = refl
  Ty-decode {S₁ ⇒ T₁} {S₂ ⇒ T₂} (eS , eT) = ap² _⇒_ (Ty-decode eS) (Ty-decode eT)

  Ty-code-prop : ∀ t₁ t₂ → is-prop (Ty-code t₁ t₂)
  Ty-code-prop  𝟚         𝟚        = hlevel!
  Ty-code-prop  𝟚        (_ ⇒ _)   = hlevel!
  Ty-code-prop (_ ⇒ _)    𝟚        = hlevel!
  Ty-code-prop (S₁ ⇒ T₁) (S₂ ⇒ T₂) = ×-is-of-hlevel 1 (Ty-code-prop S₁ S₂) (Ty-code-prop T₁ T₂)

  Ty-identity-system : is-identity-system Ty-code Ty-code-refl
  Ty-identity-system = set-identity-system Ty-code-prop Ty-decode

Ty-is-set : is-set Ty
Ty-is-set = identity-system→is-of-hlevel 1 Ty-path-code.Ty-identity-system Ty-path-code.Ty-code-prop

-- contexts

data Ctx : 𝒰 where
  ∅   : Ctx
  _﹐_ : Ctx → Ty → Ctx

Ctx-≃ : Iso Ctx (List Ty)
Ctx-≃ = ff , iso gg ri li
  where
  ff : Ctx → List Ty
  ff ∅       = []
  ff (c ﹐ i) = i ∷ ff c
  gg : List Ty → Ctx
  gg []      = ∅
  gg (t ∷ l) = gg l ﹐ t
  ri : gg is-right-inverse-of ff
  ri []            = refl
  ri (t ∷ l) = ap (t ∷_) (ri l)
  li : gg is-left-inverse-of ff
  li ∅          = refl
  li (c ﹐ t) = ap (_﹐ t) (li c)

Ctx-is-set : is-set Ctx
Ctx-is-set = iso→is-of-hlevel 2 Ctx-≃ (list-is-of-hlevel 0 Ty-is-set)

-- de Brujin indices

data _∋_ : Ctx → Ty → 𝒰 where

  here : ∀ {Γ A}
      ------------------
       → Γ ﹐ A ∋ A

  there : ∀ {Γ A B}
        → Γ ∋ A
          ------------------
        → Γ ﹐ B ∋ A

∅-empty : ∀ {A} → ¬ (∅ ∋ A)
∅-empty ()

-- typed terms

data _⊢_ : Ctx → Ty → 𝒰 where

  -- Axiom
  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----------
    → Γ ⊢ A

  -- ⇒-I
  ƛ_ : ∀ {Γ A B}
    → Γ ﹐ A ⊢ B
      -------------------
    → Γ ⊢ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      -------------
    → Γ ⊢ B

  -- true
  𝓉 : ∀ {Γ}
      ----------
    → Γ ⊢ 𝟚

  -- false
  𝒻 : ∀ {Γ}
      ----------
    → Γ ⊢ 𝟚

  -- if-then-else
  ⁇_↑_↓_ : ∀ {Γ A}
    → Γ ⊢ 𝟚
    → Γ ⊢ A
    → Γ ⊢ A
      -------------------
    → Γ ⊢ A

-- Context append
_◇_ : Ctx → Ctx → Ctx
Δ ◇ ∅       = Δ
Δ ◇ (Γ ﹐ S) = Δ ◇ Γ ﹐ S

-- Inject de Brujin index into larger context
inject-var : ∀ {Γ Δ T}
           → Γ ∋ T → Δ ◇ Γ ∋ T
inject-var  here     = here
inject-var (there x) = there (inject-var x)

-- Inject term into larger context (similar to weakening)
inject : ∀ {Γ Δ T}
       → Γ ⊢ T → Δ ◇ Γ ⊢ T
inject (` i)         = ` inject-var i
inject (ƛ t)         = ƛ inject t
inject (r · s)       = inject r · inject s
inject 𝓉             = 𝓉
inject 𝒻             = 𝒻
inject (⁇ r ↑ s ↓ t) = ⁇ inject r ↑ inject s ↓ inject t

-- If we have a variable in a injected context
-- we can determine where it came from
split : ∀ {Γ Δ T}
      → Γ ◇ Δ ∋ T → (Γ ∋ T) ⊎ (Δ ∋ T)
split {Δ = ∅}      i        = inl i
split {Δ = Δ ﹐ _}  here     = inr here
split {Δ = Δ ﹐ _} (there i) = [ inl , inr ∘ there ]ᵤ (split {Δ = Δ} i)

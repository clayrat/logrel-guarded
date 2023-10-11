module STLC2.Int.TyTerm where

open import Prelude
open import Data.Empty
open import Data.List

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

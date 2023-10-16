module STLC.DBFull.Ty where

open import Prelude
open import Data.Empty
open import Data.Dec
open import Data.String
open import Data.List

open import STLC.DBFull.Term

infix  4  _∋_⦂_
infix  4  _⊢_⦂_
infixl 5 _﹐_
infixr 7 _⇒_

-- types

data Ty : 𝒰 where
  _⇒_ : Ty → Ty → Ty
  𝟙   : Ty

-- context

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

-- lookup and context inclusion

data _∋_⦂_ : Ctx → ℕ → Ty → 𝒰 where

  here : ∀ {Γ A}
      ------------------
       → Γ ﹐ A ∋ zero ⦂ A

  there : ∀ {Γ x A}
        → Γ ∋ x ⦂ A
          ------------------
        → Γ ﹐ A ∋ (suc x) ⦂ A

∅-empty : ∀ {x A} → ¬ (∅ ∋ x ⦂ A)
∅-empty ()

-- typing judgement

data _⊢_⦂_ : Ctx → Term → Ty → 𝒰 where

  -- Unit
  ⊢𝓉𝓉 : ∀ {Γ}
      -----------
    → Γ ⊢ 𝓉𝓉 ⦂ 𝟙

  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ N A B}
    → Γ ﹐ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ N ⦂ A ⇒ B

  -- ⇒-E
  _⊢·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B


module STLC.DBFull.Term where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Dec
open import Data.String
open import Structures.IdentitySystem

open import Interlude


--infix  1 begin_
--infixr 2 _—→⟨_⟩_
--infix  2 _—↠_
--infix  3 _∎ᵣ
--infix  4 _—→_
infix  5 ƛ_
infixl 7 _·_
infix  9 `_
--infix  9 _[_:=_]

-- terms

data Term : 𝒰 where
  𝓉𝓉  : Term
  `_  : ℕ → Term
  ƛ_  : Term → Term
  _·_ : Term → Term → Term

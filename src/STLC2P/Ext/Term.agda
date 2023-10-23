module STLC2P.Ext.Term where

open import Prelude
open import Data.Empty
open import Data.Dec
open import Data.String

open import Interlude

-- names

Id : 𝒰
Id = String

infix  3 _⇀₁
infix  3 _⇀₂
infix  5 ƛ_⇒_
infix  5 ⁇_↑_↓_
infixl 7 _·_
infix  8 〈_⹁_〉
infix  9 `_

-- terms

data Term : 𝒰 where
  -- pure STLC
  `_     : Id → Term
  ƛ_⇒_   : Id → Term → Term
  _·_    : Term → Term → Term
  -- booleans
  𝓉      : Term
  𝒻      : Term
  ⁇_↑_↓_ : Term → Term → Term → Term
  -- pairs
  〈_⹁_〉   : Term → Term → Term
  _⇀₁   : Term → Term
  _⇀₂   : Term → Term

-- TODO terms form a set

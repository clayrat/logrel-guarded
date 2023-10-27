module PCF.Ext.Subst where

open import Prelude
--open import Data.Empty
--open import Data.Unit
open import Data.Dec
open import Data.Nat hiding (_·_)
open import Data.String
--open import Structures.IdentitySystem

--open import Interlude
open import PCF.Ext.Term

infix  9 _[_:=_]

-- substitution

_[_:=_] : Term → Id → Term → Term
(` x)          [ y := T ] with x ≟ y
... | yes _        = T
... | no  _        = ` x
(ƛ x ⇒ S)      [ y := T ] with x ≟ y
... | yes _        = ƛ x ⇒ S
... | no  _        = ƛ x ⇒ S [ y := T ]
(R · S)        [ y := T ] = R [ y := T ] · S [ y := T ]
(Y S)          [ y := T ] = Y (S [ y := T ])
(＃ n)         [ y := T ] = ＃ n
𝓈 S            [ y := T ] = 𝓈 (S [ y := T ])
𝓅 S            [ y := T ] = 𝓅 (S [ y := T ])
(?⁰ N ↑ R ↓ S) [ y := T ] = ?⁰ N [ y := T ] ↑ R [ y := T ] ↓ S [ y := T ]

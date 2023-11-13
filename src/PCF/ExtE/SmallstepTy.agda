{-# OPTIONS --guarded #-}
module PCF.ExtE.SmallstepTy where

open import Prelude
open import Data.Nat hiding (_·_)

open import Later
open import Interlude
open import Guarded.Partial
open import PCF.ExtE.TyTerm
open import PCF.ExtE.TyDeriv
open import PCF.ExtE.Smallstep

-- preservation

preserve : ∀ {M N A k}
          → M —→⁅ k ⁆ N
          → ∅ ⊢ M ⦂ A
            ----------
          → ∅ ⊢ N ⦂ A
preserve  β-ƛ    (⊢ƛ e ⊢M ⊢· ⊢N) = subst-ty ⊢N ⊢M
preserve  Ｙ     (⊢Y ⊢M)          = ⊢M ⊢· ⊢Y ⊢M
preserve  β-𝓈    (⊢𝓈 ⊢＃)         = ⊢＃
preserve  β-𝓅⁰   (⊢𝓅 ⊢＃)         = ⊢＃
preserve  β-𝓅ˢ   (⊢𝓅 ⊢＃)         = ⊢＃
preserve  β-?⁰   (⊢?⁰ ⊢＃ ⊢M ⊢N) = ⊢M
preserve  β-?ˢ   (⊢?⁰ ⊢＃ ⊢M ⊢N) = ⊢N
preserve (ξ-· s) (⊢M ⊢· ⊢N)     = preserve s ⊢M ⊢· ⊢N
preserve (ξ-𝓈 s) (⊢𝓈 ⊢M)         = ⊢𝓈 (preserve s ⊢M)
preserve (ξ-𝓅 s) (⊢𝓅 ⊢M)         = ⊢𝓅 (preserve s ⊢M)
preserve (ξ-? s) (⊢?⁰ ⊢L ⊢M ⊢N) = ⊢?⁰ (preserve s ⊢L) ⊢M ⊢N

rtc0-preserve : ∀ {M N A}
          → M —↠⁰ N
          → ∅ ⊢ M ⦂ A
            ----------
          → ∅ ⊢ N ⦂ A
rtc0-preserve {M} {.M} (.M ∎ᵣ)         ⊢M = ⊢M
rtc0-preserve {M} {N}  (.M —→⟨ S ⟩ MS) ⊢M = rtc0-preserve MS (preserve S ⊢M)


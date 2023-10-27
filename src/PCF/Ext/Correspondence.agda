{-# OPTIONS --guarded #-}
module PCF.Ext.Correspondence where

open import Prelude
open import Data.Empty
open import Data.Nat hiding (_·_)
open import Data.String
open import Data.Sum

open import Later
open import Interlude
open import PCF.Ext.Term
open import PCF.Ext.Subst
open import PCF.Ext.BigstepG
open import PCF.Ext.Smallstep

-- 2.5.1
small⁰-big : {k : ℕ} (M N : Term) (Q : Val → ℕ → 𝒰)
           → M —→⁅ s⁰ ⁆ N
           → N ⇓⁅ k ⁆ Q
           → M ⇓⁅ k ⁆ Q
small⁰-big .((ƛ x ⇒ M) · N)       .(M [ x := N ])  Q (β-ƛ {x} {M} {N})        N⇓ =
  roll-· (next (roll-Q· {t = M} (next N⇓)))
small⁰-big .(𝓅 (＃ 0))            .(＃ 0)          Q  β-𝓅⁰                    N⇓ =
  roll-𝓅 {Q = Q} (next (0 , refl , N⇓))
small⁰-big .(𝓅 (＃ suc n))        .(＃ n)          Q (β-𝓅ˢ {n})               N⇓ =
  roll-𝓅 {Q = Q} (next (suc n , refl , N⇓))
small⁰-big .(?⁰ ＃ 0 ↑ M ↓ N)      M               Q (β-?⁰ {M} {N})           N⇓ =
  roll-? (next (roll-Q?0 {t = M} (next N⇓)))
small⁰-big .(?⁰ ＃ suc n ↑ M ↓ N)  N               Q (β-?ˢ {M} {N} {n})       N⇓ =
  roll-? (next (roll-Q?s {s = M} {n = n} (next N⇓)))
small⁰-big .(M · N)               .(M′ · N)        Q (ξ-· {M} {M′} {N} s)    N⇓ =
  roll-· (▹map (small⁰-big M M′ (Q· N Q) s) (unroll-· N⇓))
small⁰-big .(𝓈 M)                 .(𝓈 M′)          Q (ξ-𝓈 {M} {M′} s)        N⇓ =
  roll-𝓈 {Q = Q} (▹map (small⁰-big M M′ (Q𝓈 Q) s) (unroll-𝓈 {Q = Q} N⇓))
small⁰-big .(𝓅 M)                 .(𝓅 M′)         Q (ξ-𝓅 {M} {M′} s)         N⇓ =
  roll-𝓅 {Q = Q} (▹map (small⁰-big M M′ (Q𝓅 Q) s) (unroll-𝓅 {Q = Q} N⇓))
small⁰-big .(?⁰ L ↑ M ↓ N)        .(?⁰ L′ ↑ M ↓ N) Q (ξ-? {L} {L′} {M} {N} s) N⇓ =
  roll-? (▹map (small⁰-big L L′ (Q? M N Q) s) (unroll-? N⇓))

-- 2.5.2
small¹-big : {k : ℕ} (M N : Term) (Q : Val → ℕ → 𝒰)
           → M —→⁅ s¹ ⁆ N
           → ▹ (N ⇓⁅ k ⁆ Q)
           → M ⇓⁅ suc k ⁆ Q
small¹-big .(Y M)          .(M · Y M)       Q (Ｙ {M})                 N⇓▹ =
  roll-Y N⇓▹
small¹-big .(M · N)        .(M′ · N)        Q (ξ-· {M} {M′} {N} s)     N⇓▹ =
  roll-· (▹map (small¹-big M M′ (Q· N Q) s ∘ unroll-·) N⇓▹)
small¹-big .(𝓈 M)          .(𝓈 M′)          Q (ξ-𝓈 {M} {M′} s)         N⇓▹ =
  roll-𝓈 {Q = Q} (▹map (small¹-big M M′ (Q𝓈 Q) s ∘ unroll-𝓈 {Q = Q}) N⇓▹)
small¹-big .(𝓅 M)          .(𝓅 M′)          Q (ξ-𝓅 {M} {M′} s)        N⇓▹ =
  roll-𝓅 {Q = Q} (▹map (small¹-big M M′ (Q𝓅 Q) s ∘ unroll-𝓅 {Q = Q}) N⇓▹)
small¹-big .(?⁰ L ↑ M ↓ N) .(?⁰ L′ ↑ M ↓ N) Q (ξ-? {L} {L′} {M} {N} s) N⇓▹ =
  roll-? (▹map (small¹-big L L′ (Q? M N Q) s ∘ unroll-?) N⇓▹)

-- 2.6

small-rtc-big : {k : ℕ} (M N : Term) (V : Val)
               → M —↠⁰ N
               → N ⇓⁅ k ⁆ᵛ V
               → M ⇓⁅ k ⁆ᵛ V
small-rtc-big M .M V (.M ∎ᵣ)        N⇓ = N⇓
small-rtc-big M  N V (.M —→⟨ s ⟩ r) N⇓ =
  small⁰-big M _ _ s (small-rtc-big _ N V r N⇓)

-- 2.7

_⇛⁅_⁆_ : Term → ℕ → (Term → ℕ → 𝒰) → 𝒰
M ⇛⁅ zero ⁆  Q =  Σ[ N ꞉ Term ] (M —↠⁰ N) × Q N 0
M ⇛⁅ suc k ⁆ Q = (Σ[ N ꞉ Term ] (M —↠⁰ N) × Q N (suc k))
               ⊎ (Σ[ M′ ꞉ Term ] (Σ[ M″ ꞉ Term ] (M —↠⁰ M′) × (M′ —→⁅ s¹ ⁆ M″) × (▹ (M″ ⇛⁅ k ⁆ Q))))

-- TODO define ⇛-elim to reduce duplication

-- 2.8

small-rtc-inter : {k : ℕ} (M N : Term) (Q : Term → ℕ → 𝒰)
                → M —↠⁰ N
                → N ⇛⁅ k ⁆ Q
                → M ⇛⁅ k ⁆ Q
small-rtc-inter {k = zero}  M N Q MN (P , NP , qP)                 = P , MN —↠⁰∘ NP , qP
small-rtc-inter {k = suc k} M N Q MN (inl (P , NP , qP))           = inl (P , MN —↠⁰∘ NP , qP)
small-rtc-inter {k = suc k} M N Q MN (inr (R , S , NR , RS , SQ▹)) = inr (R , S , MN —↠⁰∘ NR , RS , SQ▹)

-- 2.9

inter-comp : {k : ℕ} (M : Term) (Q : Term → ℕ → 𝒰)
           → M ⇛⁅ k ⁆ (λ L n → L ⇛⁅ n ⁆ Q)
           → M ⇛⁅ k ⁆ Q
inter-comp {k = zero}  M Q (N , MN , qN)                 = small-rtc-inter M N Q MN qN
inter-comp {k = suc k} M Q (inl (N , MN , qN))           = small-rtc-inter M N Q MN qN
inter-comp {k = suc k} M Q (inr (N , P , NP , PS , SQ▹)) =
  inr (N , P , NP , PS , ▹map (inter-comp {k} P Q) SQ▹)

-- 2.10

Qᴱ : (Term → Term) → (Term → ℕ → 𝒰) → Term → ℕ → 𝒰
Qᴱ f Q T m = Σ[ M ꞉ Term ] (T ＝ f M) × Q M m

inter-· : {k : ℕ} (M N : Term) (Q : Term → ℕ → 𝒰)
        → M ⇛⁅ k ⁆ Q
        → (M · N) ⇛⁅ k ⁆ (Qᴱ (_· N) Q)
inter-· {k = zero}  M N Q (P , MP , qP)                 = P · N , —↠⁰-· MP , P , refl , qP
inter-· {k = suc k} M N Q (inl (P , MP , qP))           = inl (P · N , —↠⁰-· MP , P , refl , qP)
inter-· {k = suc k} M N Q (inr (R , S , MR , RS , SQ▹)) =
  inr (R · N , S · N , —↠⁰-· MR , ξ-· RS , ▹map (inter-· {k} S N Q) SQ▹)

inter-𝓈 : {k : ℕ} (M : Term) (Q : Term → ℕ → 𝒰)
        → M ⇛⁅ k ⁆ Q
        → (𝓈 M) ⇛⁅ k ⁆ (Qᴱ 𝓈 Q)
inter-𝓈 {k = zero}  M Q (N , MN , qN)                 = 𝓈 N , —↠⁰-𝓈 MN , N , refl , qN
inter-𝓈 {k = suc k} M Q (inl (N , MN , qN))           = inl (𝓈 N , —↠⁰-𝓈 MN , N , refl , qN)
inter-𝓈 {k = suc k} M Q (inr (N , P , MN , NP , SQ▹)) =
  inr (𝓈 N , 𝓈 P , —↠⁰-𝓈 MN , ξ-𝓈 NP , ▹map (inter-𝓈 {k} P Q) SQ▹)

inter-𝓅 : {k : ℕ} (M : Term) (Q : Term → ℕ → 𝒰)
        → M ⇛⁅ k ⁆ Q
        → (𝓅 M) ⇛⁅ k ⁆ (Qᴱ 𝓅 Q)
inter-𝓅 {k = zero}  M Q (N , MN , qN)                 = 𝓅 N , —↠⁰-𝓅 MN , N , refl , qN
inter-𝓅 {k = suc k} M Q (inl (N , MN , qN))           = inl (𝓅 N , —↠⁰-𝓅 MN , N , refl , qN)
inter-𝓅 {k = suc k} M Q (inr (N , P , MN , NP , SQ▹)) =
  inr (𝓅 N , 𝓅 P , —↠⁰-𝓅 MN , ξ-𝓅 NP , ▹map (inter-𝓅 {k} P Q) SQ▹)

inter-? : {k : ℕ} (L M N : Term) (Q : Term → ℕ → 𝒰)
        → L ⇛⁅ k ⁆ Q
        → (?⁰ L ↑ M ↓ N) ⇛⁅ k ⁆ (Qᴱ (λ q → ?⁰ q ↑ M ↓ N) Q)
inter-? {k = zero}  L M N Q (P , LP , qP)                 = ?⁰ P ↑ M ↓ N , —↠⁰-? LP , P , refl , qP
inter-? {k = suc k} L M N Q (inl (P , LP , qP))           = inl (?⁰ P ↑ M ↓ N , —↠⁰-? LP , P , refl , qP)
inter-? {k = suc k} L M N Q (inr (R , S , LR , RS , SQ▹)) =
  inr (?⁰ R ↑ M ↓ N , ?⁰ S ↑ M ↓ N , —↠⁰-? LR , ξ-? RS , ▹map (inter-? {k} S M N Q) SQ▹)


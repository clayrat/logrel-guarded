{-# OPTIONS --guarded #-}
module PCF.Ext.Smallstep where

open import Prelude
open import Data.Empty
open import Data.Nat hiding (_·_)
open import Data.String

open import Later
open import Interlude
open import PCF.Ext.Term
open import PCF.Ext.Subst

infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  2 _—↠⁰_
infix  3 _∎ᵣ
infix  4 _—→⁅_⁆_

-- Step-indexed Small-Step Operational Semantics

data Step : 𝒰 where
  s⁰ s¹ : Step

s→ℕ : Step → ℕ
s→ℕ s⁰ = 0
s→ℕ s¹ = 1

data _—→⁅_⁆_ : Term → Step → Term → 𝒰 where
  β-ƛ  : ∀ {x M N}
         ---------------------------------
       → (ƛ x ⇒ M) · N —→⁅ s⁰ ⁆ M [ x := N ]

  Ｙ   : ∀ {M}
        -------------------
      → Y M —→⁅ s¹ ⁆ M · Y M

  β-𝓈  : ∀ {n}
         --------------------------
       → 𝓈 (＃ n) —→⁅ s⁰ ⁆ ＃ (suc n)

  β-𝓅⁰ : --------------------
         𝓅 (＃ 0) —→⁅ s⁰ ⁆ ＃ 0

  β-𝓅ˢ : ∀ {n}
         --------------------------
       → 𝓅 (＃ (suc n)) —→⁅ s⁰ ⁆ ＃ n

  β-?⁰ : ∀ {M N}
        -------------------
      → ?⁰ (＃ 0) ↑ M ↓ N —→⁅ s⁰ ⁆ M

  β-?ˢ : ∀ {M N n}
        -------------------
      → ?⁰ (＃ (suc n)) ↑ M ↓ N —→⁅ s⁰ ⁆ N

  ξ-· : ∀ {M M′ k N}
      → M —→⁅ k ⁆ M′
        -------------------
      → M · N —→⁅ k ⁆ M′ · N

  ξ-𝓈 : ∀ {M M′ k}
      → M —→⁅ k ⁆ M′
        -------------------
      → 𝓈 M —→⁅ k ⁆ 𝓈 M′

  ξ-𝓅 : ∀ {M M′ k}
      → M —→⁅ k ⁆ M′
        -------------------
      → 𝓅 M —→⁅ k ⁆ 𝓅 M′

  ξ-? : ∀ {L L′ M N k}
      → L —→⁅ k ⁆ L′
        -------------------
      → ?⁰ L ↑ M ↓ N —→⁅ k ⁆ ?⁰ L′ ↑ M ↓ N

-- 2.1
step-det : ∀ M k N k′ N′
         → M —→⁅ k  ⁆ N
         → M —→⁅ k′ ⁆ N′
         → (k ＝ k′) × (N ＝ N′)
step-det .((ƛ x ⇒ M) · N)       .s⁰ .(M [ x := N ]) .s⁰ .(M [ x := N ])  (β-ƛ {x} {M} {N})               β-ƛ               = refl , refl
step-det .(Y _)                 .s¹ .(_ · Y _)      .s¹ .(_ · Y _)        Ｙ                             Ｙ                = refl , refl
step-det .(𝓈 (＃ _))            .s⁰ .(＃ _)          .s⁰ .(＃ _)           β-𝓈                           β-𝓈               = refl , refl
step-det .(𝓅 (＃ 0))            .s⁰ .(＃ 0)          .s⁰ .(＃ 0)           β-𝓅⁰                          β-𝓅⁰              = refl , refl
step-det .(𝓅 (＃ suc _))        .s⁰ .(＃ _)          .s⁰ .(＃ _)           β-𝓅ˢ                          β-𝓅ˢ              = refl , refl
step-det .(?⁰ ＃ 0 ↑ N ↓ _)     .s⁰   N              .s⁰ .N                β-?⁰                          β-?⁰              = refl , refl
step-det .(?⁰ ＃ suc _ ↑ _ ↓ N) .s⁰   N              .s⁰ .N                β-?ˢ                          β-?ˢ              = refl , refl
step-det .(M · N)                k .(M₁ · N)          k′ .(M₂ · N)       (ξ-· {M} {M′ = M₁} {N} s₁)     (ξ-· {M′ = M₂} s₂) =
  let k＝k′ , M＝M′ = step-det M k M₁ k′ M₂ s₁ s₂ in
  k＝k′ , ap (_· N) M＝M′
step-det .(𝓈 M)                  k .(𝓈 M₁)             k′ .(𝓈 M₂)         (ξ-𝓈 {M} {M′ = M₁} s₁)         (ξ-𝓈 {M′ = M₂} s₂) =
  let k＝k′ , M＝M′ = step-det M k M₁ k′ M₂ s₁ s₂ in
  k＝k′ , ap 𝓈 M＝M′
step-det .(𝓅 M)                  k .(𝓅 M₁)            k′ .(𝓅 M₂)         (ξ-𝓅 {M} {M′ = M₁} s₁)         (ξ-𝓅 {M′ = M₂} s₂) =
  let k＝k′ , M＝M′ = step-det M k M₁ k′ M₂ s₁ s₂ in
  k＝k′ , ap 𝓅 M＝M′
step-det .(?⁰ L ↑ M ↓ N)         k .(?⁰ L₁ ↑ M ↓ N)   k′ .(?⁰ L₂ ↑ M ↓ N) (ξ-? {L} {L′ = L₁} {M} {N} s₁) (ξ-? {L′ = L₂} s₂) =
  let k＝k′ , L＝L′ = step-det L k L₁ k′ L₂ s₁ s₂ in
  k＝k′ , ap (λ q → ?⁰ q ↑ M ↓ N) L＝L′

-- step RTC on 0

data _—↠⁰_ : Term → Term → 𝒰 where
  _∎ᵣ : ∀ M
      ---------
    → M —↠⁰ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→⁅ s⁰ ⁆ M
    → M —↠⁰ N
      ---------
    → L —↠⁰ N

begin_ : ∀ {M N}
  → M —↠⁰ N
    ------
  → M —↠⁰ N
begin M—↠N = M—↠N

-- lifting
^—↠⁰ : ∀ {L M} → L —→⁅ s⁰ ⁆ M → L —↠⁰ M
^—↠⁰ {L} {M} LM = L —→⟨ LM ⟩ M ∎ᵣ

-- concatenating
_—↠⁰∘_ : ∀ {L M N} → L —↠⁰ M → M —↠⁰ N → L —↠⁰ N
(_ ∎ᵣ)            —↠⁰∘ LN = LN
(L₀ —→⟨ L₀L ⟩ LM) —↠⁰∘ MN = L₀ —→⟨ L₀L ⟩ (LM —↠⁰∘ MN)

-- appending
_—↠⁰+_ : ∀ {L M N} → L —↠⁰ M → M —→⁅ s⁰ ⁆ N → L —↠⁰ N
LM —↠⁰+ MN = LM —↠⁰∘ (^—↠⁰ MN)

-- congruences
—↠⁰-· : ∀ {M M′ N}
       → M —↠⁰ M′
       → (M · N) —↠⁰ (M′ · N)
—↠⁰-· {M} {.M} {N} (.M ∎ᵣ)         = M · N ∎ᵣ
—↠⁰-· {M} {M′} {N} (.M —→⟨ S ⟩ MS) = M · N —→⟨ ξ-· S ⟩ —↠⁰-· MS

—↠⁰-𝓈 : ∀ {M M′}
       → M —↠⁰ M′
       → (𝓈 M) —↠⁰ (𝓈 M′)
—↠⁰-𝓈 {M} {.M} (.M ∎ᵣ)         = 𝓈 M ∎ᵣ
—↠⁰-𝓈 {M} {M′} (.M —→⟨ S ⟩ MS) = 𝓈 M —→⟨ ξ-𝓈 S ⟩ —↠⁰-𝓈 MS

—↠⁰-𝓅 : ∀ {M M′}
       → M —↠⁰ M′
       → (𝓅 M) —↠⁰ (𝓅 M′)
—↠⁰-𝓅 {M} {.M} (.M ∎ᵣ)         = 𝓅 M ∎ᵣ
—↠⁰-𝓅 {M} {M′} (.M —→⟨ S ⟩ MS) = 𝓅 M —→⟨ ξ-𝓅 S ⟩ —↠⁰-𝓅 MS

—↠⁰-? : ∀ {L L′ M N}
       → L —↠⁰ L′
       → (?⁰ L ↑ M ↓ N) —↠⁰ (?⁰ L′ ↑ M ↓ N)
—↠⁰-? {L} {.L} {M} {N} (.L ∎ᵣ)         = ?⁰ L ↑ M ↓ N ∎ᵣ
—↠⁰-? {L} {L′} {M} {N} (.L —→⟨ S ⟩ MS) = ?⁰ L ↑ M ↓ N —→⟨ ξ-? S ⟩ —↠⁰-? MS

-- step RTC over arbitrary steps w/ predicate
_=⇒⁅_⁆_ : Term → ℕ → (Term → 𝒰) → 𝒰
M =⇒⁅ 0     ⁆ Q = Σ[ N ꞉ Term ] (M —↠⁰ N) × (Q N)
M =⇒⁅ suc k ⁆ Q = Σ[ M′ ꞉ Term ] (Σ[ M″ ꞉ Term ] (M —↠⁰ M′) × (M′ —→⁅ s¹ ⁆ M″) × ▹ (M″ =⇒⁅ k ⁆ Q))

-- step RTC over arbitrary steps
_=⇒⁅_⁆ᵗ_ : Term → ℕ → Term → 𝒰
M =⇒⁅ k ⁆ᵗ N = M =⇒⁅ k ⁆ (_＝ N)

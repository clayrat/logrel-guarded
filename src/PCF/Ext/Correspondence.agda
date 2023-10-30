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
open import PCF.Ext.Bigstep
open import PCF.Ext.Smallstep

-- 2.5.1
small⁰-big : {k : ℕ} (M N : Term) (Q : Val → ℕ → 𝒰)
           → M —→⁅ s⁰ ⁆ N
           → N ⇓⁅ k ⁆ Q
           → M ⇓⁅ k ⁆ Q
small⁰-big .((ƛ x ⇒ M) · N)       .(M [ x := N ])  Q (β-ƛ {x} {M} {N})        N⇓ =
  N⇓
small⁰-big .(𝓈 (＃ n))            .(＃ (suc n))    Q (β-𝓈 {n})                N⇓ =
  n , refl , N⇓
small⁰-big .(𝓅 (＃ 0))            .(＃ 0)          Q  β-𝓅⁰                    N⇓ =
  0 , refl , N⇓
small⁰-big .(𝓅 (＃ suc n))        .(＃ n)          Q (β-𝓅ˢ {n})               N⇓ =
  suc n , refl , N⇓
small⁰-big .(?⁰ ＃ 0 ↑ M ↓ N)      M               Q (β-?⁰ {M} {N})           N⇓ =
  N⇓
small⁰-big .(?⁰ ＃ suc n ↑ M ↓ N)  N               Q (β-?ˢ {M} {N} {n})       N⇓ =
  N⇓
small⁰-big .(M · N)               .(M′ · N)        Q (ξ-· {M} {M′} {N} s)    N⇓ =
  small⁰-big M M′ (Q· N Q) s  N⇓
small⁰-big .(𝓈 M)                 .(𝓈 M′)          Q (ξ-𝓈 {M} {M′} s)        N⇓ =
  small⁰-big M M′ (Q𝓈 Q) s N⇓
small⁰-big .(𝓅 M)                 .(𝓅 M′)         Q (ξ-𝓅 {M} {M′} s)         N⇓ =
  small⁰-big M M′ (Q𝓅 Q) s N⇓
small⁰-big .(?⁰ L ↑ M ↓ N)        .(?⁰ L′ ↑ M ↓ N) Q (ξ-? {L} {L′} {M} {N} s) N⇓ =
  small⁰-big L L′ (Q? M N Q) s N⇓

-- 2.5.2
small¹-big : {k : ℕ} (M N : Term) (Q : Val → ℕ → 𝒰)
           → M —→⁅ s¹ ⁆ N
           → ▹ (N ⇓⁅ k ⁆ Q)
           → M ⇓⁅ suc k ⁆ Q
small¹-big .(Y M)          .(M · Y M)       Q (Ｙ {M})                 N⇓▹ =
  N⇓▹
small¹-big .(M · N)        .(M′ · N)        Q (ξ-· {M} {M′} {N} s)     N⇓▹ =
  small¹-big M M′ (Q· N Q) s  N⇓▹
small¹-big .(𝓈 M)          .(𝓈 M′)          Q (ξ-𝓈 {M} {M′} s)         N⇓▹ =
  small¹-big M M′ (Q𝓈 Q) s N⇓▹
small¹-big .(𝓅 M)          .(𝓅 M′)          Q (ξ-𝓅 {M} {M′} s)        N⇓▹ =
  small¹-big M M′ (Q𝓅 Q) s N⇓▹
small¹-big .(?⁰ L ↑ M ↓ N) .(?⁰ L′ ↑ M ↓ N) Q (ξ-? {L} {L′} {M} {N} s) N⇓▹ =
  small¹-big L L′ (Q? M N Q) s N⇓▹

-- 2.6

small-rtc-big : {k : ℕ} (M N : Term) (Q : Val → ℕ → 𝒰)
               → M —↠⁰ N
               → N ⇓⁅ k ⁆ Q
               → M ⇓⁅ k ⁆ Q
small-rtc-big M .M V (.M ∎ᵣ)        N⇓ = N⇓
small-rtc-big M  N V (.M —→⟨ s ⟩ r) N⇓ =
  small⁰-big M _ _ s (small-rtc-big _ N V r N⇓)

small-rtc-big-v : {k : ℕ} (M N : Term) (V : Val)
               → M —↠⁰ N
               → N ⇓⁅ k ⁆ᵛ V
               → M ⇓⁅ k ⁆ᵛ V
small-rtc-big-v M N V = small-rtc-big M N (λ v l → (l ＝ 0) × (v ＝ V))

-- 2.7

_⇛⁅_⁆_ : Term → ℕ → (Term → ℕ → 𝒰) → 𝒰
M ⇛⁅ zero ⁆  Q =  Σ[ N ꞉ Term ] (M —↠⁰ N) × Q N 0
M ⇛⁅ suc k ⁆ Q = (Σ[ N ꞉ Term ] (M —↠⁰ N) × Q N (suc k))
               ⊎ (Σ[ M′ ꞉ Term ] (Σ[ M″ ꞉ Term ] (M —↠⁰ M′) × (M′ —→⁅ s¹ ⁆ M″) × (▹ (M″ ⇛⁅ k ⁆ Q))))

-- constructors

⇛ᵏ : {k : ℕ} {M N : Term} {Q : Term → ℕ → 𝒰}
   → M —↠⁰ N → Q N k
     ----------------
   → M ⇛⁅ k ⁆ Q
⇛ᵏ {k = zero}  {N} MN QN = N , MN , QN
⇛ᵏ {k = suc k} {N} MN QN = inl (N , MN , QN)

⇛ˢ : {k : ℕ} {M M′ M″ : Term} {Q : Term → ℕ → 𝒰}
   → M —↠⁰ M′ → M′ —→⁅ s¹ ⁆ M″ → ▹ (M″ ⇛⁅ k ⁆ Q)
     ------------------------------------------
   → M ⇛⁅ suc k ⁆ Q
⇛ˢ {M′} {M″} MM′ MM″ MQ▹ = inr (M′ , M″ , MM′ , MM″ , MQ▹)

-- TODO define ⇛-elim to reduce duplication

-- 2.8

small-rtc-inter : {k : ℕ} (M N : Term) (Q : Term → ℕ → 𝒰)
                → M —↠⁰ N
                → N ⇛⁅ k ⁆ Q
                → M ⇛⁅ k ⁆ Q
small-rtc-inter {k = zero}  M N Q MN (P , NP , qP)                 = ⇛ᵏ {Q = Q} (MN —↠⁰∘ NP) qP
small-rtc-inter {k = suc k} M N Q MN (inl (P , NP , qP))           = ⇛ᵏ         (MN —↠⁰∘ NP) qP
small-rtc-inter {k = suc k} M N Q MN (inr (R , S , NR , RS , SQ▹)) = ⇛ˢ (MN —↠⁰∘ NR) RS SQ▹

-- 2.9

inter-comp : {k : ℕ} (M : Term) (Q : Term → ℕ → 𝒰)
           → M ⇛⁅ k ⁆ (λ L n → L ⇛⁅ n ⁆ Q)
           → M ⇛⁅ k ⁆ Q
inter-comp {k = zero}  M Q (N , MN , qN)                 =
  small-rtc-inter M N Q MN qN
inter-comp {k = suc k} M Q (inl (N , MN , qN))           =
  small-rtc-inter M N Q MN qN
inter-comp {k = suc k} M Q (inr (N , P , NP , PS , SQ▹)) =
  ⇛ˢ NP PS (▹map (inter-comp {k} P Q) SQ▹)

-- 2.10

Qᴱ : (Term → Term) → (Term → ℕ → 𝒰) → Term → ℕ → 𝒰
Qᴱ f Q T m = Σ[ M ꞉ Term ] (T ＝ f M) × Q M m

inter-· : {k : ℕ} (M N : Term) (Q : Term → ℕ → 𝒰)
        → M ⇛⁅ k ⁆ Q
        → (M · N) ⇛⁅ k ⁆ (Qᴱ (_· N) Q)
inter-· {k = zero}  M N Q (P , MP , qP)                 =
  ⇛ᵏ {Q = Qᴱ (_· N) Q} (—↠⁰-· MP) (P , refl , qP)
inter-· {k = suc k} M N Q (inl (P , MP , qP))           =
  ⇛ᵏ                   (—↠⁰-· MP) (P , refl , qP)
inter-· {k = suc k} M N Q (inr (R , S , MR , RS , SQ▹)) =
  ⇛ˢ (—↠⁰-· MR) (ξ-· RS) (▹map (inter-· {k} S N Q) SQ▹)

inter-𝓈 : {k : ℕ} (M : Term) (Q : Term → ℕ → 𝒰)
        → M ⇛⁅ k ⁆ Q
        → (𝓈 M) ⇛⁅ k ⁆ (Qᴱ 𝓈 Q)
inter-𝓈 {k = zero}  M Q (N , MN , qN)                 =
  ⇛ᵏ {Q = Qᴱ 𝓈 Q} (—↠⁰-𝓈 MN) (N , refl , qN)
inter-𝓈 {k = suc k} M Q (inl (N , MN , qN))           =
  ⇛ᵏ             (—↠⁰-𝓈 MN) (N , refl , qN)
inter-𝓈 {k = suc k} M Q (inr (N , P , MN , NP , SQ▹)) =
  ⇛ˢ (—↠⁰-𝓈 MN) (ξ-𝓈 NP) (▹map (inter-𝓈 {k} P Q) SQ▹)

inter-𝓅 : {k : ℕ} (M : Term) (Q : Term → ℕ → 𝒰)
        → M ⇛⁅ k ⁆ Q
        → (𝓅 M) ⇛⁅ k ⁆ (Qᴱ 𝓅 Q)
inter-𝓅 {k = zero}  M Q (N , MN , qN)                 =
  ⇛ᵏ {Q = Qᴱ 𝓅 Q} (—↠⁰-𝓅 MN) (N , refl , qN)
inter-𝓅 {k = suc k} M Q (inl (N , MN , qN))           =
  ⇛ᵏ              (—↠⁰-𝓅 MN) (N , refl , qN)
inter-𝓅 {k = suc k} M Q (inr (N , P , MN , NP , SQ▹)) =
  ⇛ˢ (—↠⁰-𝓅 MN) (ξ-𝓅 NP) (▹map (inter-𝓅 {k} P Q) SQ▹)

inter-? : {k : ℕ} (L M N : Term) (Q : Term → ℕ → 𝒰)
        → L ⇛⁅ k ⁆ Q
        → (?⁰ L ↑ M ↓ N) ⇛⁅ k ⁆ (Qᴱ (λ q → ?⁰ q ↑ M ↓ N) Q)
inter-? {k = zero}  L M N Q (P , LP , qP)                 =
  ⇛ᵏ {Q = Qᴱ (λ q → ?⁰ q ↑ M ↓ N) Q} (—↠⁰-? LP) (P , refl , qP)
inter-? {k = suc k} L M N Q (inl (P , LP , qP))           =
  ⇛ᵏ                                 (—↠⁰-? LP) (P , refl , qP)
inter-? {k = suc k} L M N Q (inr (R , S , LR , RS , SQ▹)) =
  ⇛ˢ (—↠⁰-? LR) (ξ-? RS) (▹map (inter-? {k} S M N Q) SQ▹)

-- 2.11

inter-big-comp : {k : ℕ} (M : Term) (Q : Val → ℕ → 𝒰)
          → M ⇛⁅ k ⁆ (λ N z → N ⇓⁅ z ⁆ Q)
          → M ⇓⁅ k ⁆ Q
inter-big-comp {k = zero}  M Q (P , LP , qP)                 =
  small-rtc-big M P Q LP qP
inter-big-comp {k = suc k} M Q (inl (P , LP , qP))           =
  small-rtc-big M P Q LP qP
inter-big-comp {k = suc k} M Q (inr (R , S , LR , RS , SQ▹)) =
  small-rtc-big M R Q LR (small¹-big R S Q RS (▹map (inter-big-comp S Q) SQ▹))

-- 2.12

Q𝓈-covariant : (Q R : Val → ℕ → 𝒰)
             → (∀ v n → Q v n → R v n)
             → ∀ v n → Q𝓈 Q v n → Q𝓈 R v n
Q𝓈-covariant Q R qr v n (x , e , qx) = x , e , qr (v-＃ (suc x)) n qx

Q𝓅-covariant : (Q R : Val → ℕ → 𝒰)
             → (∀ v n → Q v n → R v n)
             → ∀ v n → Q𝓅 Q v n → Q𝓅 R v n
Q𝓅-covariant Q R qr v n (x , e , qx) = x , e , qr (v-＃ (pred x)) n qx

{-
cov-distr : ▹ (  (Q R : Val → ℕ → 𝒰) → (∀ v n → Q v n → R v n)
                      → (M : Term) → (k : ℕ)
                      → M ⇓⁅ k ⁆ Q → M ⇓⁅ k ⁆ R)
          → (Q R : Val → ℕ → 𝒰) → (∀ v n → Q v n → R v n)
          → (M : Term) → (k : ℕ)
          → ▹ (M ⇓⁅ k ⁆ Q → M ⇓⁅ k ⁆ R)
cov-distr cb▹ Q R qr M k = cb▹ ⊛ next Q ⊛ next R ⊛ next qr
                               ⊛ next M ⊛ next k
-}

-- substitution is problematic
{-# TERMINATING #-}
mutual
  Q·-covariant : (Q R : Val → ℕ → 𝒰) → (∀ v n → Q v n → R v n)
               → (s : Term) → (v : Val) → (n : ℕ)
               → Q· s Q v n → Q· s R v n
  Q·-covariant Q R qr s (v-ƛ x t) n qq =
    ⇓-covariant Q R qr (t [ x := s ]) n qq

  Q?-covariant : (Q R : Val → ℕ → 𝒰) → (∀ v n → Q v n → R v n)
               → (s t : Term) → (v : Val) → (n : ℕ)
               → Q? s t Q v n → Q? s t R v n
  Q?-covariant Q R qr s t (v-＃ zero)    n qq =
    ⇓-covariant Q R qr s n qq
  Q?-covariant Q R qr s t (v-＃ (suc m)) n qq =
    ⇓-covariant Q R qr t n qq

  ⇓-covariant : (Q R : Val → ℕ → 𝒰) → (∀ v n → Q v n → R v n)
              → (M : Term) → (k : ℕ)
              → M ⇓⁅ k ⁆ Q → M ⇓⁅ k ⁆ R
  ⇓-covariant Q R qr (ƛ x ⇒ t)       k      M⇓ =
    qr (v-ƛ x t) k M⇓
  ⇓-covariant Q R qr (r · s)         k      M⇓ =
    ⇓-covariant (Q· s Q) (Q· s R) (Q·-covariant Q R qr s) r k M⇓
  ⇓-covariant Q R qr (Y t)          (suc k) M⇓ =
    ▹map (⇓-covariant Q R qr (t · Y t) k) M⇓
  ⇓-covariant Q R qr (＃ n)           k     M⇓ =
    qr (v-＃ n) k M⇓
  ⇓-covariant Q R qr (𝓈 t)           k      M⇓ =
    ⇓-covariant (Q𝓈 Q) (Q𝓈 R) (Q𝓈-covariant Q R qr) t k M⇓
  ⇓-covariant Q R qr (𝓅 t)           k      M⇓ =
    ⇓-covariant (Q𝓅 Q) (Q𝓅 R) (Q𝓅-covariant Q R qr) t k M⇓
  ⇓-covariant Q R qr (?⁰ r ↑ s ↓ t)  k      M⇓ =
    ⇓-covariant (Q? s t Q) (Q? s t R) (Q?-covariant Q R qr s t) r k M⇓

⇛-covariant : (Q R : Term → ℕ → 𝒰) → (∀ v n → Q v n → R v n)
            → (M : Term) → (k : ℕ)
            → M ⇛⁅ k ⁆ Q → M ⇛⁅ k ⁆ R
⇛-covariant Q R qr M  zero   (N , MN , QN)                = ⇛ᵏ {Q = R} MN (qr N 0 QN)
⇛-covariant Q R qr M (suc k) (inl (N , MN , QN))          = ⇛ᵏ {Q = R} MN (qr N (suc k) QN)
⇛-covariant Q R qr M (suc k) (inr (N , S , MN , NS , Q▹)) = ⇛ˢ MN NS (▹map (⇛-covariant Q R qr S k) Q▹)

-- 2.13.1

Qᵀ : (Val → ℕ → 𝒰)
   → Term → ℕ → 𝒰
Qᵀ Q N k = Σ[ v ꞉ Val ] IsVal N v × Q v k

Qᵀ-impl : (Q : Val → ℕ → 𝒰)
        → (N : Term) → (k : ℕ)
        → Qᵀ Q N k → N ⇓⁅ k ⁆ Q
Qᵀ-impl Q (ƛ x ⇒ t) k (.(v-ƛ x t) , is-ƛ , q) = q
Qᵀ-impl Q (＃ n)    k (.(v-＃ n)  , is-＃ , q) = q

-- TODO looks like Q₂ and Q₃ can be merged in all cases
-- substitution is problematic
{-# TERMINATING #-}
big→inter : {k : ℕ} (M : Term) (Q : Val → ℕ → 𝒰)
          → M ⇓⁅ k ⁆ Q
          → M ⇛⁅ k ⁆ (Qᵀ Q)
big→inter     (ƛ x ⇒ t)      Q M⇓ =
  ⇛ᵏ (ƛ x ⇒ t ∎ᵣ) (v-ƛ x t , is-ƛ , M⇓)
big→inter {k} (r · s)        Q M⇓ =
  let h1 = ⇓-covariant (Q· s Q) Q₂ Q·₂-impl r k M⇓
      h2 = ⇓-covariant Q₂ Q₃ Q₂₃-impl r k h1
      h3 = big→inter r Q₃ h2
      h4 = inter-· r s (Qᵀ Q₃) h3
      h5 = ⇛-covariant (Qᴱ (_· s) (Qᵀ Q₃)) Q₄ Q₃₄ (r · s) k h4
      h6 = ⇛-covariant Q₄ (λ L n → L ⇛⁅ n ⁆ Qᵀ Q) Q₄i (r · s) k h5
    in
   inter-comp (r · s) (Qᵀ Q) h6
  where
  Q₂ : Val → ℕ → 𝒰
  Q₂ (v-＃ x)  m = ⊥
  Q₂ (v-ƛ x t) m = (t [ x := s ]) ⇛⁅ m ⁆ Qᵀ Q

  Q·₂-impl : ∀ v n → Q· s Q v n → Q₂ v n
  Q·₂-impl (v-ƛ x t) n qq = big→inter (t [ x := s ]) Q qq

  Q₃ : Val → ℕ → 𝒰
  Q₃ (v-＃ x)  m = ⊥
  Q₃ (v-ƛ x t) m = ((ƛ x ⇒ t) · s) ⇛⁅ m ⁆ Qᵀ Q

  Q₂₃-impl : ∀ v n → Q₂ v n → Q₃ v n
  Q₂₃-impl (v-ƛ x t) n qq =
    small-rtc-inter ((ƛ x ⇒ t) · s) (t [ x := s ]) (Qᵀ Q) (^—↠⁰ β-ƛ) qq

  Q₄ : Term → ℕ → 𝒰
  Q₄ (` x) m = ⊥
  Q₄ (ƛ x ⇒ t) m = ⊥
  Q₄ (` x · s) m = ⊥
  Q₄ ((ƛ x ⇒ r) · s) m = ((ƛ x ⇒ r) · s) ⇛⁅ m ⁆ Qᵀ Q
  Q₄ (r · r₁ · s) m = ⊥
  Q₄ (Y r · s) m = ⊥
  Q₄ (＃ x · s) m = ⊥
  Q₄ (𝓈 r · s) m = ⊥
  Q₄ (𝓅 r · s) m = ⊥
  Q₄ ((?⁰ r ↑ r₁ ↓ r₂) · s) m = ⊥
  Q₄ (Y t) m = ⊥
  Q₄ (＃ x) m = ⊥
  Q₄ (𝓈 t) m = ⊥
  Q₄ (𝓅 t) m = ⊥
  Q₄ (?⁰ t ↑ t₁ ↓ t₂) m = ⊥

  Q₃₄ : ∀ t n → Qᴱ (_· s) (Qᵀ Q₃) t n → Q₄ t n
  Q₃₄ t1 n (.(ƛ x ⇒ t) , er , .(v-ƛ x t) , is-ƛ {x} {t} , qq) = subst (λ q → Q₄ q n) (sym er) qq

  Q₄i : ∀ v n → Q₄ v n → v ⇛⁅ n ⁆ Qᵀ Q
  Q₄i ((ƛ x ⇒ t) · s) n qq = qq

big→inter {suc k} (Y t)          Q M⇓ =
  ⇛ˢ (Y t ∎ᵣ) Ｙ (▹map (big→inter (t · Y t) Q) M⇓)
big→inter         (＃ n)          Q M⇓ =
  ⇛ᵏ (＃ n ∎ᵣ) (v-＃ n , is-＃ , M⇓)
big→inter {k} (𝓈 t)          Q M⇓ =
  let h1 = ⇓-covariant (Q𝓈 Q) Q₂ Q𝓈₂-impl t k M⇓
      h2 = ⇓-covariant Q₂ Q₃ Q₂₃-impl t k h1
      h3 = big→inter t Q₃ h2
      h4 = inter-𝓈 t (Qᵀ Q₃) h3
      h5 = ⇛-covariant (Qᴱ 𝓈 (Qᵀ Q₃)) Q₄ Q₃₄ (𝓈 t) k h4
      h6 = ⇛-covariant Q₄ (λ L n → L ⇛⁅ n ⁆ Qᵀ Q) Q₄i (𝓈 t) k h5
   in
  inter-comp (𝓈 t) (Qᵀ Q) h6
  where
  Q₂ : Val → ℕ → 𝒰
  Q₂ (v-＃ n)  m = (＃ (suc n)) ⇛⁅ m ⁆ Qᵀ Q
  Q₂ (v-ƛ _ _) m = ⊥

  Q𝓈₂-impl : ∀ v s → Q𝓈 Q v s → Q₂ v s
  Q𝓈₂-impl (v-＃ x)  s (n , e , q) =
    big→inter (＃ suc x) Q (subst (λ q → Q (v-＃ (suc q)) s) (sym (v-＃-inj e)) q)
  Q𝓈₂-impl (v-ƛ x t) s (n , e , q) =
    absurd (v-＃≠v-ƛ (sym e))

  Q₃ : Val → ℕ → 𝒰
  Q₃ (v-＃ n)  m = (𝓈 (＃ n)) ⇛⁅ m ⁆ Qᵀ Q
  Q₃ (v-ƛ x t) m = ⊥

  Q₂₃-impl : ∀ v n → Q₂ v n → Q₃ v n
  Q₂₃-impl (v-＃ m) n qq =
    small-rtc-inter (𝓈 (＃ m)) (＃ (suc m)) (Qᵀ Q) (^—↠⁰ β-𝓈) qq

  Q₄ : Term → ℕ → 𝒰
  Q₄ (` x) m = ⊥
  Q₄ (ƛ x ⇒ t) m = ⊥
  Q₄ (r · s) m = ⊥
  Q₄ (Y t) m = ⊥
  Q₄ (＃ _) m = ⊥
  Q₄ (𝓈 (` x)) m = ⊥
  Q₄ (𝓈 (ƛ x ⇒ t)) m = ⊥
  Q₄ (𝓈 (t · t₁)) m = ⊥
  Q₄ (𝓈 (Y t)) m = ⊥
  Q₄ (𝓈 (＃ n)) m = 𝓈 (＃ n) ⇛⁅ m ⁆ Qᵀ Q
  Q₄ (𝓈 (𝓈 t)) m = ⊥
  Q₄ (𝓈 (𝓅 t)) m = ⊥
  Q₄ (𝓈 (?⁰ t ↑ t₁ ↓ t₂)) m = ⊥
  Q₄ (𝓅 t) m = ⊥
  Q₄ (?⁰ t ↑ t₁ ↓ t₂) m = ⊥

  Q₃₄ : ∀ t n → Qᴱ 𝓈 (Qᵀ Q₃) t n → Q₄ t n
  Q₃₄ t1 n (.(＃ m) , e , .(v-＃ m) , is-＃ {n = m} , qq) = subst (λ q → Q₄ q n) (sym e) qq

  Q₄i : ∀ v n → Q₄ v n → v ⇛⁅ n ⁆ Qᵀ Q
  Q₄i (𝓈 (＃ m)) n qq = qq

big→inter {k}     (𝓅 t)          Q M⇓ =
  let h1 = ⇓-covariant (Q𝓅 Q) Q₂ Q𝓅₂-impl t k M⇓
      h2 = ⇓-covariant Q₂ Q₃ Q₂₃-impl t k h1
      h3 = big→inter t Q₃ h2
      h4 = inter-𝓅 t (Qᵀ Q₃) h3
      h5 = ⇛-covariant (Qᴱ 𝓅 (Qᵀ Q₃)) Q₄ Q₃₄ (𝓅 t) k h4
      h6 = ⇛-covariant Q₄ (λ L n → L ⇛⁅ n ⁆ Qᵀ Q) Q₄i (𝓅 t) k h5
   in
  inter-comp (𝓅 t) (Qᵀ Q) h6
  where
  Q₂ : Val → ℕ → 𝒰
  Q₂ (v-＃ n)  m = (＃ (pred n)) ⇛⁅ m ⁆ Qᵀ Q
  Q₂ (v-ƛ _ _) m = ⊥

  Q𝓅₂-impl : ∀ v s → Q𝓅 Q v s → Q₂ v s
  Q𝓅₂-impl (v-＃ x)  s (n , e , q) =
    big→inter (＃ pred x) Q (subst (λ q → Q (v-＃ (pred q)) s) (sym (v-＃-inj e)) q)
  Q𝓅₂-impl (v-ƛ x t) s (n , e , q) =
    absurd (v-＃≠v-ƛ (sym e))

  Q₃ : Val → ℕ → 𝒰
  Q₃ (v-＃ n)  m = (𝓅 (＃ n)) ⇛⁅ m ⁆ Qᵀ Q
  Q₃ (v-ƛ x t) m = ⊥

  Q₂₃-impl : ∀ v n → Q₂ v n → Q₃ v n
  Q₂₃-impl (v-＃  zero  ) n qq = small-rtc-inter (𝓅 (＃ 0)    ) (＃ 0) (Qᵀ Q) (^—↠⁰ β-𝓅⁰) qq
  Q₂₃-impl (v-＃ (suc m)) n qq = small-rtc-inter (𝓅 (＃ suc m)) (＃ m) (Qᵀ Q) (^—↠⁰ β-𝓅ˢ) qq

  Q₄ : Term → ℕ → 𝒰
  Q₄ (` x) m = ⊥
  Q₄ (ƛ x ⇒ t) m = ⊥
  Q₄ (r · s) m = ⊥
  Q₄ (Y t) m = ⊥
  Q₄ (＃ _) m = ⊥
  Q₄ (𝓈 _) m = ⊥
  Q₄ (𝓅 (` x)) m = ⊥
  Q₄ (𝓅 (ƛ x ⇒ t)) m = ⊥
  Q₄ (𝓅 (t · t₁)) m = ⊥
  Q₄ (𝓅 (Y t)) m = ⊥
  Q₄ (𝓅 (＃ n)) m = 𝓅 (＃ n) ⇛⁅ m ⁆ Qᵀ Q
  Q₄ (𝓅 (𝓈 t)) m = ⊥
  Q₄ (𝓅 (𝓅 t)) m = ⊥
  Q₄ (𝓅 (?⁰ t ↑ t₁ ↓ t₂)) m = ⊥
  Q₄ (?⁰ t ↑ t₁ ↓ t₂) m = ⊥

  Q₃₄ : ∀ t n → Qᴱ 𝓅 (Qᵀ Q₃) t n → Q₄ t n
  Q₃₄ t1 n (.(＃ m) , e , .(v-＃ m) , is-＃ {n = m} , qq) = subst (λ q → Q₄ q n) (sym e) qq

  Q₄i : ∀ v n → Q₄ v n → v ⇛⁅ n ⁆ Qᵀ Q
  Q₄i (𝓅 (＃ m)) n qq = qq

big→inter {k}     (?⁰ r ↑ s ↓ t) Q M⇓ =
  let h1 = ⇓-covariant (Q? s t Q) Q₂ Q?₂-impl r k M⇓
      h2 = ⇓-covariant Q₂ Q₃ Q₂₃-impl r k h1
      h3 = big→inter r Q₃ h2
      h4 = inter-? r s t (Qᵀ Q₃) h3
      h5 = ⇛-covariant (Qᴱ (λ q → ?⁰ q ↑ s ↓ t) (Qᵀ Q₃)) Q₄ Q₃₄ (?⁰ r ↑ s ↓ t) k h4
      h6 = ⇛-covariant Q₄ (λ L n → L ⇛⁅ n ⁆ Qᵀ Q) Q₄i (?⁰ r ↑ s ↓ t) k h5
    in
   inter-comp (?⁰ r ↑ s ↓ t) (Qᵀ Q) h6
  where
  Q₂ : Val → ℕ → 𝒰
  Q₂ (v-＃  zero  ) m = s ⇛⁅ m ⁆ Qᵀ Q
  Q₂ (v-＃ (suc _)) m = t ⇛⁅ m ⁆ Qᵀ Q
  Q₂ (v-ƛ _ _     ) m = ⊥

  Q?₂-impl : ∀ v n → Q? s t Q v n → Q₂ v n
  Q?₂-impl (v-＃  zero)   n qq = big→inter s Q qq
  Q?₂-impl (v-＃ (suc _)) n qq = big→inter t Q qq

  Q₃ : Val → ℕ → 𝒰
  Q₃ (v-＃ n ) m = (?⁰ (＃ n) ↑ s ↓ t) ⇛⁅ m ⁆ Qᵀ Q
  Q₃ (v-ƛ _ _) m = ⊥

  Q₂₃-impl : ∀ v n → Q₂ v n → Q₃ v n
  Q₂₃-impl (v-＃  zero  ) n qq = small-rtc-inter (?⁰ ＃ 0     ↑ s ↓ t) s (Qᵀ Q) (^—↠⁰ β-?⁰) qq
  Q₂₃-impl (v-＃ (suc m)) n qq = small-rtc-inter (?⁰ ＃ suc m ↑ s ↓ t) t (Qᵀ Q) (^—↠⁰ β-?ˢ) qq

  Q₄ : Term → ℕ → 𝒰
  Q₄ (` x) m = ⊥
  Q₄ (ƛ x ⇒ t) m = ⊥
  Q₄ (r · s) m = ⊥
  Q₄ (Y t) m = ⊥
  Q₄ (＃ x) m = ⊥
  Q₄ (𝓈 t) m = ⊥
  Q₄ (𝓅 t) m = ⊥
  Q₄ (?⁰ ` x ↑ t₁ ↓ t₂) m = ⊥
  Q₄ (?⁰ ƛ x ⇒ t ↑ t₁ ↓ t₂) m = ⊥
  Q₄ (?⁰ t · t₃ ↑ t₁ ↓ t₂) m = ⊥
  Q₄ (?⁰ Y t ↑ t₁ ↓ t₂) m = ⊥
  Q₄ (?⁰ ＃ n ↑ t₁ ↓ t₂) m = (?⁰ ＃ n ↑ t₁ ↓ t₂) ⇛⁅ m ⁆ Qᵀ Q
  Q₄ (?⁰ 𝓈 t ↑ t₁ ↓ t₂) m = ⊥
  Q₄ (?⁰ 𝓅 t ↑ t₁ ↓ t₂) m = ⊥
  Q₄ (?⁰ ?⁰ t ↑ t₃ ↓ t₄ ↑ t₁ ↓ t₂) m = ⊥

  Q₃₄ : ∀ p n → Qᴱ (λ q → ?⁰ q ↑ s ↓ t) (Qᵀ Q₃) p n → Q₄ p n
  Q₃₄ p n (.(＃ m) , e , .(v-＃ m) , is-＃ {n = m} , qq) = subst (λ q → Q₄ q n) (sym e) qq

  Q₄i : ∀ v n → Q₄ v n → v ⇛⁅ n ⁆ Qᵀ Q
  Q₄i (?⁰ ＃ p ↑ t₁ ↓ t₂) n qq = qq

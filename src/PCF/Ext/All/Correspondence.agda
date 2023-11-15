{-# OPTIONS --guarded #-}
module PCF.Ext.All.Correspondence where

open import Prelude
open import Data.Empty
open import Data.Nat hiding (_·_)
open import Data.String
open import Data.Sum

open import Later
open import Interlude
open import PCF.Ext.TyTerm
open import PCF.Ext.Subst
open import PCF.Ext.All.Bigstep
open import PCF.Ext.All.Smallstep

-- 2.5.1

small⁰-big : ∀ {k M N Q}
           → M —→⁅ s⁰ ⁆ N
           → N ⇓⁅ k ⁆ Q
           → M ⇓⁅ k ⁆ Q
small⁰-big             (ξ-· s) N⇓ = small⁰-big s N⇓
small⁰-big {suc k} {Q} (ξ-𝓈 s) N⇓ = ⇉𝓈 {Q = Q} (▹map (small⁰-big s) (𝓈⇉ {Q = Q} N⇓))
small⁰-big {suc k} {Q} (ξ-𝓅 s) N⇓ = ⇉𝓅 {Q = Q} (▹map (small⁰-big s) (𝓅⇉ {Q = Q} N⇓))
small⁰-big             (ξ-? s) N⇓ = small⁰-big s N⇓

-- 2.5.2

small¹-big : ∀ {k M N Q}
           → M —→⁅ s¹ ⁆ N
           → ▹ (N ⇓⁅ k ⁆ Q)
           → M ⇓⁅ suc k ⁆ Q
small¹-big                (β-ƛ {M} {N} {A}) N⇓▹ = ⇉Q· {t = M} {s = N} {A = A} N⇓▹
small¹-big                 Ｙ               N⇓▹ = ⇉Y N⇓▹
small¹-big            {Q} (β-𝓈 {n})         N⇓▹ = ⇉𝓈 {Q = Q} (▹map (λ q → n , refl , q) N⇓▹)
small¹-big            {Q}  β-𝓅⁰            N⇓▹ = ⇉𝓅 {Q = Q} (▹map (λ q → 0 , refl , q) N⇓▹)
small¹-big            {Q} (β-𝓅ˢ {n})       N⇓▹ = ⇉𝓅 {Q = Q} (▹map (λ q → suc n , refl , q) N⇓▹)
small¹-big                (β-?⁰ {N})        N⇓▹ = ⇉Q?0 {t = N} N⇓▹
small¹-big                (β-?ˢ {M} {n})    N⇓▹ = ⇉Q?s {s = M} {n = n} N⇓▹
small¹-big                (ξ-· s)           N⇓▹ = small¹-big s N⇓▹
small¹-big {k = zero} {Q} (ξ-𝓈 s)           N⇓▹ = ⇉𝓈 {Q = Q} (▹map (λ x → absurd x) N⇓▹)
small¹-big {suc k}    {Q} (ξ-𝓈 s)           N⇓▹ = ⇉𝓈 {Q = Q} (▹map (small¹-big s ∘ 𝓈⇉ {Q = Q}) N⇓▹)
small¹-big {k = zero} {Q} (ξ-𝓅 s)           N⇓▹ = ⇉𝓅 {Q = Q} (▹map (λ x → absurd x) N⇓▹)
small¹-big {suc k}    {Q} (ξ-𝓅 s)           N⇓▹ = ⇉𝓅 {Q = Q} (▹map (small¹-big s ∘ 𝓅⇉ {Q = Q}) N⇓▹)
small¹-big                (ξ-? s)           N⇓▹ = small¹-big s N⇓▹

-- 2.6

small-rtc-big : ∀ {k M N} (Q : Val → ℕ → 𝒰)
              → M —↠⁰ N
              → N ⇓⁅ k ⁆ Q
              → M ⇓⁅ k ⁆ Q
small-rtc-big {M} Q (.M ∎ᵣ)        N⇓ = N⇓
small-rtc-big {M} Q (.M —→⟨ s ⟩ r) N⇓ =
  small⁰-big s (small-rtc-big Q r N⇓)

small-rtc-big-v : ∀ {k M N} (V : Val)
                → M —↠⁰ N
                → N ⇓⁅ k ⁆ᵛ V
                → M ⇓⁅ k ⁆ᵛ V
small-rtc-big-v V = small-rtc-big (λ v l → (l ＝ 0) × (v ＝ V))

-- 2.7
-- we define it as a typelevel function by induction on k to work around size issues
_⇛⁅_⁆_ : Term → ℕ → (Term → ℕ → 𝒰) → 𝒰
M ⇛⁅ zero ⁆  Q =  Σ[ N ꞉ Term ] (M —↠⁰ N) × Q N 0
M ⇛⁅ suc k ⁆ Q = (Σ[ N ꞉ Term ] (M —↠⁰ N) × Q N (suc k))
               ⊎ (Σ[ M′ ꞉ Term ] (Σ[ M″ ꞉ Term ] (M —↠⁰ M′) × (M′ —→⁅ s¹ ⁆ M″) × (▹ (M″ ⇛⁅ k ⁆ Q))))

-- constructors

⇛ᵏ : ∀ {k M N Q}
   → M —↠⁰ N → Q N k
     ----------------
   → M ⇛⁅ k ⁆ Q
⇛ᵏ {k = zero}  {N} MN QN = N , MN , QN
⇛ᵏ {k = suc k} {N} MN QN = inl (N , MN , QN)

⇛ˢ : ∀ {k M M′ M″ Q}
   → M —↠⁰ M′ → M′ —→⁅ s¹ ⁆ M″ → ▹ (M″ ⇛⁅ k ⁆ Q)
     ------------------------------------------
   → M ⇛⁅ suc k ⁆ Q
⇛ˢ {M′} {M″} MM′ MM″ MQ▹ = inr (M′ , M″ , MM′ , MM″ , MQ▹)

-- TODO define ⇛-elim to remove duplication for the k case

⇛-covariant : ∀ {k M Q R}
            → (∀ v n → Q v n → R v n)
            → M ⇛⁅ k ⁆ Q
            → M ⇛⁅ k ⁆ R
⇛-covariant {k = zero} {R} qr (N , MN , QN)                = ⇛ᵏ {Q = R} MN (qr N 0 QN)
⇛-covariant {suc k}    {R} qr (inl (N , MN , QN))          = ⇛ᵏ {Q = R} MN (qr N (suc k) QN)
⇛-covariant {suc k}        qr (inr (N , S , MN , NS , Q▹)) = ⇛ˢ MN NS (▹map (⇛-covariant qr) Q▹)

-- 2.8

small-rtc-inter : ∀ {k M N Q}
                → M —↠⁰ N
                → N ⇛⁅ k ⁆ Q
                → M ⇛⁅ k ⁆ Q
small-rtc-inter {k = zero} {Q} MN (P , NP , qP)                 = ⇛ᵏ {Q = Q} (MN —↠⁰∘ NP) qP
small-rtc-inter {suc k}        MN (inl (P , NP , qP))           = ⇛ᵏ         (MN —↠⁰∘ NP) qP
small-rtc-inter {suc k}        MN (inr (R , S , NR , RS , SQ▹)) = ⇛ˢ (MN —↠⁰∘ NR) RS SQ▹

-- 2.9

inter-comp : ∀ {k M Q}
           → M ⇛⁅ k ⁆ (λ L n → L ⇛⁅ n ⁆ Q)
           → M ⇛⁅ k ⁆ Q
inter-comp {k = zero}  {Q} (N , MN , qN)                 =
  small-rtc-inter {Q = Q} MN qN
inter-comp {k = suc k}     (inl (N , MN , qN))           =
  small-rtc-inter          MN qN
inter-comp {k = suc k}     (inr (N , P , NP , PS , SQ▹)) =
  ⇛ˢ NP PS (▹map inter-comp SQ▹)

-- 2.10

Qᴱ : (Term → Term) → (Term → ℕ → 𝒰) → Term → ℕ → 𝒰
Qᴱ f Q T m = Σ[ M ꞉ Term ] (T ＝ f M) × Q M m

inter-· : ∀ {k M N Q}
        → M ⇛⁅ k ⁆ Q
        → (M · N) ⇛⁅ k ⁆ (Qᴱ (_· N) Q)
inter-· {k = zero}  {N} {Q} (P , MP , qP)                 =
  ⇛ᵏ {Q = Qᴱ (_· N) Q} (—↠⁰-· MP) (P , refl , qP)
inter-· {k = suc k}         (inl (P , MP , qP))           =
  ⇛ᵏ                   (—↠⁰-· MP) (P , refl , qP)
inter-· {k = suc k}         (inr (R , S , MR , RS , SQ▹)) =
  ⇛ˢ (—↠⁰-· MR) (ξ-· RS) (▹map inter-· SQ▹)

inter-𝓈 : ∀ {k M Q}
        → M ⇛⁅ k ⁆ Q
        → (𝓈 M) ⇛⁅ k ⁆ (Qᴱ 𝓈 Q)
inter-𝓈 {k = zero}  {Q} (N , MN , qN)                 =
  ⇛ᵏ {Q = Qᴱ 𝓈 Q} (—↠⁰-𝓈 MN) (N , refl , qN)
inter-𝓈 {k = suc k}     (inl (N , MN , qN))           =
  ⇛ᵏ             (—↠⁰-𝓈 MN) (N , refl , qN)
inter-𝓈 {k = suc k}     (inr (N , P , MN , NP , SQ▹)) =
  ⇛ˢ (—↠⁰-𝓈 MN) (ξ-𝓈 NP) (▹map inter-𝓈 SQ▹)

inter-𝓅 : ∀ {k M Q}
        → M ⇛⁅ k ⁆ Q
        → (𝓅 M) ⇛⁅ k ⁆ (Qᴱ 𝓅 Q)
inter-𝓅 {k = zero}  {Q} (N , MN , qN)                 =
  ⇛ᵏ {Q = Qᴱ 𝓅 Q} (—↠⁰-𝓅 MN) (N , refl , qN)
inter-𝓅 {k = suc k}     (inl (N , MN , qN))           =
  ⇛ᵏ              (—↠⁰-𝓅 MN) (N , refl , qN)
inter-𝓅 {k = suc k}     (inr (N , P , MN , NP , SQ▹)) =
  ⇛ˢ (—↠⁰-𝓅 MN) (ξ-𝓅 NP) (▹map inter-𝓅 SQ▹)

inter-? : ∀ {k L M N Q}
        → L ⇛⁅ k ⁆ Q
        → (?⁰ L ↑ M ↓ N) ⇛⁅ k ⁆ (Qᴱ (λ q → ?⁰ q ↑ M ↓ N) Q)
inter-? {k = zero}  {M} {N} {Q} (P , LP , qP)                 =
  ⇛ᵏ {Q = Qᴱ (λ q → ?⁰ q ↑ M ↓ N) Q} (—↠⁰-? LP) (P , refl , qP)
inter-? {k = suc k}             (inl (P , LP , qP))           =
  ⇛ᵏ                                 (—↠⁰-? LP) (P , refl , qP)
inter-? {k = suc k}             (inr (R , S , LR , RS , SQ▹)) =
  ⇛ˢ (—↠⁰-? LR) (ξ-? RS) (▹map inter-? SQ▹)

-- 2.11

inter-big-comp : ∀ {k M Q}
          → M ⇛⁅ k ⁆ (λ N z → N ⇓⁅ z ⁆ Q)
          → M ⇓⁅ k ⁆ Q
inter-big-comp {k = zero}  {Q} (P , LP , qP)                 =
  small-rtc-big Q LP qP
inter-big-comp {k = suc k} {Q} (inl (P , LP , qP))           =
  small-rtc-big Q LP qP
inter-big-comp {k = suc k} {Q} (inr (R , S , LR , RS , SQ▹)) =
  small-rtc-big Q LR (small¹-big RS (▹map inter-big-comp SQ▹))

-- 2.12

Q𝓈-covariant : ∀ {Q R}
             → (∀ v n → Q v n → R v n)
             → ∀ v n → Q𝓈 Q v n → Q𝓈 R v n
Q𝓈-covariant qr v n (x , e , qx) = x , e , qr (v-＃ (suc x)) n qx

Q𝓅-covariant : ∀ {Q R}
             → (∀ v n → Q v n → R v n)
             → ∀ v n → Q𝓅 Q v n → Q𝓅 R v n
Q𝓅-covariant qr v n (x , e , qx) = x , e , qr (v-＃ (pred x)) n qx

cov-distr : ▹ (  (Q R : Val → ℕ → 𝒰) → (∀ v n → Q v n → R v n)
                      → (M : Term) → (k : ℕ)
                      → M ⇓⁅ k ⁆ Q → M ⇓⁅ k ⁆ R)
          → (Q R : Val → ℕ → 𝒰) → (∀ v n → Q v n → R v n)
          → (M : Term) → (k : ℕ)
          → ▹ (M ⇓⁅ k ⁆ Q → M ⇓⁅ k ⁆ R)
cov-distr cb▹ Q R qr M k = cb▹ ⊛ next Q ⊛ next R ⊛ next qr
                               ⊛ next M ⊛ next k

Q·-covariant-rec : (  (Q R : Val → ℕ → 𝒰) → (∀ v n → Q v n → R v n)
                    → (M : Term) → (k : ℕ)
                    → ▹ (M ⇓⁅ k ⁆ Q → M ⇓⁅ k ⁆ R))
                 → (Q R : Val → ℕ → 𝒰) → (∀ v n → Q v n → R v n)
                 → (s : Term) → (v : Val) → (n : ℕ)
                 → Q· s Q v n → Q· s R v n
Q·-covariant-rec cb▹ Q R qr s (v-ƛ x A t) (suc n) qq =
  ⇉Q· {t} {x} {s} {A}
      (cb▹ Q R qr (t [ x := s ]) n
        ⊛ Q·⇉ {t} {x} {A} {s} qq)

Q?-covariant-rec : (  (Q R : Val → ℕ → 𝒰) → (∀ v n → Q v n → R v n)
                    → (M : Term) → (k : ℕ)
                    → ▹ (M ⇓⁅ k ⁆ Q → M ⇓⁅ k ⁆ R))
                 → (Q R : Val → ℕ → 𝒰) → (∀ v n → Q v n → R v n)
                 → (s t : Term) → (v : Val) → (n : ℕ)
                 → Q? s t Q v n → Q? s t R v n
Q?-covariant-rec cb▹ Q R qr s t (v-＃ zero)    (suc n) qq =
  ⇉Q?0 {s} {t}
       (cb▹ Q R qr s n
          ⊛ Q?0⇉ {s} {t} qq)
Q?-covariant-rec cb▹ Q R qr s t (v-＃ (suc m)) (suc n) qq =
  ⇉Q?s {s} {t} {m = n} {n = m}
       (cb▹ Q R qr t n
          ⊛ Q?s⇉ {s} {t} {m = n} {n = m} qq)

⇓-covariant-body : (  (Q R : Val → ℕ → 𝒰) → (∀ v n → Q v n → R v n)
                    → (M : Term) → (k : ℕ)
                    → ▹ (M ⇓⁅ k ⁆ Q → M ⇓⁅ k ⁆ R))
                 → (Q R : Val → ℕ → 𝒰) → (∀ v n → Q v n → R v n)
                 → (M : Term) → (k : ℕ)
                 → M ⇓⁅ k ⁆ Q → M ⇓⁅ k ⁆ R
⇓-covariant-body cb▹ Q R qr (ƛ x ⦂ A ⇒ t)       k      M⇓ =
  qr (v-ƛ x A t) k M⇓
⇓-covariant-body cb▹ Q R qr (r · s)            k      M⇓ =
  ⇓-covariant-body cb▹ (Q· s Q) (Q· s R) (Q·-covariant-rec cb▹ Q R qr s) r k M⇓
⇓-covariant-body cb▹ Q R qr (Y t)          (suc k) M⇓ =
  ⇉Y (cb▹ Q R qr (t · Y t) k
        ⊛ Y⇉ M⇓)
⇓-covariant-body cb▹ Q R qr (＃ n)           k     M⇓ =
  qr (v-＃ n) k M⇓
⇓-covariant-body cb▹ Q R qr (𝓈 t)          (suc k) M⇓ =
  ⇉𝓈 {Q = R} (cb▹ (Q𝓈 Q) (Q𝓈 R) (Q𝓈-covariant qr) t k
                ⊛ 𝓈⇉ {Q = Q} M⇓)
⇓-covariant-body cb▹ Q R qr (𝓅 t)          (suc k) M⇓ =
  ⇉𝓅 {Q = R} (cb▹ (Q𝓅 Q) (Q𝓅 R) (Q𝓅-covariant qr) t k
                ⊛ 𝓅⇉ {Q = Q} M⇓)
⇓-covariant-body cb▹ Q R qr (?⁰ r ↑ s ↓ t)  k      M⇓ =
  ⇓-covariant-body cb▹ (Q? s t Q) (Q? s t R) (Q?-covariant-rec cb▹ Q R qr s t) r k M⇓

⇓-covariant : (Q R : Val → ℕ → 𝒰) → (∀ v n → Q v n → R v n)
            → (M : Term) → (k : ℕ)
            → M ⇓⁅ k ⁆ Q → M ⇓⁅ k ⁆ R
⇓-covariant = fix (⇓-covariant-body ∘ cov-distr)

-- 2.13.1

Qᵀ : (Val → ℕ → 𝒰)
   → Term → ℕ → 𝒰
Qᵀ Q N k = Σ[ v ꞉ Val ] IsVal N v × Q v k

Qᵀ⁰ : (Val → 𝒰)
   → Term → 𝒰
Qᵀ⁰ Q N = Σ[ v ꞉ Val ] IsVal N v × Q v

Qᵀ-impl : (Q : Val → ℕ → 𝒰)
        → (N : Term) → (k : ℕ)
        → Qᵀ Q N k → N ⇓⁅ k ⁆ Q
Qᵀ-impl Q (ƛ x ⦂ A ⇒ t) k (.(v-ƛ x A t) , is-ƛ , q) = q
Qᵀ-impl Q (＃ n)        k (.(v-＃ n)    , is-＃ , q) = q

-- TODO looks like Q₂ and Q₃ can be merged in all cases
big→inter-body :
               ▹ (∀ k M Q → M ⇓⁅ k ⁆ Q → M ⇛⁅ k ⁆ Qᵀ Q)
               →  ∀ k M Q → M ⇓⁅ k ⁆ Q → M ⇛⁅ k ⁆ Qᵀ Q
big→inter-body ih▹  k      (ƛ x ⦂ A ⇒ M)   Q M⇓ =
  ⇛ᵏ (ƛ x ⦂ A ⇒ M ∎ᵣ) (v-ƛ x A M , is-ƛ , M⇓)
big→inter-body ih▹  k      (M · N)        Q M⇓ = {!!}
big→inter-body ih▹ (suc k) (Y M)          Q M⇓ =
  ⇛ˢ (Y M ∎ᵣ) Ｙ (▹map (big→inter-body ih▹ k (M · Y M) Q) (Y⇉ M⇓))
big→inter-body ih▹  k      (＃ n)          Q M⇓ =
  ⇛ᵏ (＃ n ∎ᵣ) (v-＃ n , is-＃ , M⇓)
big→inter-body ih▹  k      (𝓈 M)          Q M⇓ = {!!}
big→inter-body ih▹  k      (𝓅 M)          Q M⇓ = {!!}
big→inter-body ih▹  k      (?⁰ L ↑ M ↓ N) Q M⇓ = {!!}

big→inter : (k : ℕ) (M : Term) (Q : Val → ℕ → 𝒰)
          → M ⇓⁅ k ⁆ Q
          → M ⇛⁅ k ⁆ (Qᵀ Q)
big→inter = fix big→inter-body

-- 2.13.2

inter→big : ∀ {k M Q}
          → M ⇛⁅ k ⁆ (Qᵀ Q)
          → M ⇓⁅ k ⁆ Q
inter→big {Q} = inter-big-comp ∘ ⇛-covariant go
  where
  go : ∀ v n → Qᵀ Q v n → v ⇓⁅ n ⁆ Q
  go .(＃ _)        n (.(v-＃ _  )  , is-＃ , q) = q
  go .(ƛ _ ⦂ _ ⇒ _) n (.(v-ƛ _ _ _) , is-ƛ , q) = q

-- 2.14.1

Q⁰ : (Term → 𝒰) → Term → ℕ → 𝒰
Q⁰ Q N k = (k ＝ 0) × Q N

inter→small-rtc : ∀ {k M Q}
                → M ⇛⁅ k ⁆ Q⁰ Q
                → M =⇒⁅ k ⁆ Q
inter→small-rtc {k = zero}  (N , MN , _ , QN)             =
  N , MN , QN
inter→small-rtc {k = suc k} (inl (N , MN , e , _))        =
  absurd (suc≠zero e)
inter→small-rtc {k = suc k} (inr (N , R , MN , NR , QR▹)) =
  N , R , MN , NR , ▹map inter→small-rtc QR▹

-- 2.14.2

small-rtc→inter : ∀ {k M Q}
                → M =⇒⁅ k ⁆ Q
                → M ⇛⁅ k ⁆ Q⁰ Q
small-rtc→inter {k = zero } {Q} (N , MN , QN)           = ⇛ᵏ {Q = Q⁰ Q} MN (refl , QN)
small-rtc→inter {k = suc k}     (N , R , MN , NR , QR▹) = ⇛ˢ MN NR (▹map small-rtc→inter QR▹)

-- 2.3.1

big→small-rtc : ∀ {k M Q}
              → M ⇓⁅ k ⁆⁰ Q
              → M =⇒⁅ k ⁆ (Qᵀ⁰ Q)
big→small-rtc {k} {M} {Q} M⇓ =
  inter→small-rtc $
  ⇛-covariant go $
  big→inter k M (λ v l → (l ＝ 0) × (Q v)) M⇓
  where
  go : ∀ v n → Qᵀ (λ w l → (l ＝ 0) × Q w) v n → Q⁰ (Qᵀ⁰ Q) v n
  go v n (w , iw , n0 , qw) = n0 , w , iw , qw

-- 2.3.2

small-rtc→big : ∀ {k M Q}
              → M =⇒⁅ k ⁆ (Qᵀ⁰ Q)
              → M ⇓⁅ k ⁆⁰ Q
small-rtc→big {Q} = inter→big ∘ ⇛-covariant go ∘ small-rtc→inter
  where
  go : ∀ v n → Q⁰ (Qᵀ⁰ Q) v n → Qᵀ (λ w l → (l ＝ 0) × Q w) v n
  go v n (n0 , w , iw , qw) = w , iw , n0 , qw

-- 2.4.1

big→small-rtc-v : ∀ {k M N V}
                → IsVal N V
                → M ⇓⁅ k ⁆ᵛ V
                → M =⇒⁅ k ⁆ᵗ N
big→small-rtc-v {N} {V} iV = =⇒-covariant go ∘ big→small-rtc
  where
  go : ∀ T → Qᵀ⁰ (_＝ V) T → T ＝ N
  go T (W , iW , e) = IsVal-unique T N V (subst (IsVal T) e iW) iV

-- 2.4.2

small-rtc→big-v : ∀ {k M N V}
                → IsVal N V
                → M =⇒⁅ k ⁆ᵗ N
                → M ⇓⁅ k ⁆ᵛ V
small-rtc→big-v {N} {V} iV = small-rtc→big ∘ =⇒-covariant go
  where
  go : ∀ T → T ＝ N → Qᵀ⁰ (_＝ V) T
  go T e = V , subst (λ q → IsVal q V) (sym e) iV , refl

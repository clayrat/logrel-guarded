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
small⁰-big (ξ-· s) N⇓ = small⁰-big s N⇓
small⁰-big (ξ-𝓈 s) N⇓ = small⁰-big s N⇓
small⁰-big (ξ-𝓅 s) N⇓ = small⁰-big s N⇓
small⁰-big (ξ-? s) N⇓ = small⁰-big s N⇓

-- 2.5.2

small¹-big : ∀ {k M N Q}
           → M —→⁅ s¹ ⁆ N
           → ▹ (N ⇓⁅ k ⁆ Q)
           → M ⇓⁅ suc k ⁆ Q
small¹-big (β-ƛ {M} {N} {A}) N⇓▹ = ⇉Q· {t = M} {s = N} {A = A} N⇓▹
small¹-big  Ｙ               N⇓▹ = ⇉Y N⇓▹
small¹-big (β-𝓈 {n})         N⇓▹ = N⇓▹
small¹-big  β-𝓅⁰            N⇓▹ = N⇓▹
small¹-big (β-𝓅ˢ {n})       N⇓▹ = N⇓▹
small¹-big (β-?⁰ {N})        N⇓▹ = ⇉Q?0 {t = N} N⇓▹
small¹-big (β-?ˢ {M} {n})    N⇓▹ = ⇉Q?s {s = M} {n = n} N⇓▹
small¹-big (ξ-· s)           N⇓▹ = small¹-big s N⇓▹
small¹-big (ξ-𝓈 s)           N⇓▹ = small¹-big s N⇓▹
small¹-big (ξ-𝓅 s)           N⇓▹ = small¹-big s N⇓▹
small¹-big (ξ-? s)           N⇓▹ = small¹-big s N⇓▹

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

small-rtc-inter1 : ∀ {k M N Q}
                → M —→⁅ s¹ ⁆ N
                → ▹ (N ⇛⁅ k ⁆ Q)
                → M ⇛⁅ suc k ⁆ Q
small-rtc-inter1 {M} MN NQ▹ = ⇛ˢ (M ∎ᵣ) MN NQ▹

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
Q𝓈-covariant qr (v-＃ x) (suc n) = ▹map (qr (v-＃ (suc x)) n)

Q𝓅-covariant : ∀ {Q R}
             → (∀ v n → Q v n → R v n)
             → ∀ v n → Q𝓅 Q v n → Q𝓅 R v n
Q𝓅-covariant qr (v-＃ x) (suc n) = ▹map (qr (v-＃ (pred x)) n)

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
⇓-covariant-body cb▹ Q R qr (𝓈 t)           k      M⇓ =
  ⇓-covariant-body cb▹ (Q𝓈 Q) (Q𝓈 R) (Q𝓈-covariant qr) t k M⇓
⇓-covariant-body cb▹ Q R qr (𝓅 t)           k      M⇓ =
  ⇓-covariant-body cb▹ (Q𝓅 Q) (Q𝓅 R) (Q𝓅-covariant qr) t k M⇓
⇓-covariant-body cb▹ Q R qr (?⁰ r ↑ s ↓ t)  k      M⇓ =
  ⇓-covariant-body cb▹ (Q? s t Q) (Q? s t R) (Q?-covariant-rec cb▹ Q R qr s t) r k M⇓

⇓-covariant-exp : (Q R : Val → ℕ → 𝒰) → (∀ v n → Q v n → R v n)
                → (M : Term) → (k : ℕ)
                → M ⇓⁅ k ⁆ Q → M ⇓⁅ k ⁆ R
⇓-covariant-exp = fix (⇓-covariant-body ∘ cov-distr)

⇓-covariant : ∀ {k Q R M}
            → (∀ v n → Q v n → R v n)
            → M ⇓⁅ k ⁆ Q → M ⇓⁅ k ⁆ R
⇓-covariant {k} {Q} {R} {M} qr = ⇓-covariant-exp Q R qr M k

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

big→inter-body :
               ▹ (∀ k M Q → M ⇓⁅ k ⁆ Q → M ⇛⁅ k ⁆ Qᵀ Q)
               →  ∀ k M Q → M ⇓⁅ k ⁆ Q → M ⇛⁅ k ⁆ Qᵀ Q
big→inter-body ih▹  k      (ƛ x ⦂ A ⇒ M)   Q M⇓ =
  ⇛ᵏ (ƛ x ⦂ A ⇒ M ∎ᵣ) (v-ƛ x A M , is-ƛ , M⇓)
big→inter-body ih▹  k      (M · N)        Q M⇓ =
  inter-comp $
  ⇛-covariant Q₄i $
  ⇛-covariant Q₃₄ $
  inter-· {N = N} $
  big→inter-body ih▹ k M Q₃ $
  ⇓-covariant {k = k} {M = M} Q₂₃-impl $
  ⇓-covariant {k = k} {M = M} Q·₂-impl M⇓
  where
  Q₂ : Val → ℕ → 𝒰
  Q₂ (v-＃ _)     _      = ⊥
  Q₂ (v-ƛ _ _ _)  zero   = ⊥
  Q₂ (v-ƛ x _ t) (suc m) = ▹ ((t [ x := N ]) ⇛⁅ m ⁆ Qᵀ Q)

  Q·₂-impl : ∀ v n → Q· N Q v n → Q₂ v n
  Q·₂-impl (v-ƛ x A t) (suc n) qq =
    ih▹ ⊛ next n ⊛ next (t [ x := N ]) ⊛ next Q ⊛ Q·⇉ {t} {x} {A} {N} qq

  Q₃ : Val → ℕ → 𝒰
  Q₃ (v-＃ _)     _ = ⊥
  Q₃ (v-ƛ x A t)  m = ((ƛ x ⦂ A ⇒ t) · N) ⇛⁅ m ⁆ Qᵀ Q

  Q₂₃-impl : ∀ v n → Q₂ v n → Q₃ v n
  Q₂₃-impl (v-ƛ x A t) (suc n) = small-rtc-inter1 β-ƛ

  Q₄ : Term → ℕ → 𝒰
  Q₄ (` _)                _ = ⊥
  Q₄ (ƛ _ ⦂ _ ⇒ _)        _ = ⊥
  Q₄ (` _ · _)            _ = ⊥
  Q₄ ((ƛ x ⦂ A ⇒ r) · s)  m = ((ƛ x ⦂ A ⇒ r) · s) ⇛⁅ m ⁆ Qᵀ Q
  Q₄ (_ · _ · _)          _ = ⊥
  Q₄ (Y _ · _)            _ = ⊥
  Q₄ (＃ _ · _)           _ = ⊥
  Q₄ (𝓈 _ · _)            _ = ⊥
  Q₄ (𝓅 _ · _)            _ = ⊥
  Q₄ ((?⁰ _ ↑ _ ↓ _) · s) _ = ⊥
  Q₄ (Y _)                _ = ⊥
  Q₄ (＃ _)               _ = ⊥
  Q₄ (𝓈 _)                _ = ⊥
  Q₄ (𝓅 _)                _ = ⊥
  Q₄ (?⁰ _ ↑ _ ↓ _)       _ = ⊥

  Q₃₄ : ∀ T n → Qᴱ (_· N) (Qᵀ Q₃) T n → Q₄ T n
  Q₃₄ T n (.(ƛ x ⦂ A ⇒ t) , er , .(v-ƛ x A t) , is-ƛ {x} {A} {t} , qq) =
    subst (λ q → Q₄ q n) (sym er) qq

  Q₄i : ∀ v n → Q₄ v n → v ⇛⁅ n ⁆ Qᵀ Q
  Q₄i ((ƛ x ⦂ A ⇒ t) · s) n qq = qq

big→inter-body ih▹ (suc k) (Y M)          Q M⇓ =
  small-rtc-inter1 Ｙ (ih▹ ⊛ next k ⊛ next (M · Y M) ⊛ next Q ⊛ (Y⇉ M⇓))

big→inter-body ih▹  k      (＃ n)          Q M⇓ =
  ⇛ᵏ (＃ n ∎ᵣ) (v-＃ n , is-＃ , M⇓)

big→inter-body ih▹  k      (𝓈 M)          Q M⇓ =
  inter-comp $
  ⇛-covariant Q₄i $
  ⇛-covariant Q₃₄ $
  inter-𝓈 $
  big→inter-body ih▹ k M Q₃ $
  ⇓-covariant {k = k} {M = M} Q₂₃-impl $
  ⇓-covariant {k = k} {M = M} Q𝓈₂-impl M⇓
  where
  Q₂ : Val → ℕ → 𝒰
  Q₂ (v-＃ n)     zero    = ⊥
  Q₂ (v-＃ n)    (suc m) = ▹ ((＃ (suc n)) ⇛⁅ m ⁆ Qᵀ Q)
  Q₂ (v-ƛ _ _ _)  _      = ⊥

  Q𝓈₂-impl : ∀ v s → Q𝓈 Q v s → Q₂ v s
  Q𝓈₂-impl (v-＃ x) (suc s) q▹ = ih▹ ⊛ next s ⊛ next (＃ (suc x)) ⊛ next Q ⊛ q▹

  Q₃ : Val → ℕ → 𝒰
  Q₃ (v-＃ n)    m = (𝓈 (＃ n)) ⇛⁅ m ⁆ Qᵀ Q
  Q₃ (v-ƛ x A t) m = ⊥

  Q₂₃-impl : ∀ v n → Q₂ v n → Q₃ v n
  Q₂₃-impl (v-＃ m) (suc n) = small-rtc-inter1 β-𝓈

  Q₄ : Term → ℕ → 𝒰
  Q₄ (` _)             _ = ⊥
  Q₄ (ƛ _ ⦂ _ ⇒ _)      _ = ⊥
  Q₄ (_ · _)            _ = ⊥
  Q₄ (Y _)              _ = ⊥
  Q₄ (＃ _)             _ = ⊥
  Q₄ (𝓈 (` _))          _ = ⊥
  Q₄ (𝓈 (ƛ _ ⦂ _ ⇒ _))  _ = ⊥
  Q₄ (𝓈 (_ · _))        _ = ⊥
  Q₄ (𝓈 (Y _))          _ = ⊥
  Q₄ (𝓈 (＃ n))         m = 𝓈 (＃ n) ⇛⁅ m ⁆ Qᵀ Q
  Q₄ (𝓈 (𝓈 _))          _ = ⊥
  Q₄ (𝓈 (𝓅 _))          _ = ⊥
  Q₄ (𝓈 (?⁰ _ ↑ _ ↓ _)) _ = ⊥
  Q₄ (𝓅 _)              _ = ⊥
  Q₄ (?⁰ _ ↑ _ ↓ _)     _ = ⊥

  Q₃₄ : ∀ t n → Qᴱ 𝓈 (Qᵀ Q₃) t n → Q₄ t n
  Q₃₄ t1 n (.(＃ m) , e , .(v-＃ m) , is-＃ {n = m} , qq) =
    subst (λ q → Q₄ q n) (sym e) qq

  Q₄i : ∀ v n → Q₄ v n → v ⇛⁅ n ⁆ Qᵀ Q
  Q₄i (𝓈 (＃ m)) n qq = qq

big→inter-body ih▹  k      (𝓅 M)          Q M⇓ =
  inter-comp $
  ⇛-covariant Q₄i $
  ⇛-covariant Q₃₄ $
  inter-𝓅 $
  big→inter-body ih▹ k M Q₃ $
  ⇓-covariant {k = k} {M = M} Q₂₃-impl $
  ⇓-covariant {k = k} {M = M} Q𝓅₂-impl M⇓
  where
  Q₂ : Val → ℕ → 𝒰
  Q₂ (v-＃ n)     zero    = ⊥
  Q₂ (v-＃ n)    (suc m) = ▹ ((＃ (pred n)) ⇛⁅ m ⁆ Qᵀ Q)
  Q₂ (v-ƛ _ _ _)  _      = ⊥

  Q𝓅₂-impl : ∀ v s → Q𝓅 Q v s → Q₂ v s
  Q𝓅₂-impl (v-＃ x) (suc s) q▹ = ih▹ ⊛ next s ⊛ next (＃ (pred x)) ⊛ next Q ⊛ q▹

  Q₃ : Val → ℕ → 𝒰
  Q₃ (v-＃ n)    m = (𝓅 (＃ n)) ⇛⁅ m ⁆ Qᵀ Q
  Q₃ (v-ƛ x A t) m = ⊥

  Q₂₃-impl : ∀ v n → Q₂ v n → Q₃ v n
  Q₂₃-impl (v-＃ zero)    (suc n) = small-rtc-inter1 β-𝓅⁰
  Q₂₃-impl (v-＃ (suc m)) (suc n) = small-rtc-inter1 β-𝓅ˢ

  Q₄ : Term → ℕ → 𝒰
  Q₄ (` _)             _ = ⊥
  Q₄ (ƛ _ ⦂ _ ⇒ _)      _ = ⊥
  Q₄ (_ · _)            _ = ⊥
  Q₄ (Y _)              _ = ⊥
  Q₄ (＃ _)             _ = ⊥
  Q₄ (𝓈 _)              _ = ⊥
  Q₄ (𝓅 (` _))          _ = ⊥
  Q₄ (𝓅 (ƛ _ ⦂ _ ⇒ _))  _ = ⊥
  Q₄ (𝓅 (_ · _))        _ = ⊥
  Q₄ (𝓅 (Y _))          _ = ⊥
  Q₄ (𝓅 (＃ n))         m = 𝓅 (＃ n) ⇛⁅ m ⁆ Qᵀ Q
  Q₄ (𝓅 (𝓈 _))          _ = ⊥
  Q₄ (𝓅 (𝓅 _))          _ = ⊥
  Q₄ (𝓅 (?⁰ _ ↑ _ ↓ _)) _ = ⊥
  Q₄ (?⁰ _ ↑ _ ↓ _)     _ = ⊥

  Q₃₄ : ∀ t n → Qᴱ 𝓅 (Qᵀ Q₃) t n → Q₄ t n
  Q₃₄ t1 n (.(＃ m) , e , .(v-＃ m) , is-＃ {n = m} , qq) =
    subst (λ q → Q₄ q n) (sym e) qq

  Q₄i : ∀ v n → Q₄ v n → v ⇛⁅ n ⁆ Qᵀ Q
  Q₄i (𝓅 (＃ m)) n qq = qq

big→inter-body ih▹  k      (?⁰ L ↑ M ↓ N) Q M⇓ =
   inter-comp $
   ⇛-covariant Q₄i $
   ⇛-covariant Q₃₄ $
   inter-? {M = M} {N = N} $
   big→inter-body ih▹ k L Q₃ $
   ⇓-covariant {k = k} {M = L} Q₂₃-impl $
   ⇓-covariant {k = k} {M = L} Q?₂-impl M⇓
  where
  Q₂ : Val → ℕ → 𝒰
  Q₂ (v-＃  _)       zero   = ⊥
  Q₂ (v-＃  zero)   (suc m) = ▹ (M ⇛⁅ m ⁆ Qᵀ Q)
  Q₂ (v-＃ (suc _)) (suc m) = ▹ (N ⇛⁅ m ⁆ Qᵀ Q)
  Q₂ (v-ƛ _ _ _)     _      = ⊥

  Q?₂-impl : ∀ v n → Q? M N Q v n → Q₂ v n
  Q?₂-impl (v-＃  zero)   (suc n) qq = ih▹ ⊛ next n ⊛ next M ⊛ next Q ⊛ Q?0⇉ {t = N} qq
  Q?₂-impl (v-＃ (suc m)) (suc n) qq = ih▹ ⊛ next n ⊛ next N ⊛ next Q ⊛ Q?s⇉ {s = M} {n = m} qq

  Q₃ : Val → ℕ → 𝒰
  Q₃ (v-＃ n)    m = (?⁰ (＃ n) ↑ M ↓ N) ⇛⁅ m ⁆ Qᵀ Q
  Q₃ (v-ƛ _ _ _) m = ⊥

  Q₂₃-impl : ∀ v n → Q₂ v n → Q₃ v n
  Q₂₃-impl (v-＃ zero)    (suc n) = small-rtc-inter1 β-?⁰
  Q₂₃-impl (v-＃ (suc _)) (suc n) = small-rtc-inter1 β-?ˢ

  Q₄ : Term → ℕ → 𝒰
  Q₄ (` _)                     _ = ⊥
  Q₄ (ƛ _ ⦂ _ ⇒ _)              _ = ⊥
  Q₄ (_ · _)                   _ = ⊥
  Q₄ (Y _)                     _ = ⊥
  Q₄ (＃ _)                    _ = ⊥
  Q₄ (𝓈 _)                     _ = ⊥
  Q₄ (𝓅 _)                     _ = ⊥
  Q₄ (?⁰ ` _ ↑ _ ↓ _)          _ = ⊥
  Q₄ (?⁰ ƛ _ ⦂ _ ⇒ _ ↑ _ ↓ _)  _ = ⊥
  Q₄ (?⁰ _ · _ ↑ _ ↓ _)        _ = ⊥
  Q₄ (?⁰ Y _ ↑ _ ↓ _)          _ = ⊥
  Q₄ (?⁰ ＃ n ↑ s ↓ t)         m = (?⁰ ＃ n ↑ s ↓ t) ⇛⁅ m ⁆ Qᵀ Q
  Q₄ (?⁰ 𝓈 _ ↑ _ ↓ _)          _ = ⊥
  Q₄ (?⁰ 𝓅 _ ↑ _ ↓ _)          _ = ⊥
  Q₄ (?⁰ ?⁰ _ ↑ _ ↓ _ ↑ _ ↓ _) _ = ⊥

  Q₃₄ : ∀ p n → Qᴱ (λ q → ?⁰ q ↑ M ↓ N) (Qᵀ Q₃) p n → Q₄ p n
  Q₃₄ p n (.(＃ m) , e , .(v-＃ m) , is-＃ {n = m} , qq) = subst (λ q → Q₄ q n) (sym e) qq

  Q₄i : ∀ v n → Q₄ v n → v ⇛⁅ n ⁆ Qᵀ Q
  Q₄i (?⁰ ＃ p ↑ s ↓ t) n qq = qq

big→inter-exp : (k : ℕ) (M : Term) (Q : Val → ℕ → 𝒰)
          → M ⇓⁅ k ⁆ Q
          → M ⇛⁅ k ⁆ (Qᵀ Q)
big→inter-exp = fix big→inter-body

big→inter : ∀ {k M Q}
          → M ⇓⁅ k ⁆ Q
          → M ⇛⁅ k ⁆ (Qᵀ Q)
big→inter {k} {M} {Q} = big→inter-exp k M Q

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
big→small-rtc {Q} = inter→small-rtc ∘ ⇛-covariant go ∘ big→inter
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

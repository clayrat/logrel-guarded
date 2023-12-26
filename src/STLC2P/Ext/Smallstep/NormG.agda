{-# OPTIONS --guarded #-}
module STLC2P.Ext.Smallstep.NormG where

open import Prelude hiding (_⊆_)
open import Data.Empty
open import Data.Dec
open import Data.String
open import Data.Maybe
open import Data.List
open import Data.List.Correspondences.Unary.All

open import Later
open import Interlude
open import Guarded.Partial

open import STLC2P.Ext.Term
open import STLC2P.Ext.Ty
open import STLC2P.Ext.Smallstep.Step
open import STLC2P.Ext.Smallstep.TyStep
open import STLC2P.Ext.Smallstep.Multi

-- guarded version of the R logical relation as data

{-
data R : Ty → Term → 𝒰 where

  R𝟚 : ∀ {t}
     → ∅ ⊢ t ⦂ 𝟚
     → halts t
     → R 𝟚 t

  R⇒ : ∀ {T₁ T₂ t}
     → ∅ ⊢ t ⦂ (T₁ ⇒ T₂)
     → halts t
     → (∀ s → ▹ R T₁ s → Part (▹ R T₂ (t · s)))
     → R (T₁ ⇒ T₂) t

  R𝕩 : ∀ {T₁ T₂ t}
     → ∅ ⊢ t ⦂ T₁ 𝕩 T₂
     → halts t
     → ▹ R T₁ (t ⇀₁)
     → ▹ R T₂ (t ⇀₂)
     → R (T₁ 𝕩 T₂) t
-}

R-case : (Ty → Term → ▹ 𝒰) → Ty → Term → 𝒰
R-case R▹  𝟚        t = (∅ ⊢ t ⦂ 𝟚)
                      × halts t
R-case R▹ (T₁ ⇒ T₂) t = (∅ ⊢ t ⦂ (T₁ ⇒ T₂))
                      × halts t
                      × (∀ s → ▸ R▹ T₁ s → Part (▸ R▹ T₂ (t · s)))
R-case R▹ (T₁ 𝕩 T₂) t = (∅ ⊢ t ⦂ T₁ 𝕩 T₂)
                      × halts t
                      × ▸ R▹ T₁ (t ⇀₁)
                      × ▸ R▹ T₂ (t ⇀₂)

R-body : ▹ (Ty → Term → 𝒰) → Ty → Term → 𝒰
R-body f = R-case (λ T t → f ⊛ next T ⊛ next t)

R : Ty → Term → 𝒰
R = fix R-body

-- constructors

R𝟚 : ∀ {t}
   → ∅ ⊢ t ⦂ 𝟚 → halts t
   → R 𝟚 t
R𝟚 ⊢t h = ⊢t , h

R⇒ : ∀ {T₁ T₂ t}
   → ∅ ⊢ t ⦂ (T₁ ⇒ T₂) → halts t
   → (∀ s → ▹ R T₁ s → Part (▹ R T₂ (t · s)))
   → R (T₁ ⇒ T₂) t
R⇒ {T₁} {T₂} {t} ⊢t h r =
  ⊢t , h , λ s → transport (λ i → ▹[ α ] pfix R-body (~ i) α T₁ s
                                 → Part (▹[ α ] pfix R-body (~ i) α T₂ (t · s)))
                           (r s)

R𝕩 : ∀ {T₁ T₂ t}
   → ∅ ⊢ t ⦂ T₁ 𝕩 T₂
   → halts t
   → ▹ R T₁ (t ⇀₁)
   → ▹ R T₂ (t ⇀₂)
   → R (T₁ 𝕩 T₂) t
R𝕩 {T₁} {T₂} {t} ⊢t h r1 r2 =
  ⊢t , h
  , transport (λ i → ▹[ α ] pfix R-body (~ i) α T₁ (t ⇀₁)) r1
  , transport (λ i → ▹[ α ] pfix R-body (~ i) α T₂ (t ⇀₂)) r2

-- destructors

R𝟚-match : ∀ {t}
   → R 𝟚 t
   → (∅ ⊢ t ⦂ 𝟚) × halts t
R𝟚-match = id

R⇒-match : ∀ {T₁ T₂ t}
         → R (T₁ ⇒ T₂) t
         → (∅ ⊢ t ⦂ (T₁ ⇒ T₂)) × halts t × (∀ s → ▹ R T₁ s → Part (▹ R T₂ (t · s)))
R⇒-match {T₁} {T₂} {t} (⊢t , h , r) =
  ⊢t , h , λ s → transport (λ i → ▹[ α ] pfix R-body i α T₁ s
                                 → Part (▹[ α ] pfix R-body i α T₂ (t · s)))
                            (r s)

R𝕩-match : ∀ {T₁ T₂ t}
         → R (T₁ 𝕩 T₂) t
         → (∅ ⊢ t ⦂ T₁ 𝕩 T₂) × halts t × ▹ R T₁ (t ⇀₁) × ▹ R T₂ (t ⇀₂)
R𝕩-match {T₁} {T₂} {t} (⊢t , h , r1 , r2) =
  ⊢t , h
  , transport (λ i → ▹[ α ] pfix R-body i α T₁ (t ⇀₁)) r1
  , transport (λ i → ▹[ α ] pfix R-body i α T₂ (t ⇀₂)) r2

-- projections

R-halts : ∀ {T t} → R T t → halts t
R-halts {T = 𝟚}       (_ , h)     = h
R-halts {T = T₁ ⇒ T₂} (_ , h , _) = h
R-halts {T = T₁ 𝕩 T₂} (_ , h , _) = h

R-typable-empty : ∀ {T t} → R T t → ∅ ⊢ t ⦂ T
R-typable-empty {T = 𝟚}       (tp , _)     = tp
R-typable-empty {T = T₁ ⇒ T₂} (tp , _ , _) = tp
R-typable-empty {T = T₁ 𝕩 T₂} (tp , _ , _) = tp

-- R properties

step-preserves-R : ∀ {T t t′}
                 → (t —→ t′) → R T t → R T t′
step-preserves-R {T = 𝟚}       S r = let tp , h = R𝟚-match r in
  R𝟚 (preserve tp S) (step-preserves-halting S .fst h)
step-preserves-R {T = T₁ ⇒ T₂} S r = let tp , h , Ri = R⇒-match r in
  R⇒ (preserve tp S) (step-preserves-halting S .fst h)
     (λ t″ R₁ → mapᵖ (▹map (step-preserves-R (ξ-·₁ S))) (Ri t″ R₁))
step-preserves-R {T = T₁ 𝕩 T₂} S r = let tp , h , Rp1 , Rp2 = R𝕩-match r in
  R𝕩 (preserve tp S) (step-preserves-halting S .fst h)
     (▹map (step-preserves-R (ξ-⇀₁ S)) Rp1)
     (▹map (step-preserves-R (ξ-⇀₂ S)) Rp2)

multistep-preserves-R : ∀ {T t t′}
                      → (t —↠ t′) → R T t → R T t′
multistep-preserves-R {T} {t} {.t} (.t ∎ᵣ)         Rt = Rt
multistep-preserves-R {T} {t} {t′} (.t —→⟨ TM ⟩ M) Rt =
  multistep-preserves-R M (step-preserves-R TM Rt)

step-preserves-R' : ∀ {T t t′}
                  → ∅ ⊢ t ⦂ T → (t —→ t′) → R T t′ → R T t
step-preserves-R' {T = 𝟚}       {t} {t′} tp S r = let _ , h′ = R𝟚-match r in
  R𝟚 tp (step-preserves-halting S .snd h′)
step-preserves-R' {T = T₁ ⇒ T₂} {t} {t′} tp S r = let _ , h′ , Ri = R⇒-match r in
  R⇒ tp (step-preserves-halting S .snd h′)
     (λ t″ R₁ → mapᵖ (▹map² (λ x → step-preserves-R' (tp ⊢· R-typable-empty x) (ξ-·₁ S)) R₁)
                     (Ri t″ R₁))
step-preserves-R' {T = T₁ 𝕩 T₂} {t} {t′} tp S r = let _ , h′ , Rp1 , Rp2 = R𝕩-match r in
  R𝕩 tp (step-preserves-halting S .snd h′)
     (▹map (step-preserves-R' (⊢⇀₁ tp) (ξ-⇀₁ S)) Rp1)
     (▹map (step-preserves-R' (⊢⇀₂ tp) (ξ-⇀₂ S)) Rp2)

multistep-preserves-R' : ∀ {T t t′}
                       → ∅ ⊢ t ⦂ T → (t —↠ t′) → R T t′ → R T t
multistep-preserves-R' {T} {t} {.t} tp (.t ∎ᵣ)         Rt = Rt
multistep-preserves-R' {T} {t} {t′} tp (.t —→⟨ TM ⟩ S) Rt =
  step-preserves-R' tp TM (multistep-preserves-R' (preserve tp TM) S Rt)

-- instantiations

data Inst : Tass → Env → 𝒰 where
  V-nil  : Inst [] []
  V-cons : ∀ {x T v c e}
         → Value v → R T v → Inst c e
         → Inst ((x , T) ∷ c) ((x , v) ∷ e)

instantiation-domains-match : ∀ {c e}
                            → Inst c e
                            → ∀ {x T}
                            → lup x c ＝ just T
                            → Σ[ t ꞉ Term ] (lup x e ＝ just t)
instantiation-domains-match  V-nil                         e =
  absurd (nothing≠just e)
instantiation-domains-match (V-cons {x = y} {v} V r i) {x} e with x ≟ y
... | yes prf = v , refl
... | no ctra = instantiation-domains-match i e

instantiation-env-closed : ∀ {c e}
                         → Inst c e
                         → closed-env e
instantiation-env-closed {.[]}            {.[]}             V-nil                             = []
instantiation-env-closed {.((x , T) ∷ c)} {.((x , v) ∷ e)} (V-cons {x} {T} {v} {c} {e} V r i) =
  ∅⊢-closed (R-typable-empty r) ∷ instantiation-env-closed i

instantiation-R : ∀ {c e t T}
                → Inst c e
                → ∀ x
                → lup x c ＝ just T
                → lup x e ＝ just t
                → R T t
instantiation-R {.[]}            {.[]}                     V-nil                                 _ ec _  =
  absurd (nothing≠just ec)
instantiation-R {.((y , S) ∷ c)} {.((y , v) ∷ e)} {t} (V-cons {x = y} {T = S} {v} {c} {e} V r i) x ec ee with x ≟ y
... | yes prf = subst (λ q → R q t) (just-inj ec) (subst (R S) (just-inj ee) r)
... | no ctra = instantiation-R i x ec ee

instantiation-drop : ∀ {c e}
                   → Inst c e
                   → ∀ x → Inst (drp x c) (drp x e)
instantiation-drop {.[]}            {.[]}             V-nil                                 x = V-nil
instantiation-drop {.((y , T) ∷ c)} {.((y , v) ∷ e)} (V-cons {x = y} {T} {v} {c} {e} V r i) x with x ≟ y
... | yes prf = instantiation-drop i x
... | no ctra = V-cons V r (instantiation-drop i x)

-- The R Lemma

msubst-preserves-typing : ∀ {c e Γ t S}
                        → Inst c e
                        → mupdate c Γ ⊢ t ⦂ S
                        → Γ ⊢ msubst e t ⦂ S
msubst-preserves-typing {.[]}            {.[]}             V-nil                             ty = ty
msubst-preserves-typing {.((x , T) ∷ c)} {.((x , v) ∷ e)} (V-cons {x} {T} {v} {c} {e} V r i) ty =
  msubst-preserves-typing i (subst-ty (R-typable-empty r) ty)

msubst-R : ∀ {c e t T}
         → mupdate c ∅ ⊢ t ⦂ T
         → Inst c e
         → Part (R T (msubst e t))
------ core ------
msubst-R         {t = .(` x)}            (⊢` {x} l)                       i =
  let lupc = mupdate-lookup l
      t′ , P = instantiation-domains-match i lupc
    in
  now $ instantiation-R i x lupc
    (P ∙ ap just (sym (ap (extract (` x)) P)
                  ∙ sym (msubst-var (instantiation-env-closed i) x)))
msubst-R {c} {e} {.(ƛ x ⇒ N)} {.(A ⇒ B)} (⊢ƛ {x} {N} {A} {B} ⊢N)          i =
  let mabs = msubst-abs e x N
      WT : ∅ ⊢ ƛ x ⇒ msubst (drp x e) N ⦂ A ⇒ B
      WT = ⊢ƛ $ msubst-preserves-typing (instantiation-drop i x)
                                         (weaken (go c x A) ⊢N)
      in
  now $ R⇒ (subst (λ q → ∅ ⊢ q ⦂ A ⇒ B) (sym mabs) WT)
           (value-halts (subst Value (sym mabs) V-ƛ))
           (λ s → later ∘ ▹map λ Rs →
                  let v , P , Q  = R-halts Rs
                      Rv = multistep-preserves-R P Rs
                    in
                  mapᵖ (next ∘ subst (λ q → R B (q · s)) (sym mabs) ∘
                        multistep-preserves-R'
                          (WT ⊢· R-typable-empty Rs)
                          (multistep-appr V-ƛ P
                            —↠+
                           subst (λ q → (ƛ x ⇒ msubst (drp x e) N) · v —→ q)
                                 (sym $ subst-msubst (∅⊢-closed (R-typable-empty Rv))
                                                     (instantiation-env-closed i)
                                                     x N)
                                 (β-ƛ Q)))
                       (msubst-R ⊢N (V-cons Q Rv i)))
  where
  go : ∀ c x A → (mupdate c ∅ , x ⦂ A) ⊆ mupdate (drp x c) (∅ , x ⦂ A)
  go []            x A T i l = l
  go ((y , p) ∷ c) x A T i l with x ≟ y
  ... | yes prf = go c x A T i (⊆-shadow T i (subst (λ q → mupdate c ∅ , q ⦂ p , x ⦂ A ∋ i ⦂ T) (sym prf) l))
  go ((y , p) ∷ c) x A .A .x  here                     | no ctra = there ctra (go c x A A x here)
  go ((y , p) ∷ c) x A .p .y (there _    here)         | no ctra = here
  go ((y , p) ∷ c) x A  T  i (there i≠x (there i≠y l)) | no ctra = there i≠y (go c x A T i (there i≠x l))
msubst-R     {e} {.(L · M)}    {T}       (_⊢·_ {L} {M} {A} ⊢L ⊢M)        i =
  msubst-R ⊢L i >>=ᵖ λ R1 →
  msubst-R ⊢M i >>=ᵖ λ R2 →
  let (_ , _ , R1→) = R⇒-match R1
      Rapp = R1→ (msubst e M) (next R2)
    in
  later $ Part▹ (subst (λ q → ▹ R T q) (sym $ msubst-app e L M)) Rapp
------ booleans ------
msubst-R     {e}                          ⊢𝓉                               i =
  let mt = sym $ msubst-true e in
  now $ R𝟚 (subst (λ q → ∅ ⊢ q ⦂ 𝟚) mt ⊢𝓉)
           (subst halts mt $ value-halts V-𝓉)
msubst-R     {e}                          ⊢𝒻                              i =
  let mf = sym $ msubst-false e in
  now $ R𝟚 (subst (λ q → ∅ ⊢ q ⦂ 𝟚) mf ⊢𝒻)
           (subst halts mf $ value-halts V-𝒻)
msubst-R     {e} {.(⁇ L ↑ M ↓ N)}   {T}       (⊢⁇ {L} {M} {N} ⊢L ⊢M ⊢N) i =
  msubst-R ⊢L i >>=ᵖ go
  where
  go : R 𝟚 (msubst e L) → Part (R T (msubst e (⁇ L ↑ M ↓ N)))
  go (⊢mL , .(ƛ _ ⇒ _)  , S , V-ƛ) = absurd (¬ƛ⦂𝟚 $ multi-preserve ⊢mL S)
  go (⊢mL , .𝓉          , S , V-𝓉) =
    mapᵖ (subst (R T) (sym $ msubst-if e L M N) ∘
          multistep-preserves-R'
            (⊢⁇ ⊢mL (msubst-preserves-typing i ⊢M) (msubst-preserves-typing i ⊢N))
            (multistep-test0 S —↠+ β-𝓉))
         (msubst-R ⊢M i)
  go (⊢mL , .𝒻         , S , V-𝒻) =
    mapᵖ (subst (R T) (sym $ msubst-if e L M N) ∘
          multistep-preserves-R'
            (⊢⁇ ⊢mL (msubst-preserves-typing i ⊢M) (msubst-preserves-typing i ⊢N))
            (multistep-test0 S —↠+ β-𝒻))
         (msubst-R ⊢N i)
  go (⊢mL , .(〈 _ ⹁ _ 〉) , S , V-〈〉 _ _) = absurd (¬〈〉⦂𝟚 $ multi-preserve ⊢mL S)
------ pairs ------
msubst-R     {e} {.(〈 L ⹁ M 〉)}     {.(A 𝕩 B)} (⊢〈〉 {L} {M} {A} {B} ⊢L ⊢M) i =
  let mp = sym $ msubst-pair e L M
      ⊢mLM = ⊢〈〉 (msubst-preserves-typing i ⊢L) (msubst-preserves-typing i ⊢M)
    in
  msubst-R ⊢L i >>=ᵖ λ R1 →
  msubst-R ⊢M i >>=ᵖ λ R2 →
  let t1 , s1 , v1 = R-halts R1
      t2 , s2 , v2 = R-halts R2
      s12 = multistep-pairl s1 —↠∘ multistep-pairr v1 s2
    in
  now $ R𝕩 (subst (λ q → ∅ ⊢ q ⦂ A 𝕩 B) mp ⊢mLM)
           (subst halts mp $ 〈 t1 ⹁ t2 〉 , s12 , V-〈〉 v1 v2)
           (next $ subst (λ q → R A (q ⇀₁)) mp $
              multistep-preserves-R' (⊢⇀₁ ⊢mLM) (multistep-fst s12 —↠+ β-〈〉₁ v1 v2) $
              multistep-preserves-R s1 R1)
           (next $ (subst (λ q → R B (q ⇀₂)) mp $
              multistep-preserves-R' (⊢⇀₂ ⊢mLM) (multistep-snd s12 —↠+ β-〈〉₂ v1 v2) $
              multistep-preserves-R s2 R2))
msubst-R     {e} {.(L ⇀₁)}         {T = A}  (⊢⇀₁ {L} {B} ⊢L)              i =
  msubst-R ⊢L i >>=ᵖ λ Rl →
  let _ , _ , Ra , _ = R𝕩-match Rl in
  later (▹map (now ∘ subst (R A) (sym $ msubst-fst e L)) Ra)
msubst-R     {e} {.(L ⇀₂)}         {T = B}  (⊢⇀₂ {L} {A} ⊢L)              i =
  msubst-R ⊢L i >>=ᵖ λ Rl →
  let _ , _ , _ , Rb = R𝕩-match Rl in
  later (▹map (now ∘ subst (R B) (sym $ msubst-snd e L)) Rb)

normalization : ∀ {t T}
              → ∅ ⊢ t ⦂ T
              → Part (halts t)
normalization ⊢t = mapᵖ R-halts $ msubst-R ⊢t V-nil

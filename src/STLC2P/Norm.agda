module STLC2P.Norm where

open import Prelude
open import Data.Empty
open import Data.Dec
open import Data.String
open import Data.Maybe
open import Data.List.Correspondences.Unary.All

open import Interlude
open import STLC2P.Term
open import STLC2P.Ty
open import STLC2P.Multi

--- R logical relation

R : Ty → Term → 𝒰
R (T₁ ⇒ T₂) t = (∅ ⊢ t ⦂ T₁ ⇒ T₂)
              × halts t
              × (∀ s → R T₁ s → R T₂ (t · s))
R  𝟚        t = (∅ ⊢ t ⦂ 𝟚)
              × halts t
R (T₁ 𝕩 T₂) t = (∅ ⊢ t ⦂ T₁ 𝕩 T₂)
              × halts t
              × R T₁ (t ⇀₁) × R T₂ (t ⇀₂)

R-halts : (T : Ty) → (t : Term) → R T t → halts t
R-halts (T₁ ⇒ T₂) t (_ , h , _) = h
R-halts (T₁ 𝕩 T₂) t (_ , h , _) = h
R-halts  𝟚        t (_ , h)     = h

R-typable-empty : (T : Ty) → (t : Term) → R T t → ∅ ⊢ t ⦂ T
R-typable-empty (T₁ ⇒ T₂) t (tp , _ , _) = tp
R-typable-empty (T₁ 𝕩 T₂) t (tp , _ , _) = tp
R-typable-empty  𝟚        t (tp , _)     = tp

step-preserves-R : ∀ T t t′
                 → (t —→ t′) → R T t → R T t′
step-preserves-R (T₁ ⇒ T₂) t t′ S (tp , h , Ri)         =
  preserve tp S , step-preserves-halting S .fst h ,
    λ t″ R₁ → step-preserves-R T₂ (t · t″) (t′ · t″) (ξ-·₁ S) (Ri t″ R₁)
step-preserves-R (T₁ 𝕩 T₂) t t′ S (tp , h , Rp1 , Rp2) =
  preserve tp S , step-preserves-halting S .fst h
  , step-preserves-R T₁ (t ⇀₁) (t′ ⇀₁) (ξ-⇀₁ S) Rp1
  , step-preserves-R T₂ (t ⇀₂) (t′ ⇀₂) (ξ-⇀₂ S) Rp2
step-preserves-R  𝟚       t t′ S (tp , h)              =
  (preserve tp S) , (step-preserves-halting S .fst h)

multistep-preserves-R : ∀ T t t′
                      → (t —↠ t′) → R T t → R T t′
multistep-preserves-R T t .t  (.t ∎ᵣ)         Rt = Rt
multistep-preserves-R T t  t′ (.t —→⟨ TM ⟩ M) Rt =
  multistep-preserves-R _ _ _ M (step-preserves-R _ _ _ TM Rt)

step-preserves-R' : ∀ T t t′
                  → ∅ ⊢ t ⦂ T → (t —→ t′) → R T t′ → R T t
step-preserves-R' (T₁ ⇒ T₂) t t′ tp S (_ , h′ , Ri)        =
  tp , step-preserves-halting S .snd h′ ,
    λ t″ R₁ → step-preserves-R' T₂ (t · t″) (t′ · t″)
                (tp ⊢· R-typable-empty T₁ t″ R₁)
                (ξ-·₁ S) (Ri t″ R₁)
step-preserves-R' (T₁ 𝕩 T₂) t t′ tp S (_ , h′ , Rp1 , Rp2) =
  tp , step-preserves-halting S .snd h′
  , step-preserves-R' T₁ (t ⇀₁) (t′ ⇀₁) (⊢⇀₁ tp) (ξ-⇀₁ S) Rp1
  , step-preserves-R' T₂ (t ⇀₂) (t′ ⇀₂) (⊢⇀₂ tp) (ξ-⇀₂ S) Rp2
step-preserves-R'  𝟚        t t′ tp S (_ , h′)             =
  tp , step-preserves-halting S .snd h′

multistep-preserves-R' : ∀ T t t′
                       → ∅ ⊢ t ⦂ T → (t —↠ t′) → R T t′ → R T t
multistep-preserves-R' T t .t  tp (.t ∎ᵣ)         Rt = Rt
multistep-preserves-R' T t  t′ tp (.t —→⟨ TM ⟩ S) Rt =
  step-preserves-R' _ _ _ tp TM (multistep-preserves-R' _ _ _ (preserve tp TM) S Rt)

-- instantiations

data Inst : Tass → Env → 𝒰 where
  V-nil : Inst [] []
  V-cons : ∀ {x T v c e}
         → Value v → R T v → Inst c e
         → Inst ((x , T) ∷ c) ((x , v) ∷ e)

instantiation-domains-match : ∀ {c e}
                            → Inst c e
                            → ∀ {x T}
                            → lup x c ＝ just T
                            → Σ[ t ꞉ Term ] (lup x e ＝ just t)
instantiation-domains-match  V-nil                         eq =
  absurd (nothing≠just eq)
instantiation-domains-match (V-cons {x = y} {v} V r i) {x} eq with x ≟ y
... | yes prf = v , refl
... | no ctra = instantiation-domains-match i eq

instantiation-env-closed : ∀ c e
                         → Inst c e
                         → closed-env e
instantiation-env-closed .[]            .[]             V-nil                             = []
instantiation-env-closed .((x , T) ∷ c) .((x , v) ∷ e) (V-cons {x} {T} {v} {c} {e} V r i) =
  ∅⊢-closed (R-typable-empty T v r) ∷ instantiation-env-closed c e i

instantiation-R : ∀ c e
                → Inst c e
                → ∀ x t T
                → lup x c ＝ just T
                → lup x e ＝ just t
                → R T t
instantiation-R .[]            .[]             V-nil                                     x t T ec ee =
  absurd (nothing≠just ee)
instantiation-R .((y , S) ∷ c) .((y , v) ∷ e) (V-cons {x = y} {T = S} {v} {c} {e} V r i) x t T ec ee with x ≟ y
... | yes prf = subst (λ q → R q t) (just-inj ec) (subst (R S) (just-inj ee) r)
... | no ctra = instantiation-R c e i x t T ec ee

instantiation-drop : ∀ c e
                   → Inst c e
                   → ∀ x → Inst (drp x c) (drp x e)
instantiation-drop .[]            .[]             V-nil                                 x = V-nil
instantiation-drop .((y , T) ∷ c) .((y , v) ∷ e) (V-cons {x = y} {T} {v} {c} {e} V r i) x with x ≟ y
... | yes prf = instantiation-drop c e i x
... | no ctra = V-cons V r (instantiation-drop c e i x)

-- The R Lemma

msubst-preserves-typing : ∀ c e
                        → Inst c e
                        → ∀ Γ t S
                        → (mupdate c Γ) ⊢ t ⦂ S
                        → Γ ⊢ (msubst e t) ⦂ S
msubst-preserves-typing .[]            .[]             V-nil                             Γ t S ty = ty
msubst-preserves-typing .((x , T) ∷ c) .((x , v) ∷ e) (V-cons {x} {T} {v} {c} {e} V r i) Γ t S ty =
  msubst-preserves-typing c e i Γ (t [ x := v ]) S (subst-ty (R-typable-empty T v r) ty)

msubst-R : ∀ c e t T
         → (mupdate c ∅) ⊢ t ⦂ T
         → Inst c e
         → R T (msubst e t)
msubst-R c e .(` x)      T       (⊢` {x} l)                       i =
  let lupc = mupdate-lookup c x T l
      t′ , P = instantiation-domains-match i lupc
    in
  instantiation-R c e i x (msubst e (` x)) T lupc
    (P ∙ ap just (sym (ap (extract (` x)) P)
                       ∙ sym (msubst-var e x (instantiation-env-closed c e i))))
msubst-R c e .(ƛ x ⇒ N) .(A ⇒ B) (⊢ƛ {x} {N} {A} {B} ⊢N)         i =
  let mabs = msubst-abs e x N
      WT : ∅ ⊢ ƛ x ⇒ msubst (drp x e) N ⦂ A ⇒ B
      WT = ⊢ƛ $ msubst-preserves-typing (drp x c) (drp x e)
                    (instantiation-drop c e i x)
                    (∅ , x ⦂ A) N B
                    (weaken (go c x A) ⊢N)
      in
    subst (λ q → ∅ ⊢ q ⦂ A ⇒ B) (sym mabs) WT
  , value-halts (subst Value (sym mabs) V-ƛ)
  , λ s Rs →
      let v , P , Q  = R-halts A s Rs
          Rv = multistep-preserves-R A s v P Rs
       in
      subst (λ q → R B (q · s)) (sym mabs) $
      multistep-preserves-R' B ((ƛ x ⇒ msubst (drp x e) N) · s) (msubst ((x , v) ∷ e) N)
        (WT ⊢· (R-typable-empty A s Rs))
        (multistep-appr (ƛ x ⇒ msubst (drp x e) N) s v V-ƛ P
          —↠∘
         (((ƛ x ⇒ msubst (drp x e) N) · v)
              —→⟨ subst (λ q → (ƛ x ⇒ msubst (drp x e) N) · v —→ q)
                         (sym (subst-msubst e x v N (∅⊢-closed (R-typable-empty A v Rv))
                                                    (instantiation-env-closed c e i)))
                         (β-ƛ Q) ⟩
                (msubst e (N [ x := v ]) ∎ᵣ)))
        (msubst-R ((x , A) ∷ c) ((x , v) ∷ e) N B ⊢N (V-cons Q Rv i))
  where
  go : ∀ c x A → (mupdate c ∅ , x ⦂ A) ⊆ mupdate (drp x c) (∅ , x ⦂ A)
  go []            x A T i l = l
  go ((y , p) ∷ c) x A T i l with x ≟ y
  ... | yes prf = go c x A T i (⊆-shadow T i (subst (λ q → mupdate c ∅ , q ⦂ p , x ⦂ A ∋ i ⦂ T) (sym prf) l))
  go ((y , p) ∷ c) x A .A .x  here                     | no ctra = there ctra (go c x A A x here)
  go ((y , p) ∷ c) x A .p .y (there _    here)         | no ctra = here
  go ((y , p) ∷ c) x A  T  i (there i≠x (there i≠y l)) | no ctra = there i≠y (go c x A T i (there i≠x l))
msubst-R c e .(L · M)    T       (_⊢·_ {L} {M} {A} ⊢L ⊢M)        i =
  subst (R T) (sym (msubst-app e L M)) $
  msubst-R c e L (A ⇒ T) ⊢L i .snd .snd _ $
  msubst-R c e M A ⊢M i
msubst-R c e .𝓉              .𝟚        ⊢𝓉                         i =
  let mt = sym $ msubst-true e in
    subst (λ q → ∅ ⊢ q ⦂ 𝟚) mt ⊢𝓉
  , 𝓉 , subst (_—↠ 𝓉) mt (𝓉 ∎ᵣ) , V-𝓉
msubst-R c e .𝒻             .𝟚        ⊢𝒻                         i =
  let mf = sym $ msubst-false e in
    subst (λ q → ∅ ⊢ q ⦂ 𝟚) mf ⊢𝒻
  , 𝒻 , subst (_—↠ 𝒻) mf (𝒻 ∎ᵣ) , V-𝒻
msubst-R c e .(⁇ L ↑ M ↓ N)   T       (⊢⁇ {L} {M} {N} ⊢L ⊢M ⊢N) i with (msubst-R c e L 𝟚 ⊢L i)
... | ⊢mL , .(ƛ _ ⇒ _)  , S , V-ƛ      = absurd (¬ƛ⦂𝟚 $ multi-preserve ⊢mL S)
... | ⊢mL , .𝓉         , S , V-𝓉       =
  subst (R T) (sym (msubst-if e L M N)) $
  multistep-preserves-R' T
    (⁇ msubst e L ↑ msubst e M ↓ msubst e N)
    (msubst e M)
    (⊢⁇ ⊢mL (msubst-preserves-typing c e i ∅ M T ⊢M) (msubst-preserves-typing c e i ∅ N T ⊢N))
    (multistep-test0 (msubst e L) 𝓉 (msubst e M) (msubst e N) S
      —↠∘
     (⁇ 𝓉 ↑ msubst e M ↓ msubst e N —→⟨ β-𝓉 ⟩ msubst e M ∎ᵣ))
    (msubst-R c e M T ⊢M i)
... | ⊢mL , .𝒻         , S , V-𝒻      =
  subst (R T) (sym (msubst-if e L M N)) $
  multistep-preserves-R' T
    (⁇ msubst e L ↑ msubst e M ↓ msubst e N)
    (msubst e N)
    (⊢⁇ ⊢mL (msubst-preserves-typing c e i ∅ M T ⊢M) (msubst-preserves-typing c e i ∅ N T ⊢N))
    (multistep-test0 (msubst e L) 𝒻 (msubst e M) (msubst e N) S
      —↠∘
     (⁇ 𝒻 ↑ msubst e M ↓ msubst e N —→⟨ β-𝒻 ⟩ msubst e N ∎ᵣ))
    (msubst-R c e N T ⊢N i)
... | ⊢mL , .(〈 _ ⹁ _ 〉) , S , V-〈〉 _ _ = absurd (¬〈〉⦂𝟚 $ multi-preserve ⊢mL S)
msubst-R c e .(〈 L ⹁ M 〉)     .(A 𝕩 B) (⊢〈〉 {L} {M} {A} {B} ⊢L ⊢M) i =
  {!!} , {!!} , {!!} , {!!}
msubst-R c e .(L ⇀₁)         A       (⊢⇀₁ {L} {B} ⊢L)            i =
  subst (R A) (sym $ msubst-fst e L) $
  msubst-R c e L (A 𝕩 B) ⊢L i .snd .snd .fst
msubst-R c e .(L ⇀₂)         B       (⊢⇀₂ {L} {A} ⊢L)            i =
  subst (R B) (sym $ msubst-snd e L) $
  msubst-R c e L (A 𝕩 B) ⊢L i .snd .snd .snd

normalization : ∀ t T
              → ∅ ⊢ t ⦂ T → halts t
normalization t T ty = R-halts T t (msubst-R [] [] t T ty V-nil)

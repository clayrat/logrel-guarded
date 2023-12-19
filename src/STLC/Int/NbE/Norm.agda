{-# OPTIONS --guarded #-}
module STLC.Int.NbE.Norm where

open import Prelude hiding (apply)
open import Later
open import Guarded.Partial

open import STLC.Ty
open import STLC.Int.TyTerm
open import STLC.Int.NbE.OPE

-- neutral terms

data Ne (Ξ : Ctx → Ty → 𝒰) (Γ : Ctx) : Ty → 𝒰 where
  ne-` : ∀ {A}
       → Γ ∋ A
         ------------
       → Ne Ξ Γ A

  ne-· : ∀ {A B}
       → Ne Ξ Γ (A ⇒ B)
       → Ξ Γ A
         --------------
       → Ne Ξ Γ B

mutual
  -- weak head normal terms
  data Val (Δ : Ctx) : Ty → 𝒰 where
    v-ƛ : ∀ {Γ A B}
        → Γ ﹐ A ⊢ B
        → Env Δ Γ
          ------------------
        → Val Δ (A ⇒ B)

    v-ne : ∀ {A}
          → Ne Val Δ A
            ----------
          → Val Δ A

  -- environments
  data Env (Δ : Ctx) : Ctx → 𝒰 where
    ε    : Env Δ ∅

    _、_ : ∀ {Γ A}
         → Env Δ Γ
         → Val Δ A
           -------------
         → Env Δ (Γ ﹐ A)

lookup : ∀ {Γ Δ A}
       → Γ ∋ A → Env Δ Γ → Val Δ A
lookup  here      (e 、 v) = v
lookup (there ix) (e 、 v) = lookup ix e

mutual
  eval-body : ▹ (∀ Γ Δ B → Γ ⊢ B → Env Δ Γ → Part (Val Δ B))
            →    ∀ Γ Δ B → Γ ⊢ B → Env Δ Γ → Part (Val Δ B)
  eval-body ev▹ Γ Δ B (` x)   e = now (lookup x e)
  eval-body ev▹ Γ Δ B (ƛ M)   e = now (v-ƛ M e)
  eval-body ev▹ Γ Δ B (M · N) e = eval-body ev▹ Γ Δ (_ ⇒ B) M e >>=ᵖ λ f →
                                  eval-body ev▹ Γ Δ _ N e >>=ᵖ λ v →
                                  apply-body ev▹ f v

  apply-body : ∀ {Δ A B}
             → ▹ (∀ Γ Δ B → Γ ⊢ B → Env Δ Γ → Part (Val Δ B))
             → Val Δ (A ⇒ B) → Val Δ A → Part (Val Δ B)
  apply-body ev▹ (v-ƛ M e) va = later (beta-body ev▹ M e va)
  apply-body ev▹ (v-ne N)  va = now (v-ne (ne-· N va))

  beta-body : ∀ {Γ Δ A B}
       → ▹ (∀ Γ Δ B → Γ ⊢ B → Env Δ Γ → Part (Val Δ B))
       → Γ ﹐ A ⊢ B → Env Δ Γ → Val Δ A → ▹ Part (Val Δ B)
  beta-body {Γ} {Δ} {A} {B} ev▹ tm e v = ev▹ ⊛ next (Γ ﹐ A) ⊛ next Δ ⊛ next B ⊛ next tm ⊛ next (e 、 v)

eval : ∀ {Γ Δ B}
     → Γ ⊢ B → Env Δ Γ → Part (Val Δ B)
eval {Γ} {Δ} {B} = fix eval-body Γ Δ B

apply : ∀ {Δ A B}
      → Val Δ (A ⇒ B) → Val Δ A → Part (Val Δ B)
apply = apply-body (dfix eval-body)

beta : ∀ {Γ Δ A B}
     → Γ ﹐ A ⊢ B → Env Δ Γ → Val Δ A → ▹ Part (Val Δ B)
beta = beta-body (dfix eval-body)

data Nf (Γ : Ctx) : Ty → 𝒰 where
  nf-ƛ : ∀ {A B}
        → Nf (Γ ﹐ A) B
          ------------------
        → Nf Γ (A ⇒ B)

  nf-ne : Ne Nf Γ 𝟙
          ----------
        → Nf Γ 𝟙

var≤ : ∀ {Γ Δ A} → Γ ≤ Δ → Δ ∋ A → Γ ∋ A
var≤  id≤       v        = v
var≤ (weak≤ η)  v        = there (var≤ η v)
var≤ (lift≤ η)  here     = here
var≤ (lift≤ η) (there v) = there (var≤ η v)

mutual
  val≤ : ∀ {Γ Δ A} → Γ ≤ Δ → Val Δ A → Val Γ A
  val≤ η (v-ƛ M e) = v-ƛ M (env≤ η e)
  val≤ η (v-ne N)  = v-ne (nev≤ η N)

  env≤ : ∀ {Γ Δ E} → Γ ≤ Δ → Env Δ E → Env Γ E
  env≤ η  ε       = ε
  env≤ η (e 、 v) = (env≤ η e) 、 (val≤ η v)

  nev≤ : ∀ {Γ Δ A} → Γ ≤ Δ → Ne Val Δ A → Ne Val Γ A
  nev≤ η (ne-` x)   = ne-` (var≤ η x)
  nev≤ η (ne-· n v) = ne-· (nev≤ η n) (val≤ η v)

mutual
  nf≤ : ∀ {Γ Δ A} → Γ ≤ Δ → Nf Δ A → Nf Γ A
  nf≤ η (nf-ƛ n)  = nf-ƛ (nf≤ (lift≤ η) n)
  nf≤ η (nf-ne n) = nf-ne (nen≤ η n)

  nen≤ : ∀ {Γ Δ A} → Γ ≤ Δ → Ne Nf Δ A → Ne Nf Γ A
  nen≤ η (ne-` x)    = ne-` (var≤ η x)
  nen≤ η (ne-· ne n) = ne-· (nen≤ η ne) (nf≤ η n)

weakVal : ∀ {Γ A B}
        → Val Γ B → Val (Γ ﹐ A) B
weakVal = val≤ wk

mutual
  readback-body : ▹ (∀ Γ A → Val Γ A → Part (Nf Γ A))
                →    ∀ Γ A → Val Γ A → Part (Nf Γ A)
  readback-body r▹ Γ  𝟙      (v-ne n) = mapᵖ nf-ne (nereadback-body r▹ n)
  readback-body r▹ Γ (A ⇒ B)  v       = mapᵖ nf-ƛ (later (eta-body r▹ v))

  nereadback-body : ∀ {Γ A}
                  → ▹ (∀ Γ A → Val Γ A → Part (Nf Γ A))
                  → Ne Val Γ A → Part (Ne Nf Γ A)
  nereadback-body     r▹ (ne-` x)       = now (ne-` x)
  nereadback-body {Γ} r▹ (ne-· {A} n v) = nereadback-body r▹ n >>=ᵖ λ m →
                                          mapᵖ (ne-· m) (readback-body r▹ Γ A v)

  eta-body : ∀ {Γ A B}
           → ▹ (∀ Γ A → Val Γ A → Part (Nf Γ A))
           → Val Γ (A ⇒ B) → ▹ Part (Nf (Γ ﹐ A) B)
  eta-body {Γ} {A} {B} r▹ v =
    Part▹ id $
    apply (weakVal v) (v-ne (ne-` here)) >>=ᵖ λ w →
    ▹Part+ (r▹ ⊛ next (Γ ﹐ A) ⊛ next B ⊛ next w)  -- adds one more step!

readback : ∀ {Γ A}
         → Val Γ A → Part (Nf Γ A)
readback {Γ} {A} = fix readback-body Γ A

nereadback : ∀ {Γ A}
           → Ne Val Γ A → Part (Ne Nf Γ A)
nereadback = nereadback-body (dfix readback-body)

id-env : ∀ Γ → Env Γ Γ
id-env ∅       = ε
id-env (Γ ﹐ t) = env≤ wk (id-env Γ) 、 v-ne (ne-` here)

nf : ∀ {Γ A}
   → Γ ⊢ A → Part (Nf Γ A)
nf {Γ} t = eval t (id-env Γ) >>=ᵖ readback

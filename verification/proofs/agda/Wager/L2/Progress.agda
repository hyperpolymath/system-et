{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on typing derivations.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- T0, progress. The proof needs the operations of the grade structure
-- only: no law of the algebra is used.
open import Wager.L1.Signature
open import Wager.Grade.Algebra
import Wager.L2.Signature

module Wager.L2.Progress
  (S : Sig) (TS : Wager.L2.Signature.TSig S) (ops : GradeOps (Sig.TG S)) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Sigma using (_×_; Σ-syntax)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)

open import Wager.L1.Syntax S using (Ty; ★; []; TG; Con₁; arr; _⊗_; _⊕_; capp; base)
open import Wager.L1.Conversion S
open import Wager.L1.Heads S
open import Wager.L2.Typing S TS ops

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Canonical forms: the shape of a value comes from the head of its type.

private
  -- The type of a value in a trope state has the head `capp`.
  step-type : ∀ {o s} {X : Ty [] ★} → to o ≡ just s →
              DefEq (carrier o at to o) X → DefEq (capp s (carrier o)) X
  step-type {o = o} {X = X} p c = subst (λ m → DefEq (carrier o at m) X) p c

cf-arr : {γ : Usage n} {Γ : Cx n} {v : Tm n} {C : Ty [] ★} {q : TG} {A B : Ty [] ★} →
         Value v → γ ▸ Γ ⊢ v ∶ C → DefEq C (arr q A B) →
         Σ[ q' ∈ TG ] Σ[ A' ∈ Ty [] ★ ] Σ[ b ∈ Tm (suc n) ] (v ≡ tlam q' A' b)
cf-arr val (t-conv d e) c = cf-arr val d (d-trans e c)
cf-arr val (t-sub d le) c = cf-arr val d c
cf-arr v-lam          (t-lam d)    c = _ , _ , _ , refl
cf-arr (v-pair _ _)   (t-pair d e) c = ⊥.rec (headClash c refl)
cf-arr (v-inj₁ _)     (t-inj₁ d)   c = ⊥.rec (headClash c refl)
cf-arr (v-inj₂ _)     (t-inj₂ d)   c = ⊥.rec (headClash c refl)
cf-arr v-lit          (t-lit ℓ)    c = ⊥.rec (headClash c refl)
cf-arr (v-step val p) (t-step o d) c = ⊥.rec (headClash (step-type p c) refl)

cf-prod : {γ : Usage n} {Γ : Cx n} {v : Tm n} {C A B : Ty [] ★} →
          Value v → γ ▸ Γ ⊢ v ∶ C → DefEq C (A ⊗ B) →
          Σ[ v₁ ∈ Tm n ] Σ[ v₂ ∈ Tm n ] (v ≡ pair v₁ v₂) × Value v₁ × Value v₂
cf-prod val (t-conv d e) c = cf-prod val d (d-trans e c)
cf-prod val (t-sub d le) c = cf-prod val d c
cf-prod v-lam          (t-lam d)    c = ⊥.rec (headClash c refl)
cf-prod (v-pair w₁ w₂) (t-pair d e) c = _ , _ , refl , w₁ , w₂
cf-prod (v-inj₁ _)     (t-inj₁ d)   c = ⊥.rec (headClash c refl)
cf-prod (v-inj₂ _)     (t-inj₂ d)   c = ⊥.rec (headClash c refl)
cf-prod v-lit          (t-lit ℓ)    c = ⊥.rec (headClash c refl)
cf-prod (v-step val p) (t-step o d) c = ⊥.rec (headClash (step-type p c) refl)

cf-sum : {γ : Usage n} {Γ : Cx n} {v : Tm n} {C A B : Ty [] ★} →
         Value v → γ ▸ Γ ⊢ v ∶ C → DefEq C (A ⊕ B) →
         (Σ[ w ∈ Tm n ] (v ≡ inj₁ w) × Value w) ⊎ (Σ[ w ∈ Tm n ] (v ≡ inj₂ w) × Value w)
cf-sum val (t-conv d e) c = cf-sum val d (d-trans e c)
cf-sum val (t-sub d le) c = cf-sum val d c
cf-sum v-lam          (t-lam d)    c = ⊥.rec (headClash c refl)
cf-sum (v-pair _ _)   (t-pair d e) c = ⊥.rec (headClash c refl)
cf-sum (v-inj₁ w)     (t-inj₁ d)   c = inl (_ , refl , w)
cf-sum (v-inj₂ w)     (t-inj₂ d)   c = inr (_ , refl , w)
cf-sum v-lit          (t-lit ℓ)    c = ⊥.rec (headClash c refl)
cf-sum (v-step val p) (t-step o d) c = ⊥.rec (headClash (step-type p c) refl)

------------------------------------------------------------------------
-- Progress.

Progress : Tm 0 → Type
Progress t = Value t ⊎ (Σ[ t' ∈ Tm 0 ] (t ⟶ t'))

private
  maybe-case : (m : Maybe Con₁) → (m ≡ nothing) ⊎ (Σ[ s ∈ Con₁ ] (m ≡ just s))
  maybe-case nothing  = inl refl
  maybe-case (just s) = inr (s , refl)

  app-progress : {γ : Usage 0} {Γ : Cx 0} {f a : Tm 0} {q : TG} {A B : Ty [] ★} →
                 γ ▸ Γ ⊢ f ∶ arr q A B → Progress f → Progress a → Progress (tapp f a)
  app-progress d (inr (f' , r)) _              = inr (_ , ξ-app₁ r)
  app-progress d (inl vf)       (inr (a' , r)) = inr (_ , ξ-app₂ vf r)
  app-progress {a = a} d (inl vf) (inl va) =
    let (q' , A' , b , p) = cf-arr vf d d-refl
    in inr (subst (λ z → Σ[ t' ∈ Tm 0 ] (tapp z a ⟶ t')) (sym p) (_ , β-lam va))

  pair-progress : {s t : Tm 0} → Progress s → Progress t → Progress (pair s t)
  pair-progress (inr (s' , r)) _              = inr (_ , ξ-pair₁ r)
  pair-progress (inl vs)       (inr (t' , r)) = inr (_ , ξ-pair₂ vs r)
  pair-progress (inl vs)       (inl vt)       = inl (v-pair vs vt)

  letp-progress : {γ : Usage 0} {Γ : Cx 0} {s : Tm 0} {b : Tm 2} {A B : Ty [] ★} →
                  γ ▸ Γ ⊢ s ∶ A ⊗ B → Progress s → Progress (letp s b)
  letp-progress d (inr (s' , r)) = inr (_ , ξ-letp r)
  letp-progress {b = b} d (inl vs) =
    let (v₁ , v₂ , p , w₁ , w₂) = cf-prod vs d d-refl
    in inr (subst (λ z → Σ[ t' ∈ Tm 0 ] (letp z b ⟶ t')) (sym p) (_ , β-pair w₁ w₂))

  case-progress : {γ : Usage 0} {Γ : Cx 0} {s : Tm 0} {l r : Tm 1} {A B : Ty [] ★} →
                  γ ▸ Γ ⊢ s ∶ A ⊕ B → Progress s → Progress (case s l r)
  case-progress d (inr (s' , r)) = inr (_ , ξ-case r)
  case-progress {l = l} {r = r} d (inl vs) with cf-sum vs d d-refl
  ... | inl (w , p , vw) =
        inr (subst (λ z → Σ[ t' ∈ Tm 0 ] (case z l r ⟶ t')) (sym p) (_ , β-inj₁ vw))
  ... | inr (w , p , vw) =
        inr (subst (λ z → Σ[ t' ∈ Tm 0 ] (case z l r ⟶ t')) (sym p) (_ , β-inj₂ vw))

  inj₁-progress : {t : Tm 0} → Progress t → Progress (inj₁ t)
  inj₁-progress (inl v)        = inl (v-inj₁ v)
  inj₁-progress (inr (t' , r)) = inr (_ , ξ-inj₁ r)

  inj₂-progress : {t : Tm 0} → Progress t → Progress (inj₂ t)
  inj₂-progress (inl v)        = inl (v-inj₂ v)
  inj₂-progress (inr (t' , r)) = inr (_ , ξ-inj₂ r)

  step-progress : (o : Op) {t : Tm 0} → Progress t → Progress (step o t)
  step-progress o (inr (t' , r)) = inr (_ , ξ-step r)
  step-progress o (inl v) with maybe-case (to o)
  ... | inl p       = inr (_ , β-strip v p)
  ... | inr (s , p) = inl (v-step v p)

progress : {γ : Usage 0} {Γ : Cx 0} {t : Tm 0} {A : Ty [] ★} →
           γ ▸ Γ ⊢ t ∶ A → Progress t
progress (t-lam d)      = inl v-lam
progress (t-app d e)    = app-progress d (progress d) (progress e)
progress (t-pair d e)   = pair-progress (progress d) (progress e)
progress (t-letp d e)   = letp-progress d (progress d)
progress (t-inj₁ d)     = inj₁-progress (progress d)
progress (t-inj₂ d)     = inj₂-progress (progress d)
progress (t-case d l r) = case-progress d (progress d)
progress (t-lit ℓ)      = inl v-lit
progress (t-step o d)   = step-progress o (progress d)
progress (t-conv d e)   = progress d
progress (t-sub d le)   = progress d

{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Stage 8. Proofs of T8-Conv, T8-Inst and T8-Closed.
open import Wager.L1.Signature
open import Wager.Grade.Algebra
import Wager.L2.Signature

module Wager.Poly.Proofs
  (S : Sig) (TS : Wager.L2.Signature.TSig S) (ops : GradeOps (Sig.TG S)) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)
open import Wager.L1.Syntax S
open import Wager.L1.SyntaxLemmas S
open import Wager.L1.Conversion S
open import Wager.L2.Term S TS using (Lit; litTy; Op; carrier; from; to; _at_)
import Wager.L2.Typing S TS ops as C
import Wager.L2.Progress
import Wager.L2.Preservation
open import Wager.Poly.Typing S TS ops
open import Wager.Poly.Statements S TS ops

private
  variable
    Γ Δ Δ' : Ctx
    k j : Kind

-- Substitution and β.
sub-β : (σ : TySub Δ' Δ) (b : Ty (j ∷ Δ) k) (u : Ty Δ j) →
        sub σ (b [ u ]) ≡ sub (exts σ) b [ sub σ u ]
sub-β σ b u =
  sub-sub σ (u ∷ₛ ids) b
  ∙ cong (λ τ → sub τ b) (subExt pt)
  ∙ sym (sub-sub (sub σ u ∷ₛ ids) (exts σ) b)
  where
  pt : ∀ k x → sub σ ((u ∷ₛ ids) k x) ≡ sub (sub σ u ∷ₛ ids) (exts σ k x)
  pt k vz     = refl
  pt k (vs x) = sym (sub-ren (sub σ u ∷ₛ ids) wk (σ k x) ∙ sub-id (σ k x))

sub-resTy : (σ : TySub Δ' Δ) (x : Base ⊎ Prim) (A : Ty Δ ★) →
            sub σ (resTy x A) ≡ resTy x (sub σ A)
sub-resTy σ (inl b) A = refl
sub-resTy σ (inr q) A = refl

t8-conv : T8-Conv
t8-conv σ d-refl          = d-refl
t8-conv σ (d-sym d)       = d-sym (t8-conv σ d)
t8-conv σ (d-trans d e)   = d-trans (t8-conv σ d) (t8-conv σ e)
t8-conv σ (d-beta b u)    =
  d-trans (d-beta (sub (exts σ) b) (sub σ u)) (≡→DefEq (sym (sub-β σ b u)))
t8-conv σ (d-capp d)      = d-capp (t8-conv σ d)
t8-conv σ (d-papp d)      = d-papp (t8-conv σ d)
t8-conv σ (d-arr d e)     = d-arr (t8-conv σ d) (t8-conv σ e)
t8-conv σ (d-prod d e)    = d-prod (t8-conv σ d) (t8-conv σ e)
t8-conv σ (d-sum d e)     = d-sum (t8-conv σ d) (t8-conv σ e)
t8-conv σ (d-lam d)       = d-lam (t8-conv (exts σ) d)
t8-conv σ (d-app d e)     = d-app (t8-conv σ d) (t8-conv σ e)
t8-conv σ (δ-base p b)    = δ-base p b
t8-conv σ (δ-capp p c A)  =
  d-trans (δ-capp p c (sub σ A)) (≡→DefEq (sym (sub-resTy σ (onCon p c) A)))
t8-conv σ (δ-arr p q A B) = δ-arr p q (sub σ A) (sub σ B)
t8-conv σ (δ-prod p A B)  = δ-prod p (sub σ A) (sub σ B)
t8-conv σ (δ-sum p A B)   = δ-sum p (sub σ A) (sub σ B)

-- A closed type does not change under a substitution.
sub-⇑ : (σ : TySub Δ' Δ) (A : Ty [] ★) → sub σ (⇑ A) ≡ ⇑ A
sub-⇑ σ A =
  sub-ren σ εᵣ A
  ∙ cong (λ τ → sub τ A) (subExt (λ k ()))
  ∙ sym (sub-ren ids εᵣ A)
  ∙ sub-id (ren εᵣ A)

-- Transport of a derivation along a path of contexts or of types.
-- The usage, the term and the other index are explicit in each motive.
private
  cxᵖ : ∀ {n} {γ : Usage n} {G G' : Cxᵖ Δ n} {t : Tmᵖ Δ n} {A : Ty Δ ★} →
        G ≡ G' → γ ▸ G ⊢ᵖ t ∶ A → γ ▸ G' ⊢ᵖ t ∶ A
  cxᵖ {γ = γ} {t = t} {A = A} p d = subst (λ G → γ ▸ G ⊢ᵖ t ∶ A) p d

  tyᵖ : ∀ {n} {γ : Usage n} {G : Cxᵖ Δ n} {t : Tmᵖ Δ n} {A A' : Ty Δ ★} →
        A ≡ A' → γ ▸ G ⊢ᵖ t ∶ A → γ ▸ G ⊢ᵖ t ∶ A'
  tyᵖ {γ = γ} {G = G} {t = t} p d = subst (λ T → γ ▸ G ⊢ᵖ t ∶ T) p d

  cxᶜ : ∀ {n} {γ : Usage n} {G G' : C.Cx n} {t : C.Tm n} {A : Ty [] ★} →
        G ≡ G' → γ C.▸ G ⊢ t ∶ A → γ C.▸ G' ⊢ t ∶ A
  cxᶜ {γ = γ} {t = t} {A = A} p d = subst (λ G → γ C.▸ G ⊢ t ∶ A) p d

  tyᶜ : ∀ {n} {γ : Usage n} {G : C.Cx n} {t : C.Tm n} {A A' : Ty [] ★} →
        A ≡ A' → γ C.▸ G ⊢ t ∶ A → γ C.▸ G ⊢ t ∶ A'
  tyᶜ {γ = γ} {G = G} {t = t} p d = subst (λ T → γ C.▸ G ⊢ t ∶ T) p d

private
  cx-▹ : ∀ {n} (σ : TySub Δ' Δ) (Γ : Cxᵖ Δ n) (A : Ty Δ ★) →
         (λ i → sub σ ((Γ ▹ᵖ A) i)) ≡ ((λ i → sub σ (Γ i)) ▹ᵖ sub σ A)
  cx-▹ σ Γ A = funExt λ { zero → refl ; (suc i) → refl }

t8-inst : T8-Inst
t8-inst σ (t-var i) = t-var i
t8-inst σ {Γ = Γ} (t-lam {A = A} d) =
  t-lam (cxᵖ (cx-▹ σ Γ A) (t8-inst σ d))
t8-inst σ (t-app d e) = t-app (t8-inst σ d) (t8-inst σ e)
t8-inst σ (t-pair d e) = t-pair (t8-inst σ d) (t8-inst σ e)
t8-inst σ {Γ = Γ} (t-letp {A = A} {B = B} d e) =
  t-letp (t8-inst σ d)
    (cxᵖ
      (cx-▹ σ (Γ ▹ᵖ A) B ∙ cong (_▹ᵖ sub σ B) (cx-▹ σ Γ A))
      (t8-inst σ e))
t8-inst σ (t-inj₁ d) = t-inj₁ (t8-inst σ d)
t8-inst σ (t-inj₂ d) = t-inj₂ (t8-inst σ d)
t8-inst σ {Γ = Γ} (t-case {A = A} {B = B} d l r) =
  t-case (t8-inst σ d)
    (cxᵖ (cx-▹ σ Γ A) (t8-inst σ l))
    (cxᵖ (cx-▹ σ Γ B) (t8-inst σ r))
t8-inst σ (t-lit ℓ) = t-lit ℓ
t8-inst σ (t-step o d) =
  tyᵖ (sym (sub-⇑ σ (carrier o at to o)))
    (t-step o (tyᵖ (sub-⇑ σ (carrier o at from o)) (t8-inst σ d)))
t8-inst σ (t-conv d e) = t-conv (t8-inst σ d) (t8-conv σ e)
t8-inst σ (t-sub d le) = t-sub (t8-inst σ d) le

-- With no type variable, `⇑` is the identity.
⇑-closed : (A : Ty [] ★) → ⇑ A ≡ A
⇑-closed A = cong (λ r → ren r A) (renExt (λ k ())) ∙ ren-id A

private
  cx-C : ∀ {n} (Γ : Cxᵖ [] n) (A : Ty [] ★) → (Γ ▹ᵖ A) ≡ (Γ C.▹ᶜ A)
  cx-C Γ A = funExt λ { zero → refl ; (suc i) → refl }

t8-closed : T8-Closed
t8-closed (t-var i) = C.t-var i
t8-closed {Γ = Γ} (t-lam {A = A} d) =
  C.t-lam (cxᶜ (cx-C Γ A) (t8-closed d))
t8-closed (t-app d e) = C.t-app (t8-closed d) (t8-closed e)
t8-closed (t-pair d e) = C.t-pair (t8-closed d) (t8-closed e)
t8-closed {Γ = Γ} (t-letp {A = A} {B = B} d e) =
  C.t-letp (t8-closed d)
    (cxᶜ
      (cx-C (Γ ▹ᵖ A) B ∙ cong (C._▹ᶜ B) (cx-C Γ A)) (t8-closed e))
t8-closed (t-inj₁ d) = C.t-inj₁ (t8-closed d)
t8-closed (t-inj₂ d) = C.t-inj₂ (t8-closed d)
t8-closed {Γ = Γ} (t-case {A = A} {B = B} d l r) =
  C.t-case (t8-closed d)
    (cxᶜ (cx-C Γ A) (t8-closed l))
    (cxᶜ (cx-C Γ B) (t8-closed r))
t8-closed (t-lit ℓ) = C.t-lit ℓ
t8-closed (t-step o d) =
  tyᶜ (sym (⇑-closed (carrier o at to o)))
    (C.t-step o (tyᶜ (⇑-closed (carrier o at from o)) (t8-closed d)))
t8-closed (t-conv d e) = C.t-conv (t8-closed d) e
t8-closed (t-sub d le) = C.t-sub (t8-closed d) le

------------------------------------------------------------------------
-- The second freeze: each closed instance is a term of the target, so
-- the theorems of the target apply to it.

t8-closed-instance : T8-Closed-Instance
t8-closed-instance σ d = t8-closed (t8-inst σ d)

-- Progress uses the operations only, and no law.
t8-instance-progress : T8-Instance-Progress
t8-instance-progress σ d =
  Wager.L2.Progress.progress S TS ops (t8-closed-instance σ d)

t8-instance-preservation : T8-Instance-Preservation
t8-instance-preservation laws σ d r =
  Wager.L2.Preservation.preservation S TS (record { ops = ops ; laws = laws })
    (t8-closed-instance σ d) r

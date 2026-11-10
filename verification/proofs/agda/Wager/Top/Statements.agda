{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- The variant of the translation with a grade q: the statements,
-- frozen before their proofs. This file imports definitions and no
-- proof.
--
-- The question of the owner: is the second addition of the verdict (an
-- unrestricted grade 𝟙) stronger than necessary? The candidate: a top
-- grade q is enough, when the translation writes q.
open import Cubical.Foundations.Prelude
open import Wager.FC.Signature
open import Wager.Grade.Algebra
import Wager.Trans.Scheme

module Wager.Top.Statements
  (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
  {R : Type} (ops : GradeOps R) (q : R) where

open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Sigma using (_×_; Σ-syntax)

open import Wager.Role.Role using (rep; nom)
open import Wager.FC.Types SS
open import Wager.FC.Coercion SS
open import Wager.FC.Term SS
open import Wager.Top.Translation SS Sc ops q
open import Wager.Trans.Target SS Sc opsq using (tSig; tTSig; T; arr; ★; [])
open import Wager.Trans.Coercion SS Sc opsq using (Tm; fwd; eraseT)
import Wager.Trans.Coercion SS Sc ops as Stage4
open import Wager.L1.Eval tSig using (nf)
open import Wager.L2.Typing tSig tTSig ops using (Usage; Cx; _▸_⊢_∶_; 0ᵘ)
open import Wager.Erased.LogRel litTy
open GradeOps ops using (𝟙; _≤_)

-- The grade q is a top grade.
IsTop : Type
IsTop = ∀ r → r ≤ q

-- Top-Coercion-Typed. For the laws of a grade algebra and a source
-- signature that passes the role check: the transformer of a
-- representational coercion maps a term of the type `T τ` to a term of
-- the type `T σ`, with the same usage vector. The types have the grade
-- q on each arrow. The statement has NO hypothesis on q.
Top-Coercion-Typed : Type
Top-Coercion-Typed =
  GradeLaws ops → WellRoled →
  ∀ {τ σ} (c : Co rep τ σ) {n} {γ : Usage n} {Γ : Cx n} {t : Tm n} →
  γ ▸ Γ ⊢ t ∶ T τ → γ ▸ Γ ⊢ fwd (coIq rep c) t ∶ T σ

-- Top-Coerce-Typed. The coercion function, with the grade q on its
-- binder, is typed when 𝟙 ≤ q.
Top-Coerce-Typed : Type
Top-Coerce-Typed =
  GradeLaws ops → WellRoled → 𝟙 ≤ q →
  ∀ {τ σ} (c : Co rep τ σ) {n} (Γ : Cx n) →
  0ᵘ ▸ Γ ⊢ coerceTq c ∶ arr q (T τ) (T σ)

-- Top-Typing-All. THE CANDIDATE OF THE OWNER, for each term of the
-- source fragment: with a top grade q, the translation of a term of
-- the type τ has the type `T τ`, with the usage q for each variable.
-- This is a statement to prove or to refute. It is not claimed here.
Top-Typing-All : Type
Top-Typing-All =
  GradeLaws ops → WellRoled → IsTop →
  ∀ {n} {Γ : SCx n} {τ} (e : STm Γ τ) →
  (λ _ → q) ▸ (λ i → T (Γ i)) ⊢ trq e ∶ T τ

-- Top-Typing. The candidate for a source term with no elimination of a
-- pair and no `case`.
Top-Typing : Type
Top-Typing =
  GradeLaws ops → WellRoled → IsTop →
  ∀ {n} {Γ : SCx n} {τ} (e : STm Γ τ) → NoElim e →
  (λ _ → q) ▸ (λ i → T (Γ i)) ⊢ trq e ∶ T τ

-- Top-Same-Erasure. The variant and the translation of Stage 4 have
-- one erasure: the erasure does not read a grade.
Top-Same-Erasure : Type
Top-Same-Erasure =
  ∀ {n} {Γ : SCx n} {τ} (e : STm Γ τ) →
  eraseT (trq e) ≡ Stage4.eraseT (Stage4.tr e)

-- Top-Behaviour. T5, behaviour, for the variant: for a closed source
-- term, the erased source term and the erased translation evaluate,
-- and the two values are observationally equal at the erased type.
Top-Behaviour : Type
Top-Behaviour =
  WellRoled → ∀ {τ} (e : STm ∅ˢ τ) →
  Σ[ v ∈ UVal ] Σ[ w ∈ UVal ]
    (∅ᵉ ⊢ eraseTm e ⇓ v) × (∅ᵉ ⊢ eraseT (trq e) ⇓ w) × 𝒱 (er τ) v w

-- Top-Nominal. T6 for the variant: for each nominal coercion, the two
-- translated types have one normal form.
Top-Nominal : Type
Top-Nominal = ∀ {τ σ} → Co nom τ σ → nf (T τ) ≡ nf (T σ)

{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Stage 8. The statements, frozen before their proofs.
open import Wager.L1.Signature
open import Wager.Grade.Algebra
import Wager.L2.Signature

module Wager.Poly.Statements
  (S : Sig) (TS : Wager.L2.Signature.TSig S) (ops : GradeOps (Sig.TG S)) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.Data.Sum.Base using (_⊎_)
open import Wager.L1.Syntax S
open import Wager.L1.Conversion S
open import Wager.L2.Typing S TS ops using (_▸_⊢_∶_; Tm; Value; _⟶_)
open import Wager.Poly.Typing S TS ops

-- T8-Conv. Conversion of types is stable under a substitution of types.
T8-Conv : Type
T8-Conv = ∀ {Δ Δ' k} (σ : TySub Δ' Δ) {A B : Ty Δ k} →
          DefEq A B → DefEq (sub σ A) (sub σ B)

-- T8-Inst. Each instance of a typed open term is typed, with the same
-- usage. The type and the context are the instances.
T8-Inst : Type
T8-Inst = ∀ {Δ Δ' n} (σ : TySub Δ' Δ) {γ : Usage n} {Γ : Cxᵖ Δ n}
          {t : Tmᵖ Δ n} {A : Ty Δ ★} →
          γ ▸ Γ ⊢ᵖ t ∶ A →
          γ ▸ (λ i → sub σ (Γ i)) ⊢ᵖ inst σ t ∶ sub σ A

-- T8-Closed. A typed term with no type variable is a typed term of the
-- target calculus of stages 1 to 5. So T0 to T6 apply to each closed
-- instance of an open term.
T8-Closed : Type
T8-Closed = ∀ {n} {γ : Usage n} {Γ : Cxᵖ [] n} {t : Tmᵖ [] n} {A : Ty [] ★} →
            γ ▸ Γ ⊢ᵖ t ∶ A → γ ▸ Γ ⊢ ⌊ t ⌋ ∶ A

------------------------------------------------------------------------
-- The second freeze of Stage 8. The 3 statements above did not change.

-- T8-Closed-Instance. Each closed instance of a typed open term is a
-- typed term of the target calculus of stages 1 to 5, with the same
-- usage. Its type and its context are the instances.
T8-Closed-Instance : Type
T8-Closed-Instance = ∀ {Δ n} (σ : TySub [] Δ) {γ : Usage n} {Γ : Cxᵖ Δ n}
                     {t : Tmᵖ Δ n} {A : Ty Δ ★} →
                     γ ▸ Γ ⊢ᵖ t ∶ A →
                     γ ▸ (λ i → sub σ (Γ i)) ⊢ ⌊ inst σ t ⌋ ∶ sub σ A

-- T8-Instance-Progress. T0, part 3 applies to each closed instance: an
-- instance of a typed open term with no term variable is a value, or
-- it can make one reduction step.
T8-Instance-Progress : Type
T8-Instance-Progress = ∀ {Δ} (σ : TySub [] Δ) {γ : Usage 0} {Γ : Cxᵖ Δ 0}
                       {t : Tmᵖ Δ 0} {A : Ty Δ ★} →
                       γ ▸ Γ ⊢ᵖ t ∶ A →
                       Value ⌊ inst σ t ⌋ ⊎ (Σ[ t' ∈ Tm 0 ] (⌊ inst σ t ⌋ ⟶ t'))

-- T8-Instance-Preservation. T0, part 2 applies to each closed instance,
-- when the operations satisfy the laws of a grade algebra: a reduction
-- step of an instance keeps the instance of the type, and the usage.
T8-Instance-Preservation : Type
T8-Instance-Preservation = GradeLaws ops →
                           ∀ {Δ n} (σ : TySub [] Δ) {γ : Usage n} {Γ : Cxᵖ Δ n}
                           {t : Tmᵖ Δ n} {A : Ty Δ ★} {t' : Tm n} →
                           γ ▸ Γ ⊢ᵖ t ∶ A → ⌊ inst σ t ⌋ ⟶ t' →
                           γ ▸ (λ i → sub σ (Γ i)) ⊢ t' ∶ sub σ A

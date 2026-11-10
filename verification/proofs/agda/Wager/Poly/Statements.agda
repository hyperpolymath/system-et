{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
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
open import Wager.L1.Syntax S
open import Wager.L1.Conversion S
open import Wager.L2.Typing S TS ops using (_▸_⊢_∶_)
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

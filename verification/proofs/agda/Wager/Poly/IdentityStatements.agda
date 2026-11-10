{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Stage 8. The GADT program of Stage 6 and open types: the statements,
-- frozen before their proofs.
--
-- The signature is the signature of `Wager.Identity.Instance`, the one
-- signature of this development that has an identity family. The
-- start has one base constant b₀ at least.
open import Cubical.Foundations.Prelude
open import Wager.Grade.Algebra

module Wager.Poly.IdentityStatements
  (B₀ L₀ : Type) (ty₀ : L₀ → B₀) {R : Type} (ops : GradeOps R) (b₀ : B₀) where

open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Identity.Instance B₀ L₀ ty₀ ops
import Wager.Identity.Family
open import Wager.L1.Syntax sig
open import Wager.L1.Conversion sig
open Wager.Identity.Family.IdFamily family using (Id)

-- The base type of the start.
I₀ : Ty [] ★
I₀ = base (cb b₀)

-- The data of the GADT program of Stage 6, part 2, at the closed type
-- α (`Wager.Examples.Stage6Identity.Gⁱ`, with b₀ for `int`).
Gᵍ : Ty [] ★ → Ty [] ★
Gᵍ α = (base (Id α I₀) ⊗ α) ⊕ (base (Id α (I₀ ⊕ I₀)) ⊗ α)

-- T8-Evidence-Rigid. No open type with one type variable has the
-- evidence type `Id α B` as its instance at each closed type α.
-- The identity family is a family of base constants, and a
-- substitution does not change a base constant.
T8-Evidence-Rigid : Type
T8-Evidence-Rigid =
  (B : Ty [] ★) →
  ¬ (Σ[ E ∈ Ty (★ ∷ []) ★ ] (∀ α → DefEq (E [ α ]) (base (Id α B))))

-- T8-Gadt-Not-Open. No open type with one type variable has the data
-- type of the GADT program as its instance at each closed type α.
-- The statement is about a type. It is not about each encoding of the
-- program (DESIGN-CHOICES.adoc, DC-8.6).
T8-Gadt-Not-Open : Type
T8-Gadt-Not-Open =
  ¬ (Σ[ G ∈ Ty (★ ∷ []) ★ ] (∀ α → DefEq (G [ α ]) (Gᵍ α)))

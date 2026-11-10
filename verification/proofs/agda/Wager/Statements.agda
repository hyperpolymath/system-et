{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- THE HEADLINE THEOREMS OF THE WAGER EXPERIMENT, AS TYPES ONLY.
--
-- A reviewer reads this file. It imports definitions and no proof.
-- Each statement is a type with a plain-English reading. The module
-- `Wager.Proofs` gives one inhabitant for each statement.
--
-- A statement in this file is frozen when its stage starts. A change
-- to a frozen statement is recorded in VERDICT.adoc.
module Wager.Statements where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_; Σ-syntax)
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin)

open import Wager.Grade.Algebra
open import Wager.Grade.Affine using (Affine)
open import Wager.Grade.Level using (Sec)
open import Wager.L1.Signature
import Wager.L1.Syntax
import Wager.L1.Conversion
import Wager.L1.Eval
import Wager.L1.Normal
import Wager.L2.Signature
import Wager.L2.Typing

------------------------------------------------------------------------
-- STAGE 1
------------------------------------------------------------------------

-- The two instances that show that T0 is not empty.
--
-- English: the 3-point structure {0, 1, ω} with the systemet order is a
-- grade algebra. All 15 law fields of the Lean class hold.
Affine-Is-Grade-Algebra : Type₁
Affine-Is-Grade-Algebra = GradeAlgebra Affine

-- English: the 2-point lattice Low ≤ High is a grade algebra
-- (+ is meet, · is join, 𝟘 is High, 𝟙 is Low).
Level-Is-Grade-Algebra : Type₁
Level-Is-Grade-Algebra = GradeAlgebra Sec

module L1-Statements (S : Sig) where
  open Wager.L1.Syntax S
  open Wager.L1.Conversion S
  open Wager.L1.Normal S
  open Wager.L1.Eval S

  -- L1 (equality is conversion; ET-2 for this language).
  --
  -- English: for each signature, two type-level terms of the same kind
  -- are convertible if and only if the total normalizer `nf` gives the
  -- same normal form for both. `DefEq` is β, the δ-rules of the
  -- signature primitives, equivalence and congruence. There is no η.
  L1-Equality : Type
  L1-Equality =
    ∀ {Γ : Ctx} {k : Kind} (t u : Ty Γ k) →
      (DefEq t u → nf t ≡ nf u) × (nf t ≡ nf u → DefEq t u)

-- T0 holds for EACH signature S, EACH term signature TS, and EACH
-- grade algebra R on the term grades. The typing rules take the
-- operations of R only.
module T0-Statements
  (S : Sig) (TS : Wager.L2.Signature.TSig S) (R : GradeAlgebra (Sig.TG S)) where
  open Wager.L1.Syntax S using (Ty; ★; [])
  open Wager.L2.Typing S TS (GradeAlgebra.ops R)

  -- T0, part 1 (graded substitution).
  --
  -- English: let the term t have the type B in a context with one more
  -- variable of type A, and let t use that variable at the grade q and
  -- the other variables as γ says. Let u have the type A and use the
  -- variables as δ says. Then t with u for the variable has the type B
  -- and uses the variables as γ + q · δ says.
  T0-Substitution : Type
  T0-Substitution =
    ∀ {n : ℕ} {γ δ : Usage n} {Γ : Cx n} {q} {A B : Ty [] ★}
      {t : Tm (suc n)} {u : Tm n} →
      (γ ▹ q) ▸ (Γ ▹ᶜ A) ⊢ t ∶ B →
      δ ▸ Γ ⊢ u ∶ A →
      (γ +ᵘ (q ·ᵘ δ)) ▸ Γ ⊢ t [ u ]ᵗ ∶ B

  -- T0, part 2 (preservation).
  --
  -- English: if a term has a type with a usage vector, and the term
  -- makes one reduction step, then the result has the same type with
  -- the same usage vector, in the same context.
  T0-Preservation : Type
  T0-Preservation =
    ∀ {n : ℕ} {γ : Usage n} {Γ : Cx n} {t t' : Tm n} {A : Ty [] ★} →
      γ ▸ Γ ⊢ t ∶ A → t ⟶ t' → γ ▸ Γ ⊢ t' ∶ A

  -- T0, part 3 (progress).
  --
  -- English: a closed term that has a type is a value, or it can make
  -- one reduction step.
  T0-Progress : Type
  T0-Progress =
    ∀ {γ : Usage 0} {Γ : Cx 0} {t : Tm 0} {A : Ty [] ★} →
      γ ▸ Γ ⊢ t ∶ A → Value t ⊎ (Σ[ t' ∈ Tm 0 ] (t ⟶ t'))

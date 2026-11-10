{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- One inhabitant for each statement of `Wager.Statements`.
-- The identifiers in this file are the identifiers that VERDICT.adoc
-- names.
module Wager.Proofs where

open import Cubical.Foundations.Prelude

open import Wager.Statements
open import Wager.Grade.Algebra
open import Wager.Grade.Affine using (affine)
open import Wager.Grade.Level using (level)
open import Wager.L1.Signature
import Wager.L1.Equality
import Wager.L2.Signature
import Wager.L2.Substitution
import Wager.L2.Preservation
import Wager.L2.Progress

------------------------------------------------------------------------
-- STAGE 1
------------------------------------------------------------------------

affine-is-grade-algebra : Affine-Is-Grade-Algebra
affine-is-grade-algebra = affine

level-is-grade-algebra : Level-Is-Grade-Algebra
level-is-grade-algebra = level

module _ (S : Sig) where
  open L1-Statements S
  open Wager.L1.Equality S

  l1-equality : L1-Equality
  l1-equality t u = defEq→nf , nf→defEq

module _ (S : Sig) (TS : Wager.L2.Signature.TSig S) (R : GradeAlgebra (Sig.TG S)) where
  open T0-Statements S TS R

  t0-substitution : T0-Substitution
  t0-substitution = Wager.L2.Substitution.subst-lemma S TS R

  t0-preservation : T0-Preservation
  t0-preservation = Wager.L2.Preservation.preservation S TS R

  -- Progress uses the operations only, and no law.
  t0-progress : T0-Progress
  t0-progress = Wager.L2.Progress.progress S TS (GradeAlgebra.ops R)

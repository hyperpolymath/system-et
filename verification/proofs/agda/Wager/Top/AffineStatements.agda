{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- The variant of the translation with a grade q, in the algebra
-- {0, 1, ω} with q = ω: the statements, frozen before their proofs.
-- The source signature is `taggedS rep`, with the row scheme.
module Wager.Top.AffineStatements where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Grade.Algebra
open import Wager.Grade.Affine using (affineOps; aω)
open import Wager.Role.Role using (rep)
open import Wager.FC.Tagged
import Wager.Trans.Scheme
import Wager.Top.Statements

private
  SS = taggedS rep
  Sc = Wager.Trans.Scheme.rowScheme SS

open Wager.Top.Statements SS Sc affineOps aω

-- English: ω is a top grade of the algebra {0, 1, ω}.
Omega-Is-Top : Type
Omega-Is-Top = IsTop

-- English: THE CANDIDATE IS FALSE for the whole source fragment, in
-- the algebra {0, 1, ω} with q = ω.
Top-Typing-All-Fails : Type
Top-Typing-All-Fails = ¬ Top-Typing-All

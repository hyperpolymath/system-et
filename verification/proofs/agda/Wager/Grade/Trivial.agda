{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The one-point grade algebra: no usage discipline.
-- In this algebra the grade 𝟙 is unrestricted (𝟘 ≤ 𝟙 and 𝟙 + 𝟙 ≤ 𝟙).
-- Stage 4 uses it for the translation of whole source programs,
-- because System FC has no usage discipline.
module Wager.Grade.Trivial where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (Unit; tt)

open import Wager.Grade.Algebra

trivialOps : GradeOps Unit
trivialOps = record
  { _+_ = λ _ _ → tt ; _·_ = λ _ _ → tt ; 𝟘 = tt ; 𝟙 = tt ; _≤_ = λ _ _ → Unit }

trivialLaws : GradeLaws trivialOps
trivialLaws = record
  { add-assoc = λ _ _ _ → refl ; add-comm = λ _ _ → refl ; add-zero = λ _ → refl
  ; mul-assoc = λ _ _ _ → refl ; one-mul = λ _ → refl ; mul-one = λ _ → refl
  ; zero-mul = λ _ → refl ; mul-zero = λ _ → refl
  ; left-distrib = λ _ _ _ → refl ; right-distrib = λ _ _ _ → refl
  ; le-refl = λ _ → tt ; le-trans = λ _ _ _ _ _ → tt ; le-antisym = λ _ _ _ _ → refl
  ; add-mono = λ _ _ _ _ _ _ → tt ; mul-mono = λ _ _ _ _ _ _ → tt }

trivial : GradeAlgebra Unit
trivial = record { ops = trivialOps ; laws = trivialLaws }

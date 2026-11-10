{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- A composition table for roles, with the three properties that the
-- noninterference proof uses. `mul-zero` is not one of them, so the
-- GHC table is an instance too.
module Wager.Role.Table where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (Bool; true; false)

open import Wager.Grade.Algebra
open import Wager.Grade.Finite
open import Wager.Role.Role

record RoleTable : Type where
  field
    mul       : Role → Role → Role
    mul-assoc : ∀ a b c → mul (mul a b) c ≡ mul a (mul b c)
    mul-one   : ∀ a → mul a rep ≡ a
    mul-mono  : ∀ a b c d → leR a b ≡ true → leR c d ≡ true →
                leR (mul a c) (mul b d) ≡ true

-- The grade operations of a table: `+` is the maximum, 𝟘 is phantom,
-- 𝟙 is representational, and `≤` is the role order.
tableOps : RoleTable → GradeOps Role
tableOps T = record
  { _+_ = maxR ; _·_ = RoleTable.mul T ; 𝟘 = ph ; 𝟙 = rep
  ; _≤_ = λ a b → leR a b ≡ true }

-- The lawful table.
tableZ : RoleTable
tableZ = record
  { mul = mulZ
  ; mul-assoc = GradeLaws.mul-assoc roleZLaws
  ; mul-one   = GradeLaws.mul-one roleZLaws
  ; mul-mono  = GradeLaws.mul-mono roleZLaws }

-- The GHC table.
tableG : RoleTable
tableG = record
  { mul = mulG
  ; mul-assoc = GradeLawsExceptMulZero.mul-assoc roleGLaws14
  ; mul-one   = GradeLawsExceptMulZero.mul-one roleGLaws14
  ; mul-mono  = GradeLawsExceptMulZero.mul-mono roleGLaws14 }

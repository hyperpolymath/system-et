{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- What it means that a signature respects its declared grades.
--
-- An observer has a role:
--   a nominal observer           sees the identity of a type
--   a representational observer  sees a type up to `≈`
--   a phantom observer           sees nothing
-- A constant or a primitive with the parameter grade g is VALID when,
-- for each observer ρ: arguments that the observer `ρ · g` cannot tell
-- apart give results that the observer ρ cannot tell apart.
--
-- This file has definitions only. The composition table is a parameter.
open import Wager.Role.Signature
open import Wager.Role.Role

module Wager.Role.Validity (RS : RoleSig) (mul : Role → Role → Role) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (Unit)

open import Wager.L1.Syntax (toSig RS)
open import Wager.L1.Normal (toSig RS)
open import Wager.Role.RepEq RS

-- What an observer of each role can tell apart.
R★ : Role → CNf → CNf → Type
R★ ph  v w = Unit
R★ rep v w = v ≈ w
R★ nom v w = v ≡ w

record Valid : Type where
  field
    cvalid : ∀ c ρ {v w} → R★ (mul ρ (cgrade c)) v w → R★ ρ (ncapp c v) (ncapp c w)
    pvalid : ∀ p ρ {v w} → R★ (mul ρ (pgrade p)) v w → R★ ρ (inspect p v) (inspect p w)

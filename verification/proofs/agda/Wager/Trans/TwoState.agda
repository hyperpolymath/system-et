{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- What a translation of types must do, and what "two-state trope"
-- means (Stage 4, definitions only).
--
-- `Translation S` is a translation of the types of the source
-- signature SS into the target signature S that keeps three properties:
--   a nominal coercion becomes conversion;
--   a type-level function becomes a type-level function of the target;
--   two different base types stay different.
-- `TwoState` adds: each newtype with a parameter is ONE trope state on
-- its representation (the state does not depend on the parameter).
-- This is the form of Stage 2: `Int@age` and `Int@raw`.
open import Wager.FC.Signature

module Wager.Trans.TwoState (SS : SSig) where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Role.Role
open import Wager.L1.Signature
open import Wager.FC.Types SS
open import Wager.FC.Coercion SS
import Wager.L1.Syntax
import Wager.L1.Conversion

module _ (S : Sig) where
  open Wager.L1.Syntax S hiding (Base)
  open Wager.L1.Conversion S

  record Translation : Type where
    field
      T      : STy → Ty [] ★
      -- A nominal coercion becomes conversion.
      T-nom  : ∀ {τ σ} → Co nom τ σ → DefEq (T τ) (T σ)
      -- A type-level function becomes a type-level function of the target.
      FunG   : Fam → KG
      Fun    : (f : Fam) → Ty [] (★ ⇒[ FunG f ] ★)
      T-fam  : ∀ f τ → DefEq (T (fam f τ)) (app (Fun f) (T τ))
      -- Two different base types stay different.
      T-base : ∀ b b' → ¬ (b ≡ b') → ¬ DefEq (T (sbase b)) (T (sbase b'))

  record TwoState (t : Translation) : Type where
    open Translation t
    field
      -- One state for each newtype with a parameter.
      state : N₁ → Con₁
      -- The newtype is that state on the translation of its representation.
      T-nt  : ∀ N τ → DefEq (T (nt₁ N τ)) (capp (state N) (T (inst (body N) τ)))

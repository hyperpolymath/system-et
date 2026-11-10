{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The identity type of Stage 6, part 2, as entries of a signature
-- (DESIGN-CHOICES.adoc, DC-6.5).
--
-- The type language and the conversion relation do not change. The
-- identity type is a family of base constants: one constant `Id A B`
-- for each pair of closed types. Its one constructor is a literal
-- `rfl A` of the base type `Id A A`. The existing rule for literals
-- types it.
--
-- EQUALITY EVIDENCE IS NOW A TERM. A term of the type `base (Id A B)`
-- is evidence that the types A and B are equal. It is an ordinary
-- value: a function can take it, a pair can hold it.
--
-- The record does not say that a signature has such a family.
-- `Wager.Identity.Instance` gives one signature that has one.
open import Wager.L1.Signature
import Wager.L2.Signature
module Wager.Identity.Family (S : Sig) (TS : Wager.L2.Signature.TSig S) where

open import Cubical.Foundations.Prelude

open import Wager.L1.Syntax S
open import Wager.L1.Conversion S
open Wager.L2.Signature S
open TSig TS

record IdFamily : Type where
  field
    -- The family: a base constant for each pair of closed types.
    Id       : Ty [] ★ → Ty [] ★ → Base
    -- The family respects conversion in each index.
    Id-conv  : ∀ {A A' B B'} → DefEq A A' → DefEq B B' → Id A B ≡ Id A' B'
    -- The constructor: a literal on the diagonal.
    rfl      : Ty [] ★ → Lit
    rfl-ty   : ∀ A → litTy (rfl A) ≡ Id A A
    -- No literal is in the family off the diagonal: a literal of the
    -- base type `Id A B` shows that A and B are convertible.
    diagonal : ∀ ℓ {A B} → litTy ℓ ≡ Id A B → DefEq A B

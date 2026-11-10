{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The term-level part of the signature: literals and trope
-- transitions (docs/theory/07-tropes.adoc).
--
-- A trope state is a unary type constant s, and `A@s` is `capp s A`.
-- The raw state is the bare type A (DESIGN-CHOICES.adoc, DC-1.4).
-- Each operation o moves one carrier type from the state `from o` to
-- the state `to o`: this is the judgement `A@s ⟶ A@s'` of
-- 00-notation. An operation never changes the carrier type.
open import Wager.L1.Signature

module Wager.L2.Signature (S : Sig) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Maybe.Base using (Maybe; nothing; just) public

open import Wager.L1.Syntax S

record TSig : Type₁ where
  field
    -- Literals of base types.
    Lit   : Type
    litTy : Lit → Base
    -- Trope operations.
    Op      : Type
    carrier : Op → Ty [] ★
    from to : Op → Maybe Con₁

-- The carrier type A in the state m.
infix 31 _at_
_at_ : Ty [] ★ → Maybe Con₁ → Ty [] ★
A at nothing = A
A at just s  = capp s A

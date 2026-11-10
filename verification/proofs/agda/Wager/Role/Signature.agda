{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- A signature whose kind grades are roles.
--
-- It is a signature of the L1 language (Wager.L1.Signature) with the
-- carrier `Role` for kind grades, and one more datum: which unary
-- constants are newtype states. `A@s`, for a newtype state s, is the
-- newtype over the representation type A (DESIGN-CHOICES.adoc, DC-1.4).
module Wager.Role.Signature where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (Bool)
open import Cubical.Data.Sum.Base using (_⊎_)

open import Wager.L1.Signature
open import Wager.Role.Role

record RoleSig : Type₁ where
  field
    TG        : Type
    Base      : Type
    Con₁      : Type
    cgrade    : Con₁ → Role
    -- `true` for a newtype state, `false` for another generative constant.
    isNewtype : Con₁ → Bool
    Prim      : Type
    pgrade    : Prim → Role
    onBase    : Prim → Base → Base
    onCon     : Prim → Con₁ → Base ⊎ Prim
    onOther   : Prim → Base

toSig : RoleSig → Sig
toSig RS = record
  { KG = Role ; TG = TG ; Base = Base
  ; Con₁ = Con₁ ; cgrade = cgrade
  ; Prim = Prim ; pgrade = pgrade
  ; onBase = onBase ; onCon = onCon ; onOther = onOther }
  where open RoleSig RS

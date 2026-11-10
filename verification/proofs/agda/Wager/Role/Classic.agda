{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The concrete signature of Stage 2 (definitions only).
--
--   base types      Int, Bool, Char, Unit
--   newtype state   age:    Int@age is the newtype `Age` over Int,
--                           Int@raw is the bare type Int
--   constant        proxy:  a generative constant, `Proxy A`.
--                           Its parameter grade `pg` is a parameter of
--                           the signature, so that Stage 2 can test it
--   primitives      isAge:  tells the newtype from its representation
--                             a base type ↦ Bool,  A@age ↦ Char,
--                             Proxy A ↦ Bool,      other ↦ Unit
--                   deep:   on `Proxy A` it inspects A with isAge,
--                           on each other type it gives Unit
--   each primitive has the declared grade `nominal`
--   tropes          wrapAge: Int@raw → Int@age,  unwrapAge: Int@age → Int@raw
module Wager.Role.Classic where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)

open import Wager.Grade.Affine using (Affine)
open import Wager.Role.Role
open import Wager.Role.Signature
import Wager.L1.Syntax
import Wager.L2.Signature

data BaseName : Type where
  bInt bBool bChar bUnit : BaseName

data ConName : Type where
  age proxy : ConName

data PrimName : Type where
  isAge deep : PrimName

data OpName : Type where
  wrapAge unwrapAge : OpName

private
  cgradeC : Role → ConName → Role
  cgradeC pg age   = rep
  cgradeC pg proxy = pg

  isNewtypeC : ConName → Bool
  isNewtypeC age   = true
  isNewtypeC proxy = false

  onBaseC : PrimName → BaseName → BaseName
  onBaseC isAge _ = bBool
  onBaseC deep  _ = bUnit

  onConC : PrimName → ConName → BaseName ⊎ PrimName
  onConC isAge age   = inl bChar
  onConC isAge proxy = inl bBool
  onConC deep  age   = inl bUnit
  onConC deep  proxy = inr isAge

-- `pg` is the declared grade of the parameter of `proxy`.
classicSig : Role → RoleSig
classicSig pg = record
  { TG = Affine ; Base = BaseName
  ; Con₁ = ConName ; cgrade = cgradeC pg ; isNewtype = isNewtypeC
  ; Prim = PrimName ; pgrade = λ _ → nom
  ; onBase = onBaseC ; onCon = onConC ; onOther = λ _ → bUnit }

module Types (pg : Role) where
  open Wager.L1.Syntax (toSig (classicSig pg))
  open Wager.L2.Signature (toSig (classicSig pg))

  private
    variable
      Γ : Ctx

  Int Bool' Age : Ty Γ ★
  Int   = base bInt
  Bool' = base bBool
  Age   = capp age Int        -- Int@age

  Proxy : Ty Γ ★ → Ty Γ ★
  Proxy A = capp proxy A

  -- The classic type-level function: it maps the newtype and its
  -- representation to different types (Age ↦ Char, Int ↦ Bool).
  classicF : (g : Role) → Ty [] (★ ⇒[ g ] ★)
  classicF g = lam (papp isAge (var vz))

  -- λa. Proxy a
  proxyF : (g : Role) → Ty [] (★ ⇒[ g ] ★)
  proxyF g = lam (Proxy (var vz))

  -- λa. deep (Proxy a): an inspection below the generative constant.
  deepF : (g : Role) → Ty [] (★ ⇒[ g ] ★)
  deepF g = lam (papp deep (Proxy (var vz)))

  -- λa. isAge Int: the parameter does not occur in the body.
  constF : (g : Role) → Ty [] (★ ⇒[ g ] ★)
  constF g = lam (papp isAge Int)

  -- The newtype `Age` as a two-state trope on Int.
  classicTSig : TSig
  classicTSig = record
    { Lit = ℕ ; litTy = λ _ → bInt
    ; Op = OpName ; carrier = λ _ → base bInt
    ; from = λ { wrapAge → nothing ; unwrapAge → just age }
    ; to   = λ { wrapAge → just age ; unwrapAge → nothing } }

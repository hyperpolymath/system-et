{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The classic unsound program, in the source calculus (definitions only).
--
--   newtype Age = MkAge Int
--   type family F a where { F Int = Bool ; F Age = Char }
--   newtype T a = MkT (F a)
--
-- The parameter of T has the inferred role nominal, because it is the
-- argument of a type-level function. The declared role `d` of the
-- parameter is a parameter of the signature:
--   d = nom   the correct declaration;
--   d = rep   the wrong declaration. With it, `T Age` and `T Int` are
--             representationally equal, and a Char becomes a Bool.
module Wager.FC.Classic where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum.Base using (inl)

open import Wager.Role.Role
open import Wager.Role.Classic using (BaseName; bInt; bBool; bChar; bUnit) public
open import Wager.Erased.Untyped using (ebase)
open import Wager.FC.Signature
import Wager.FC.Types

-- One literal for each base type.
data LitName : Type where
  ℓint ℓbool ℓchar ℓunit : LitName

data Nt₀ : Type where
  ageN : Nt₀

data Nt₁ : Type where
  teeN : Nt₁

data FamName : Type where
  famF : FamName

litTyC : LitName → BaseName
litTyC ℓint  = bInt
litTyC ℓbool = bBool
litTyC ℓchar = bChar
litTyC ℓunit = bUnit

private
  -- F Int = Bool, and Unit on each other base type.
  fBaseC : FamName → BaseName → BaseName
  fBaseC famF bInt = bBool
  fBaseC famF _    = bUnit

-- `d` is the declared role of the parameter of T.
classicS : Role → SSig
classicS d = record
  { Base = BaseName ; Lit = LitName ; litTy = litTyC
  ; N₀ = Nt₀ ; rep₀ = λ _ → ebase bInt
  ; N₁ = Nt₁ ; Fam = FamName
  ; body = λ _ → bfam famF bvar ; role = λ _ → d
  ; fBase = fBaseC
  ; fNt₀ = λ _ _ → bChar                -- F Age = Char
  ; fNt₁ = λ _ _ → inl bUnit ; fOther = λ _ → bUnit }

module STypes (d : Role) where
  open Wager.FC.Types (classicS d)

  sInt sBool sChar sAge : STy
  sInt  = sbase bInt
  sBool = sbase bBool
  sChar = sbase bChar
  sAge  = nt₀ ageN

  sT sF : STy → STy
  sT τ = nt₁ teeN τ
  sF τ = fam famF τ

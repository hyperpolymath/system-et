{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- A source signature with a phantom newtype (definitions only).
-- Stage 3 uses it for examples. Stage 4 uses it for the program that
-- has no translation with two-state tropes.
--
--   newtype Age   = MkAge Int
--   newtype Box a = MkBox (a, Int)      -- inferred role: representational
--   newtype Tag a = MkTag Int           -- inferred role: phantom
--   newtype T a   = MkT (F a)           -- inferred role: nominal
--   type family F a where { F Int = Bool ; F Age = Char ; F (Tag a) = G a }
--   type family G a where { G Int = Bool ; G Bool = Char }
--
-- `taggedS d` is this signature with the declared role d for the
-- parameter of Box. Tag is declared phantom and T is declared nominal.
module Wager.FC.Tagged where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)

open import Wager.Role.Role
open import Wager.FC.Signature
open import Wager.FC.Classic using (BaseName; bInt; bBool; bChar; bUnit; LitName; ℓint; ℓbool; ℓchar; ℓunit; litTyC) public
open import Wager.Erased.Untyped using (ebase)
import Wager.FC.Types

data Nt₀E : Type where
  ageE : Nt₀E

data Nt₁E : Type where
  boxE tagE teeE : Nt₁E

data FamE : Type where
  fE gE : FamE

private
  bodyE : Nt₁E → Body BaseName FamE
  bodyE boxE = bprod bvar (bbase bInt)
  bodyE tagE = bbase bInt
  bodyE teeE = bfam fE bvar

  roleE : Role → Nt₁E → Role
  roleE d boxE = d
  roleE d tagE = ph
  roleE d teeE = nom

  fBaseE : FamE → BaseName → BaseName
  fBaseE fE bInt  = bBool
  fBaseE gE bInt  = bBool
  fBaseE gE bBool = bChar
  fBaseE _  _     = bUnit

  fNt₀E : FamE → Nt₀E → BaseName
  fNt₀E fE ageE = bChar
  fNt₀E gE ageE = bUnit

  -- F (Tag a) = G a: the function F looks at the argument of Tag.
  fNt₁E : FamE → Nt₁E → BaseName ⊎ FamE
  fNt₁E fE tagE = inr gE
  fNt₁E _  _    = inl bUnit

taggedS : Role → SSig
taggedS d = record
  { Base = BaseName ; Lit = LitName ; litTy = litTyC
  ; N₀ = Nt₀E ; rep₀ = λ _ → ebase bInt
  ; N₁ = Nt₁E ; Fam = FamE
  ; body = bodyE ; role = roleE d
  ; fBase = fBaseE ; fNt₀ = fNt₀E ; fNt₁ = fNt₁E ; fOther = λ _ → bUnit }

module TTypes (d : Role) where
  open Wager.FC.Types (taggedS d)

  sInt sBool sChar sAge : STy
  sInt  = sbase bInt
  sBool = sbase bBool
  sChar = sbase bChar
  sAge  = nt₀ ageE

  Box Tag Tee F : STy → STy
  Box = nt₁ boxE
  Tag = nt₁ tagE
  Tee = nt₁ teeE
  F   = fam fE

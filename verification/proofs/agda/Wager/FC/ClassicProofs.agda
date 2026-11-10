{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on typing derivations.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The classic unsound program in the source calculus: proofs (Stage 3).
module Wager.FC.ClassicProofs where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Grade.Finite using (false≢true)
open import Wager.Role.Role
open import Wager.FC.Signature
open import Wager.FC.Classic
open import Wager.Erased.Untyped
import Wager.FC.Types
import Wager.FC.Coercion
import Wager.FC.Term
import Wager.FC.RoleSoundness

private
  IsChar : BaseName → Type
  IsChar bChar = Unit
  IsChar _     = ⊥

  bChar≢bBool : ¬ (bChar ≡ bBool)
  bChar≢bBool p = subst IsChar p tt

  IsEChar : ETy BaseName → Type
  IsEChar (ebase b) = IsChar b
  IsEChar _         = ⊥

  eChar≢eBool : ¬ (ebase bChar ≡ ebase bBool)
  eChar≢eBool p = subst IsEChar p tt

-- The inferred role of the parameter of T is nominal. The check
-- rejects each declared role below nominal.
classic-rejected : (d : Role) → leR d rep ≡ true → ¬ SSig.WellRoled (classicS d)
classic-rejected ph  _ wr = false≢true (wr teeN)
classic-rejected rep _ wr = false≢true (wr teeN)
classic-rejected nom p _  = false≢true p

------------------------------------------------------------------------
-- The wrong declaration: the parameter of T is representational.

module Bad where
  open STypes rep
  open Wager.FC.Types (classicS rep)
  open Wager.FC.Coercion (classicS rep)
  open Wager.FC.Term (classicS rep)
  open Typing litTy

  -- T Age ~R T Int, by congruence at the declared role and Age ~R Int.
  tAge~tInt : Co rep (sT sAge) (sT sInt)
  tAge~tInt = c-nt₁ teeN (c-ax₀ ageN)

  -- Char ~N F Age ~R T Age ~R T Int ~R F Int ~N Bool.
  char~bool : Co rep sChar sBool
  char~bool =
    c-trans (c-sym (c-sub (c-fnt₀ famF ageN)))
   (c-trans (c-sym (c-ax₁ teeN sAge))
   (c-trans tAge~tInt
   (c-trans (c-ax₁ teeN sInt)
            (c-sub (c-fbase famF bInt)))))

  -- A Char literal, cast to the type Bool.
  exploit : STm ∅ˢ sBool
  exploit = cast char~bool (slit ℓchar)

  exploit-erased : eraseTm exploit ≡ ulit ℓchar
  exploit-erased = refl

  exploit-value : ∅ᵉ ⊢ eraseTm exploit ⇓ vlit ℓchar
  exploit-value = ⇓-lit

  exploit-untyped : ¬ (∅ᶜ ⊢ᵉ eraseTm exploit ∶ er sBool)
  exploit-untyped (u-lit ℓ p) = bChar≢bBool p

------------------------------------------------------------------------
-- The correct declaration: the parameter of T is nominal.

module Good where
  open STypes nom
  open Wager.FC.Types (classicS nom)
  open Wager.FC.Coercion (classicS nom)
  open Wager.FC.RoleSoundness (classicS nom)

  accepted : WellRoled
  accepted teeN = refl

  age~int : Co rep sAge sInt
  age~int = c-ax₀ ageN

  -- er (T Age) = Char and er (T Int) = Bool.
  no-coercion : ¬ Co rep (sT sAge) (sT sInt)
  no-coercion γ = eChar≢eBool (rep-sound accepted γ)

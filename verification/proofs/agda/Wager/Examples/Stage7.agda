{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on evaluations and on realisers.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Stage 7 anti-vacuity examples for the univalent cross-check.
--
-- The source signature is `taggedS rep` of Wager.FC.Tagged, with the
-- row scheme and the one-point grade algebra. The model interprets
-- `Int` as the natural numbers, and the literal `ℓint` as the number 7.
module Wager.Examples.Stage7 where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (Bool; true)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd; Σ-syntax)
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Grade.Trivial
open import Wager.Role.Role
open import Wager.FC.Signature
open import Wager.FC.Tagged
open import Wager.Erased.Untyped
import Wager.FC.Types
import Wager.FC.Coercion
import Wager.Trans.Scheme
import Wager.Trans.Target
import Wager.Trans.Coercion
import Wager.Univalent.Model
import Wager.L1.Eval
open import Wager.Examples.Stage3 using (module Role-Check)
open import Wager.Proofs

private
  SS = taggedS rep
  Sc = Wager.Trans.Scheme.rowScheme SS

-- The interpretation of the base constants, and of the 4 literals.
El : BaseName → Type
El bInt  = ℕ
El bBool = Bool
El bChar = Unit
El bUnit = Unit

elLit : (ℓ : LitName) → El (litTyC ℓ)
elLit ℓint  = 7
elLit ℓbool = true
elLit ℓchar = tt
elLit ℓunit = tt

open Wager.FC.Types SS
open Wager.FC.Coercion SS
open TTypes rep renaming (Box to BoxS)
open Role-Check using (wr-rep)
open Wager.Trans.Target SS Sc trivialOps using (T; arr; tSig)
open Wager.L1.Eval tSig using (nf)
open Wager.Trans.Coercion SS Sc trivialOps using (coI; fwd; coerceT; eraseT; lit; Tm)
open Wager.Univalent.Model SS Sc trivial El elLit
open Terms Lit

------------------------------------------------------------------------
-- The model of two types.

-- `Int` is the natural numbers. `Age` is a wrapper of them.
int-is-nat : ⟦ T sInt ⟧ ≡ ℕ
int-is-nat = refl

age-is-box : ⟦ T sAge ⟧ ≡ Box ℕ
age-is-box = refl

------------------------------------------------------------------------
-- ACCEPTED: the newtype axiom `Age ~ Int`.

age-co : Co rep sAge sInt
age-co = c-ax₀ ageE

-- Transport along the path of the axiom takes the wrapper off.
age-transport : transport (pathOf wr-rep age-co) (box 7) ≡ 7
age-transport = refl

-- The literal `ℓint`, as a term of the type `Age`, realises `box 7`.
age-literal : Real (T sAge) ∅ᵉ (ulit ℓint) (box 7)
age-literal = vlit ℓint , ⇓-lit , r-lit ℓint refl

-- The cross-check at this term: the coerced term evaluates to a
-- realiser of the transported element, which is the number 7.
age-coerced :
  Real (T sInt) ∅ᵉ (eraseT (fwd (coI rep age-co) (lit ℓint)))
       (transport (pathOf wr-rep age-co) (box 7))
age-coerced =
  coercion-denotes-transport SS Sc trivial El elLit wr-rep age-co (lit ℓint) (box 7) age-literal

-- The coercion function is a closure that realises transport.
age-function :
  Real (arr tt (T sAge) (T sInt)) ∅ᵉ (eraseT (coerceT age-co))
       (transport (pathOf wr-rep age-co))
age-function =
  coerce-function-is-transport SS Sc trivial El elLit wr-rep age-co

------------------------------------------------------------------------
-- ACCEPTED: congruence below a newtype with a parameter.
-- `BoxS a` is the source newtype `Box a` of the pair `(a, Int)`.

box-co : Co rep (BoxS sAge) (BoxS sInt)
box-co = c-nt₁ boxE age-co

-- Transport along its path changes the first component and keeps the
-- two wrappers of `Box`.
box-transport :
  transport (pathOf wr-rep box-co) (box (box 7 , 3)) ≡ box (7 , 3)
box-transport = refl

------------------------------------------------------------------------
-- REJECTED: a literal does not realise a function.

literal-not-function :
  ∀ {f : ℕ → ℕ} → ¬ 𝓡 (nf (arr tt (T sInt) (T sInt))) (vlit ℓint) f
literal-not-function ()

-- REJECTED: the literal of the type `Bool` does not realise a number.
private
  IsBool : BaseName → Type
  IsBool bBool = Unit
  IsBool _     = ⊥

bool-not-number : ∀ {k : ℕ} → ¬ Real (T sInt) ∅ᵉ (ulit ℓbool) k
bool-not-number (_ , ⇓-lit , r-lit _ p) = subst IsBool p tt

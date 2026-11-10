{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded syntax.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Two-state tropes are not enough (Stage 4).
--
--   1. The translation of Wager.Trans meets the conditions of
--      `Translation`, for each state scheme.
--   2. With the two-state scheme it is also a two-state translation.
--   3. The signature `taggedS rep` has NO two-state translation, into
--      any target signature. The reason: `Tag Int` and `Tag Bool` have
--      one representation, so a two-state translation gives them one
--      target type. The function F tells them apart, so Bool and Char
--      become convertible.
module Wager.Trans.TwoStateProofs where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (_×_; _,_; Σ-syntax)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Role.Role
open import Wager.Grade.Algebra
open import Wager.L1.Signature
open import Wager.FC.Signature
open import Wager.FC.Tagged
import Wager.FC.Types
import Wager.FC.Coercion
import Wager.L1.Conversion
import Wager.L1.Normal
import Wager.L1.Eval
import Wager.L1.Equality
import Wager.Trans.Scheme
import Wager.Trans.Target
import Wager.Trans.Nominal
import Wager.Trans.TwoState

------------------------------------------------------------------------
-- Parts 1 and 2.

module _ (SS : SSig) {R : Type} (ops : GradeOps R) where
  open Wager.FC.Types SS
  open Wager.Trans.Scheme SS
  open Wager.Trans.TwoState SS

  module _ (Sc : StateScheme) where
    open Wager.Trans.Target SS Sc ops
    open Wager.Trans.Nominal SS Sc ops
    open Wager.L1.Conversion tSig
    open Wager.L1.Normal tSig
    open Wager.L1.Equality tSig

    private
      getB : Base → Nf [] ★ → Base
      getB d (nbase b) = b
      getB d _         = d

    scheme-translation : Translation tSig
    scheme-translation = record
      { T      = T
      ; T-nom  = nominal-defeq
      ; FunG   = λ _ → nom
      ; Fun    = λ f → lam (papp f (var vz))
      ; T-fam  = λ f τ → d-sym (d-beta (papp f (var vz)) (T τ))
      ; T-base = λ b b' ne e → ne (cong (getB b) (defEq→nf e)) }

  row-translation : Translation (Wager.Trans.Target.tSig SS rowScheme ops)
  row-translation = scheme-translation rowScheme

  two-state-translation :
    (c : Fam → N₁ → Base) (h : ∀ F N → fNt₁ F N ≡ inl (c F N)) →
    Σ[ t ∈ Translation (Wager.Trans.Target.tSig SS (twoState c h) ops) ]
      TwoState (Wager.Trans.Target.tSig SS (twoState c h) ops) t
  two-state-translation c h =
      scheme-translation Sc
    , record { state = λ N → inr (N , tt)
             ; T-nt  = λ N τ → ≡→DefEq (cong (capp (inr (N , tt))) (sym (T-inst (body N) τ))) }
    where
      Sc = twoState c h
      open Wager.Trans.Target SS Sc ops
      open Wager.Trans.Nominal SS Sc ops
      open Wager.L1.Conversion tSig

------------------------------------------------------------------------
-- Part 3.

private
  SS₀ = taggedS rep

  IsBool : BaseName → Type
  IsBool bBool = Unit
  IsBool _     = ⊥

  bBool≢bChar : ¬ (bBool ≡ bChar)
  bBool≢bChar p = subst IsBool p tt

module _ (S : Sig) where
  open Wager.FC.Types SS₀
  open Wager.FC.Coercion SS₀
  open Wager.Trans.TwoState SS₀
  open Wager.L1.Conversion S
  open TTypes rep

  private
    -- F (Tag Int) ~N Bool and F (Tag Bool) ~N Char.
    f-tag-int : Co nom (F (Tag sInt)) sBool
    f-tag-int = c-trans (c-fnt₁ fE tagE sInt) (c-fbase gE bInt)

    f-tag-bool : Co nom (F (Tag sBool)) sChar
    f-tag-bool = c-trans (c-fnt₁ fE tagE sBool) (c-fbase gE bBool)

  no-two-state : (t : Translation S) → ¬ TwoState S t
  no-two-state t ts =
    T-base bBool bChar bBool≢bChar
      (d-trans (d-sym (T-nom f-tag-int))
      (d-trans (T-fam fE (Tag sInt))
      (d-trans (d-app d-refl tag-eq)
      (d-trans (d-sym (T-fam fE (Tag sBool)))
               (T-nom f-tag-bool)))))
    where
      open Translation t
      open TwoState ts
      -- The two-state form gives `Tag Int` and `Tag Bool` one target type.
      tag-eq : DefEq (T (Tag sInt)) (T (Tag sBool))
      tag-eq = d-trans (T-nt tagE sInt) (d-sym (T-nt tagE sBool))

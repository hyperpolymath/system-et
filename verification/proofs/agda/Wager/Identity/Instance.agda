{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on normal forms.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- A signature that has an identity family (Stage 6, part 2;
-- DESIGN-CHOICES.adoc, DC-6.8). It shows that the record `IdFamily`
-- is not empty.
--
-- The start is a set B₀ of base constants and a set L₀ of literals.
-- The base constants of the signature are the codes:
--
--   cb b        the base constant b of the start
--   cid x y     THE IDENTITY FAMILY, at the codes x and y of two closed
--               normal forms
--   cq, carr, cprod, csum
--               the code of a closed normal form (`enc`)
--
-- `Id A B` is `cid (enc (nf A)) (enc (nf B))`. The function `enc` is
-- injective, and two types are convertible when they have one normal
-- form. So `Id A B` and `Id A' B'` are one constant exactly when A, A'
-- are convertible and B, B' are convertible.
--
-- The literals are the literals of the start and one literal for each
-- code c, of the base type `cid c c`.
--
-- The signature has no generative constant, no primitive and no trope
-- operation. Each code is a base constant, also a code that `enc` does
-- not give.
open import Cubical.Foundations.Prelude
open import Wager.Grade.Algebra
module Wager.Identity.Instance
  (B₀ L₀ : Type) (ty₀ : L₀ → B₀) {R : Type} (ops : GradeOps R) where

open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)
open import Cubical.Data.Maybe.Base using (Maybe; nothing; just)
open import Cubical.Data.Maybe.Properties using (just-inj)

open import Wager.L1.Signature
import Wager.L2.Signature
import Wager.L2.Erasure
import Wager.Identity.Family

data Code : Type where
  cb    : B₀ → Code
  cid   : Code → Code → Code
  cq    : Code → Code
  carr  : R → Code → Code → Code
  cprod : Code → Code → Code
  csum  : Code → Code → Code

sig : Sig
sig = record
  { KG = Unit ; TG = R ; Base = Code
  ; Con₁ = ⊥ ; cgrade = λ ()
  ; Prim = ⊥ ; pgrade = λ () ; onBase = λ () ; onCon = λ () ; onOther = λ () }

-- The base type of a literal.
litTy′ : L₀ ⊎ Code → Code
litTy′ (inl ℓ) = cb (ty₀ ℓ)
litTy′ (inr c) = cid c c

tsig : Wager.L2.Signature.TSig sig
tsig = record
  { Lit = L₀ ⊎ Code ; litTy = litTy′
  ; Op = ⊥ ; carrier = λ () ; from = λ () ; to = λ () }

open import Wager.L1.Syntax sig
open import Wager.L1.Normal sig
open import Wager.L1.Eval sig
open import Wager.L1.Conversion sig
open import Wager.L1.Equality sig
open Wager.L2.Erasure sig tsig ops using (noNe)

------------------------------------------------------------------------
-- The code of a closed normal form, and its inverse.

enc : Nf [] ★ → Code
enc (ne m)       = ⊥.rec (noNe m)
enc (nbase c)    = cq c
enc (narr q a b) = carr q (enc a) (enc b)
enc (a n⊗ b)     = cprod (enc a) (enc b)
enc (a n⊕ b)     = csum (enc a) (enc b)

private
  map₂ : {A B C : Type} → (A → B → C) → Maybe A → Maybe B → Maybe C
  map₂ f (just a) (just b) = just (f a b)
  map₂ f _        _        = nothing

  dec : Code → Maybe (Nf [] ★)
  dec (cb _)       = nothing
  dec (cid _ _)    = nothing
  dec (cq c)       = just (nbase c)
  dec (carr q x y) = map₂ (narr q) (dec x) (dec y)
  dec (cprod x y)  = map₂ _n⊗_ (dec x) (dec y)
  dec (csum x y)   = map₂ _n⊕_ (dec x) (dec y)

  dec-enc : (u : Nf [] ★) → dec (enc u) ≡ just u
  dec-enc (ne m)       = ⊥.rec (noNe m)
  dec-enc (nbase c)    = refl
  dec-enc (narr q a b) = cong₂ (map₂ (narr q)) (dec-enc a) (dec-enc b)
  dec-enc (a n⊗ b)     = cong₂ (map₂ _n⊗_) (dec-enc a) (dec-enc b)
  dec-enc (a n⊕ b)     = cong₂ (map₂ _n⊕_) (dec-enc a) (dec-enc b)

enc-inj : ∀ {u v} → enc u ≡ enc v → u ≡ v
enc-inj {u} {v} p = just-inj u v (sym (dec-enc u) ∙ cong dec p ∙ dec-enc v)

------------------------------------------------------------------------
-- The family.

private
  -- The two indices of a constant of the family.
  cidL cidR : Code → Code
  cidL (cid x y) = x
  cidL c         = c
  cidR (cid x y) = y
  cidR c         = c

  isCid : Code → Type
  isCid (cid _ _) = Unit
  isCid _         = ⊥

  diag : ∀ ℓ {A B : Ty [] ★} →
         litTy′ ℓ ≡ cid (enc (nf A)) (enc (nf B)) → DefEq A B
  -- A literal of the start has a base type of the start.
  diag (inl ℓ) p = ⊥.rec (subst isCid (sym p) tt)
  -- The literal of the code c has the type `cid c c`.
  diag (inr c) p = nf→defEq (enc-inj (sym (cong cidL p) ∙ cong cidR p))

family : Wager.Identity.Family.IdFamily sig tsig
family = record
  { Id       = λ A B → cid (enc (nf A)) (enc (nf B))
  ; Id-conv  = λ d e → cong₂ cid (cong enc (defEq→nf d)) (cong enc (defEq→nf e))
  ; rfl      = λ A → inr (enc (nf A))
  ; rfl-ty   = λ A → refl
  ; diagonal = diag }

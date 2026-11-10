{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The signature of the source calculus (Stage 3).
--
-- The source calculus is a small fragment of System FC with roles,
-- after Breitner, Eisenberg, Peyton Jones and Weirich, "Safe Zero-cost
-- Coercions for Haskell". A signature declares:
--
--   base types and literals;
--   newtypes with no parameter      newtype N   = MkN <erased type>
--   newtypes with one parameter     newtype N a = MkN <body>
--                                   and a declared role for `a`;
--   total closed type-level functions with one argument. A function
--   looks at the head of its argument, as a closed type family does.
--
-- Recursion is kept out by construction: a body cannot mention a
-- declared newtype (DESIGN-CHOICES.adoc, DC-3.2).
module Wager.FC.Signature where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (true)
open import Cubical.Data.Sum.Base using (_⊎_)

open import Wager.Role.Role
open import Wager.Erased.Untyped using (ETy)

-- The body of a newtype declaration with one parameter.
data Body (B F : Type) : Type where
  bvar  : Body B F                          -- the parameter
  bbase : B → Body B F
  barr bprod bsum : Body B F → Body B F → Body B F
  bfam  : F → Body B F → Body B F           -- a type-level function

-- Role inference for the parameter of a body.
--   The parameter itself is used at the role representational.
--   A function, a pair and a sum join the uses of their parts.
--   A type-level function makes each use below it nominal.
--   A body without the parameter gives the role phantom.
roleOf : ∀ {B F} → Body B F → Role
roleOf bvar        = rep
roleOf (bbase _)   = ph
roleOf (barr β γ)  = maxR (roleOf β) (roleOf γ)
roleOf (bprod β γ) = maxR (roleOf β) (roleOf γ)
roleOf (bsum β γ)  = maxR (roleOf β) (roleOf γ)
roleOf (bfam _ β)  = mulZ nom (roleOf β)

record SSig : Type₁ where
  field
    Base   : Type
    Lit    : Type
    litTy  : Lit → Base
    -- Newtypes with no parameter, and the representation of each.
    N₀     : Type
    rep₀   : N₀ → ETy Base
    -- Newtypes with one parameter, type-level functions, the body of
    -- each newtype and the declared role of its parameter.
    N₁     : Type
    Fam    : Type
    body   : N₁ → Body Base Fam
    role   : N₁ → Role
    -- The equations of a type-level function, by the head of the argument:
    fBase  : Fam → Base → Base           -- F b         = b'
    fNt₀   : Fam → N₀ → Base             -- F N         = b'
    fNt₁   : Fam → N₁ → Base ⊎ Fam       -- F (N τ)     = b'   or   = G τ
    fOther : Fam → Base                  -- F (function, pair or sum) = b'

  -- THE SOURCE ROLE CHECK. The declared role of each parameter is not
  -- below the inferred role.
  WellRoled : Type
  WellRoled = (N : N₁) → leR (roleOf (body N)) (role N) ≡ true

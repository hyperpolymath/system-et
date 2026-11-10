{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Source types (Stage 3), and two functions on them:
--
--   ev  the nominal value of a type. Each type-level function is
--       computed. A newtype stays, with the value of its argument.
--   er  the erased type. Each newtype is replaced by its
--       representation.
--
-- The two functions are total and structurally recursive.
open import Wager.FC.Signature

module Wager.FC.Types (SS : SSig) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)

open import Wager.Erased.Untyped using (ETy; ebase; earr; eprod; esum) public
open SSig SS public

infixr 20 _⇒ˢ_
infixr 30 _+ˢ_
infixr 40 _×ˢ_

-- Closed source types.
data STy : Type where
  sbase : Base → STy
  _⇒ˢ_  : STy → STy → STy
  _×ˢ_  : STy → STy → STy
  _+ˢ_  : STy → STy → STy
  nt₀   : N₀ → STy
  nt₁   : N₁ → STy → STy
  fam   : Fam → STy → STy

-- The body of a newtype, with a type for the parameter.
inst : Body Base Fam → STy → STy
inst bvar        τ = τ
inst (bbase b)   τ = sbase b
inst (barr β γ)  τ = inst β τ ⇒ˢ inst γ τ
inst (bprod β γ) τ = inst β τ ×ˢ inst γ τ
inst (bsum β γ)  τ = inst β τ +ˢ inst γ τ
inst (bfam F β)  τ = fam F (inst β τ)

-- An erased type is a source type.
embE : ETy Base → STy
embE (ebase b)   = sbase b
embE (earr a b)  = embE a ⇒ˢ embE b
embE (eprod a b) = embE a ×ˢ embE b
embE (esum a b)  = embE a +ˢ embE b

-- The right side of the equation `F (N τ) = ...`.
resS : Base ⊎ Fam → STy → STy
resS (inl b) τ = sbase b
resS (inr G) τ = fam G τ

------------------------------------------------------------------------
-- Nominal values.

data VTy : Type where
  vbase : Base → VTy
  varr vprod vsum : VTy → VTy → VTy
  vnt₀  : N₀ → VTy
  vnt₁  : N₁ → VTy → VTy

resB : Base ⊎ Fam → (Fam → Base) → Base
resB (inl b) f = b
resB (inr G) f = f G

-- A type-level function on a value. The recursion is on the value.
applyF : Fam → VTy → Base
applyF F (vbase b)   = fBase F b
applyF F (varr _ _)  = fOther F
applyF F (vprod _ _) = fOther F
applyF F (vsum _ _)  = fOther F
applyF F (vnt₀ N)    = fNt₀ F N
applyF F (vnt₁ N v)  = resB (fNt₁ F N) (λ G → applyF G v)

ev : STy → VTy
ev (sbase b)  = vbase b
ev (τ ⇒ˢ σ)   = varr (ev τ) (ev σ)
ev (τ ×ˢ σ)   = vprod (ev τ) (ev σ)
ev (τ +ˢ σ)   = vsum (ev τ) (ev σ)
ev (nt₀ N)    = vnt₀ N
ev (nt₁ N τ)  = vnt₁ N (ev τ)
ev (fam F τ)  = vbase (applyF F (ev τ))

-- The value of a body, from the value of the parameter.
evB : Body Base Fam → VTy → VTy
evB bvar        v = v
evB (bbase b)   v = vbase b
evB (barr β γ)  v = varr (evB β v) (evB γ v)
evB (bprod β γ) v = vprod (evB β v) (evB γ v)
evB (bsum β γ)  v = vsum (evB β v) (evB γ v)
evB (bfam F β)  v = vbase (applyF F (evB β v))

------------------------------------------------------------------------
-- Erased types.

-- The erased type of a body, from the value `v` of the parameter and
-- the erased type `e` of the parameter.
erB : Body Base Fam → VTy → ETy Base → ETy Base
erB bvar        v e = e
erB (bbase b)   v e = ebase b
erB (barr β γ)  v e = earr (erB β v e) (erB γ v e)
erB (bprod β γ) v e = eprod (erB β v e) (erB γ v e)
erB (bsum β γ)  v e = esum (erB β v e) (erB γ v e)
erB (bfam F β)  v e = ebase (applyF F (evB β v))

erV : VTy → ETy Base
erV (vbase b)   = ebase b
erV (varr v w)  = earr (erV v) (erV w)
erV (vprod v w) = eprod (erV v) (erV w)
erV (vsum v w)  = esum (erV v) (erV w)
erV (vnt₀ N)    = rep₀ N
erV (vnt₁ N v)  = erB (body N) v (erV v)

er : STy → ETy Base
er τ = erV (ev τ)

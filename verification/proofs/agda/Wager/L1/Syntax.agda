{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded syntax.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- L1 syntax: the type-level language (docs/theory/00-notation.adoc),
-- after verification/proofs/lean4/Systemet/L1/Syntax.lean.
--
-- Same as the Lean language: simple kinds, de Bruijn variables with
-- intrinsic kinds, base constants, the object arrow, abstraction,
-- application.
-- Added by the task: products and sums at kind ★, a grade on each
-- kind arrow, a grade on the object arrow.
-- Added by DC-1.1: applied generative constants and applied
-- inspection primitives from the signature.
open import Wager.L1.Signature

module Wager.L1.Syntax (S : Sig) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List.Base using (List; []; _∷_) public
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)

open Sig S public

infixr 20 _⇒[_]_
infixr 30 _⊗_
infixr 29 _⊕_

-- Kinds. Each kind arrow has a grade: the grade of the parameter.
data Kind : Type where
  ★      : Kind
  _⇒[_]_ : Kind → KG → Kind → Kind

Ctx : Type
Ctx = List Kind

private
  variable
    Γ Δ Θ : Ctx
    k j   : Kind
    g     : KG

data Var : Ctx → Kind → Type where
  vz : Var (k ∷ Γ) k
  vs : Var Γ k → Var (j ∷ Γ) k

-- Type-level terms with intrinsic kinds.
data Ty (Γ : Ctx) : Kind → Type where
  var  : Var Γ k → Ty Γ k
  base : Base → Ty Γ ★
  capp : Con₁ → Ty Γ ★ → Ty Γ ★
  papp : Prim → Ty Γ ★ → Ty Γ ★
  arr  : TG → Ty Γ ★ → Ty Γ ★ → Ty Γ ★
  _⊗_  : Ty Γ ★ → Ty Γ ★ → Ty Γ ★
  _⊕_  : Ty Γ ★ → Ty Γ ★ → Ty Γ ★
  lam  : Ty (k ∷ Γ) j → Ty Γ (k ⇒[ g ] j)
  app  : Ty Γ (k ⇒[ g ] j) → Ty Γ k → Ty Γ j

-- Renamings. The kind argument is explicit, so that a path between
-- two renamings is a plain `funExt`.
Ren : Ctx → Ctx → Type
Ren Δ Γ = ∀ k → Var Γ k → Var Δ k

idᵣ : Ren Γ Γ
idᵣ k x = x

infixr 9 _∘ᵣ_
_∘ᵣ_ : Ren Θ Δ → Ren Δ Γ → Ren Θ Γ
(r' ∘ᵣ r) k x = r' k (r k x)

wk : Ren (j ∷ Γ) Γ
wk k x = vs x

ext : Ren Δ Γ → Ren (j ∷ Δ) (j ∷ Γ)
ext r k vz     = vz
ext r k (vs x) = vs (r k x)

ren : Ren Δ Γ → Ty Γ k → Ty Δ k
ren r (var x)     = var (r _ x)
ren r (base b)    = base b
ren r (capp c a)  = capp c (ren r a)
ren r (papp p a)  = papp p (ren r a)
ren r (arr q a b) = arr q (ren r a) (ren r b)
ren r (a ⊗ b)     = ren r a ⊗ ren r b
ren r (a ⊕ b)     = ren r a ⊕ ren r b
ren r (lam b)     = lam (ren (ext r) b)
ren r (app f a)   = app (ren r f) (ren r a)

-- Substitutions.
TySub : Ctx → Ctx → Type
TySub Δ Γ = ∀ k → Var Γ k → Ty Δ k

ids : TySub Γ Γ
ids k x = var x

exts : TySub Δ Γ → TySub (j ∷ Δ) (j ∷ Γ)
exts σ k vz     = var vz
exts σ k (vs x) = ren wk (σ k x)

sub : TySub Δ Γ → Ty Γ k → Ty Δ k
sub σ (var x)     = σ _ x
sub σ (base b)    = base b
sub σ (capp c a)  = capp c (sub σ a)
sub σ (papp p a)  = papp p (sub σ a)
sub σ (arr q a b) = arr q (sub σ a) (sub σ b)
sub σ (a ⊗ b)     = sub σ a ⊗ sub σ b
sub σ (a ⊕ b)     = sub σ a ⊕ sub σ b
sub σ (lam b)     = lam (sub (exts σ) b)
sub σ (app f a)   = app (sub σ f) (sub σ a)

infixr 8 _∷ₛ_
_∷ₛ_ : Ty Δ j → TySub Δ Γ → TySub Δ (j ∷ Γ)
(u ∷ₛ σ) k vz     = u
(u ∷ₛ σ) k (vs x) = σ k x

-- β-substitution of the top variable: `b [ u ]`.
infix 25 _[_]
_[_] : Ty (j ∷ Γ) k → Ty Γ j → Ty Γ k
b [ u ] = sub (u ∷ₛ ids) b

-- The result of a primitive on `capp c A`, as a type.
resTy : Base ⊎ Prim → Ty Γ ★ → Ty Γ ★
resTy (inl b) A = base b
resTy (inr q) A = papp q A

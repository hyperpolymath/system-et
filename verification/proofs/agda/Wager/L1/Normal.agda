{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded syntax.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- L1 β-normal forms, after
-- verification/proofs/lean4/Systemet/L1/Normal.lean.
--
-- `Nf` are normal forms and `Ne` are neutral terms (a variable applied
-- to normal arguments, or a primitive that waits for a neutral
-- argument). There is no η: a neutral term is normal at each kind.
open import Wager.L1.Signature

module Wager.L1.Normal (S : Sig) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum.Base as Sum using (_⊎_; inl; inr)

open import Wager.L1.Syntax S
open import Wager.L1.SyntaxLemmas S

private
  variable
    Γ Δ Θ : Ctx
    k j   : Kind
    g     : KG

infixr 30 _n⊗_
infixr 29 _n⊕_

data Ne (Γ : Ctx) : Kind → Type
data Nf (Γ : Ctx) : Kind → Type

data Ne Γ where
  nvar   : Var Γ k → Ne Γ k
  napp   : Ne Γ (k ⇒[ g ] j) → Nf Γ k → Ne Γ j
  nstuck : Prim → Ne Γ ★ → Ne Γ ★

data Nf Γ where
  ne    : Ne Γ k → Nf Γ k
  nlam  : Nf (k ∷ Γ) j → Nf Γ (k ⇒[ g ] j)
  nbase : Base → Nf Γ ★
  ncapp : Con₁ → Nf Γ ★ → Nf Γ ★
  narr  : TG → Nf Γ ★ → Nf Γ ★ → Nf Γ ★
  _n⊗_  : Nf Γ ★ → Nf Γ ★ → Nf Γ ★
  _n⊕_  : Nf Γ ★ → Nf Γ ★ → Nf Γ ★

------------------------------------------------------------------------
-- Renaming.

renNe : Ren Δ Γ → Ne Γ k → Ne Δ k
renNf : Ren Δ Γ → Nf Γ k → Nf Δ k

renNe r (nvar x)     = nvar (r _ x)
renNe r (napp n v)   = napp (renNe r n) (renNf r v)
renNe r (nstuck p n) = nstuck p (renNe r n)

renNf r (ne n)       = ne (renNe r n)
renNf r (nlam b)     = nlam (renNf (ext r) b)
renNf r (nbase b)    = nbase b
renNf r (ncapp c v)  = ncapp c (renNf r v)
renNf r (narr q a b) = narr q (renNf r a) (renNf r b)
renNf r (a n⊗ b)     = renNf r a n⊗ renNf r b
renNf r (a n⊕ b)     = renNf r a n⊕ renNf r b

renNe-id : (n : Ne Γ k) → renNe idᵣ n ≡ n
renNf-id : (v : Nf Γ k) → renNf idᵣ v ≡ v

renNe-id (nvar x)     = refl
renNe-id (napp n v)   = cong₂ napp (renNe-id n) (renNf-id v)
renNe-id (nstuck p n) = cong (nstuck p) (renNe-id n)

renNf-id (ne n)       = cong ne (renNe-id n)
renNf-id (nlam b)     = cong nlam (cong (λ r → renNf r b) (renExt ext-id) ∙ renNf-id b)
renNf-id (nbase b)    = refl
renNf-id (ncapp c v)  = cong (ncapp c) (renNf-id v)
renNf-id (narr q a b) = cong₂ (narr q) (renNf-id a) (renNf-id b)
renNf-id (a n⊗ b)     = cong₂ _n⊗_ (renNf-id a) (renNf-id b)
renNf-id (a n⊕ b)     = cong₂ _n⊕_ (renNf-id a) (renNf-id b)

renNe-comp : (r' : Ren Θ Δ) (r : Ren Δ Γ) (n : Ne Γ k) →
             renNe r' (renNe r n) ≡ renNe (r' ∘ᵣ r) n
renNf-comp : (r' : Ren Θ Δ) (r : Ren Δ Γ) (v : Nf Γ k) →
             renNf r' (renNf r v) ≡ renNf (r' ∘ᵣ r) v

renNe-comp r' r (nvar x)     = refl
renNe-comp r' r (napp n v)   = cong₂ napp (renNe-comp r' r n) (renNf-comp r' r v)
renNe-comp r' r (nstuck p n) = cong (nstuck p) (renNe-comp r' r n)

renNf-comp r' r (ne n)       = cong ne (renNe-comp r' r n)
renNf-comp r' r (nlam b)     =
  cong nlam (renNf-comp (ext r') (ext r) b
             ∙ cong (λ s → renNf s b) (renExt (ext-comp r' r)))
renNf-comp r' r (nbase b)    = refl
renNf-comp r' r (ncapp c v)  = cong (ncapp c) (renNf-comp r' r v)
renNf-comp r' r (narr q a b) = cong₂ (narr q) (renNf-comp r' r a) (renNf-comp r' r b)
renNf-comp r' r (a n⊗ b)     = cong₂ _n⊗_ (renNf-comp r' r a) (renNf-comp r' r b)
renNf-comp r' r (a n⊕ b)     = cong₂ _n⊕_ (renNf-comp r' r a) (renNf-comp r' r b)

------------------------------------------------------------------------
-- Embedding of normal forms into terms.

embNe : Ne Γ k → Ty Γ k
embNf : Nf Γ k → Ty Γ k

embNe (nvar x)     = var x
embNe (napp n v)   = app (embNe n) (embNf v)
embNe (nstuck p n) = papp p (embNe n)

embNf (ne n)       = embNe n
embNf (nlam b)     = lam (embNf b)
embNf (nbase b)    = base b
embNf (ncapp c v)  = capp c (embNf v)
embNf (narr q a b) = arr q (embNf a) (embNf b)
embNf (a n⊗ b)     = embNf a ⊗ embNf b
embNf (a n⊕ b)     = embNf a ⊕ embNf b

embNe-ren : (r : Ren Δ Γ) (n : Ne Γ k) → embNe (renNe r n) ≡ ren r (embNe n)
embNf-ren : (r : Ren Δ Γ) (v : Nf Γ k) → embNf (renNf r v) ≡ ren r (embNf v)

embNe-ren r (nvar x)     = refl
embNe-ren r (napp n v)   = cong₂ app (embNe-ren r n) (embNf-ren r v)
embNe-ren r (nstuck p n) = cong (papp p) (embNe-ren r n)

embNf-ren r (ne n)       = embNe-ren r n
embNf-ren r (nlam b)     = cong lam (embNf-ren (ext r) b)
embNf-ren r (nbase b)    = refl
embNf-ren r (ncapp c v)  = cong (capp c) (embNf-ren r v)
embNf-ren r (narr q a b) = cong₂ (arr q) (embNf-ren r a) (embNf-ren r b)
embNf-ren r (a n⊗ b)     = cong₂ _⊗_ (embNf-ren r a) (embNf-ren r b)
embNf-ren r (a n⊕ b)     = cong₂ _⊕_ (embNf-ren r a) (embNf-ren r b)

------------------------------------------------------------------------
-- The action of an inspection primitive on a normal form of kind ★.
-- It is total: the recursion is on the normal form.

resNf : Base ⊎ Prim → (Prim → Nf Γ ★) → Nf Γ ★
resNf (inl b) f = nbase b
resNf (inr q) f = f q

inspect : Prim → Nf Γ ★ → Nf Γ ★
inspect p (ne n)       = ne (nstuck p n)
inspect p (nbase b)    = nbase (onBase p b)
inspect p (ncapp c v)  = resNf (onCon p c) (λ q → inspect q v)
inspect p (narr q a b) = nbase (onOther p)
inspect p (a n⊗ b)     = nbase (onOther p)
inspect p (a n⊕ b)     = nbase (onOther p)

private
  resNf-ren : (r : Ren Δ Γ) (x : Base ⊎ Prim) {f : Prim → Nf Γ ★} {f' : Prim → Nf Δ ★} →
              (∀ q → renNf r (f q) ≡ f' q) → renNf r (resNf x f) ≡ resNf x f'
  resNf-ren r (inl b) h = refl
  resNf-ren r (inr q) h = h q

-- `inspect` commutes with renaming.
inspect-ren : (r : Ren Δ Γ) (p : Prim) (v : Nf Γ ★) →
              renNf r (inspect p v) ≡ inspect p (renNf r v)
inspect-ren r p (ne n)       = refl
inspect-ren r p (nbase b)    = refl
inspect-ren r p (ncapp c v)  = resNf-ren r (onCon p c) (λ q → inspect-ren r q v)
inspect-ren r p (narr q a b) = refl
inspect-ren r p (a n⊗ b)     = refl
inspect-ren r p (a n⊕ b)     = refl

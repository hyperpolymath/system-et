{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Stage 8. The identity family and open types: proofs.
--
-- An open type E with one type variable is convertible to the
-- embedding of its normal form v. The proof looks at v. In the
-- signature of `Wager.Identity.Instance`, v is the variable, a base
-- constant, an arrow, a product or a sum. No case has the evidence
-- type `Id α B` at each instance α:
--   the variable     its instance at the type `I₀ ⊗ I₀` is a product;
--   a base constant  its instances at `I₀` and at `I₀ ⊗ I₀` are one
--                    constant, and the two evidence types are two
--                    constants;
--   the other cases  the instance is not a base constant.
open import Cubical.Foundations.Prelude
open import Wager.Grade.Algebra

module Wager.Poly.IdentityRigid
  (B₀ L₀ : Type) (ty₀ : L₀ → B₀) {R : Type} (ops : GradeOps R) (b₀ : B₀) where

open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (_,_)

open import Wager.Identity.Instance B₀ L₀ ty₀ ops
open import Wager.L1.Syntax sig
open import Wager.L1.Normal sig
open import Wager.L1.Eval sig
open import Wager.L1.Conversion sig
open import Wager.L1.Soundness sig using (soundness)
open import Wager.L1.Equality sig using (defEq→nf)
open import Wager.Poly.Proofs sig tsig ops using (t8-conv)
open import Wager.Poly.IdentityStatements B₀ L₀ ty₀ ops b₀

private
  O : Ctx
  O = ★ ∷ []

  -- The normal form of the instance of a normal form.
  at : Nf O ★ → Ty [] ★ → Nf [] ★
  at v α = nf (embNf v [ α ])

  -- If each instance of E is convertible to X α, then each instance of
  -- the normal form of E has the normal form of X α.
  to-nf : (E : Ty O ★) (X : Ty [] ★ → Ty [] ★) →
          (∀ α → DefEq (E [ α ]) (X α)) → ∀ α → at (nf E) α ≡ nf (X α)
  to-nf E X h α =
    sym (defEq→nf (t8-conv (α ∷ₛ ids) (soundness E))) ∙ defEq→nf (h α)

  -- The context O has no variable of an arrow kind, so it has no
  -- neutral term of an arrow kind.
  noNeArr : ∀ {k g j} → Ne O (k ⇒[ g ] j) → ⊥
  noNeArr (nvar (vs ()))
  noNeArr (napp n v) = noNeArr n

  -- The shape of a closed normal form.
  isBase isArr isProd isSum : Nf [] ★ → Type
  isBase (nbase _) = Unit
  isBase _         = ⊥
  isArr (narr _ _ _) = Unit
  isArr _            = ⊥
  isProd (_ n⊗ _) = Unit
  isProd _        = ⊥
  isSum (_ n⊕ _) = Unit
  isSum _        = ⊥

  -- A base constant of the family whose first index is the code of a
  -- base constant.
  isIdAtBase : Nf [] ★ → Type
  isIdAtBase (nbase (cid (cq _) _)) = Unit
  isIdAtBase _                      = ⊥

  left⊕ left⊗ : Nf [] ★ → Nf [] ★
  left⊕ (a n⊕ b) = a
  left⊕ v        = v
  left⊗ (a n⊗ b) = a
  left⊗ v        = v

  I₀⊗I₀ : Ty [] ★
  I₀⊗I₀ = I₀ ⊗ I₀

  -- The evidence type at α, as a normal form.
  evN : Ty [] ★ → Ty [] ★ → Nf [] ★
  evN α B = nbase (cid (enc (nf α)) (enc (nf B)))

  -- No normal form has the evidence type at each instance.
  no-evidence : (B : Ty [] ★) (v : Nf O ★) → (∀ α → at v α ≡ evN α B) → ⊥
  no-evidence B (ne (nvar vz))       h = subst isProd (h I₀⊗I₀) tt
  no-evidence B (ne (nvar (vs ())))  h
  no-evidence B (ne (napp n _))      h = noNeArr n
  no-evidence B (ne (nstuck () _))   h
  no-evidence B (nbase c)            h = subst isIdAtBase (sym (h I₀) ∙ h I₀⊗I₀) tt
  no-evidence B (ncapp () _)         h
  no-evidence B (narr q a b)         h = subst isArr (h I₀) tt
  no-evidence B (a n⊗ b)             h = subst isProd (h I₀) tt
  no-evidence B (a n⊕ b)             h = subst isSum (h I₀) tt

  -- One summand of the data type: the evidence and the payload.
  no-summand : (B : Ty [] ★) (v : Nf O ★) → (∀ α → at v α ≡ (evN α B n⊗ nf α)) → ⊥
  no-summand B (ne (nvar vz))       h = subst isBase (h I₀) tt
  no-summand B (ne (nvar (vs ())))  h
  no-summand B (ne (napp n _))      h = noNeArr n
  no-summand B (ne (nstuck () _))   h
  no-summand B (nbase c)            h = subst isBase (h I₀) tt
  no-summand B (ncapp () _)         h
  no-summand B (narr q a b)         h = subst isArr (h I₀) tt
  no-summand B (a n⊗ b)             h = no-evidence B a (λ α → cong left⊗ (h α))
  no-summand B (a n⊕ b)             h = subst isSum (h I₀) tt

  no-data : (v : Nf O ★) → (∀ α → at v α ≡ nf (Gᵍ α)) → ⊥
  no-data (ne (nvar vz))       h = subst isBase (h I₀) tt
  no-data (ne (nvar (vs ())))  h
  no-data (ne (napp n _))      h = noNeArr n
  no-data (ne (nstuck () _))   h
  no-data (nbase c)            h = subst isBase (h I₀) tt
  no-data (ncapp () _)         h
  no-data (narr q a b)         h = subst isArr (h I₀) tt
  no-data (a n⊗ b)             h = subst isProd (h I₀) tt
  no-data (a n⊕ b)             h = no-summand I₀ a (λ α → cong left⊕ (h α))

t8-evidence-rigid : T8-Evidence-Rigid
t8-evidence-rigid B (E , h) =
  no-evidence B (nf E) (to-nf E (λ α → base (Id α B)) h)
  where open import Wager.Identity.Family sig tsig using (module IdFamily)
        open IdFamily family using (Id)

t8-gadt-not-open : T8-Gadt-Not-Open
t8-gadt-not-open (G , h) = no-data (nf G) (to-nf G Gᵍ h)

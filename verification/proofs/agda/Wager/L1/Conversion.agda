{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded syntax.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- L1 conversion: the one primitive relation of systemet
-- (docs/theory/02-l1-equality.adoc), after
-- verification/proofs/lean4/Systemet/L1/Conversion.lean.
--
-- `DefEq` is the least congruent equivalence that contains β and the
-- δ-rules of the signature primitives. There is no η, as in the
-- mechanized Lean fragment.
open import Wager.L1.Signature

module Wager.L1.Conversion (S : Sig) where

open import Cubical.Foundations.Prelude

open import Wager.L1.Syntax S
open import Wager.L1.SyntaxLemmas S

private
  variable
    Γ Δ : Ctx
    k j : Kind
    g   : KG

data DefEq {Γ : Ctx} : {k : Kind} → Ty Γ k → Ty Γ k → Type where
  -- equivalence
  d-refl  : {t : Ty Γ k} → DefEq t t
  d-sym   : {t u : Ty Γ k} → DefEq t u → DefEq u t
  d-trans : {t u v : Ty Γ k} → DefEq t u → DefEq u v → DefEq t v
  -- β
  d-beta  : (b : Ty (k ∷ Γ) j) (u : Ty Γ k) →
            DefEq (app {g = g} (lam b) u) (b [ u ])
  -- congruence
  d-capp  : ∀ {c} {a a' : Ty Γ ★} → DefEq a a' → DefEq (capp c a) (capp c a')
  d-papp  : ∀ {p} {a a' : Ty Γ ★} → DefEq a a' → DefEq (papp p a) (papp p a')
  d-arr   : ∀ {q} {a a' b b' : Ty Γ ★} →
            DefEq a a' → DefEq b b' → DefEq (arr q a b) (arr q a' b')
  d-prod  : {a a' b b' : Ty Γ ★} → DefEq a a' → DefEq b b' → DefEq (a ⊗ b) (a' ⊗ b')
  d-sum   : {a a' b b' : Ty Γ ★} → DefEq a a' → DefEq b b' → DefEq (a ⊕ b) (a' ⊕ b')
  d-lam   : {b b' : Ty (k ∷ Γ) j} → DefEq b b' → DefEq (lam {g = g} b) (lam b')
  d-app   : {f f' : Ty Γ (k ⇒[ g ] j)} {a a' : Ty Γ k} →
            DefEq f f' → DefEq a a' → DefEq (app f a) (app f' a')
  -- δ: a primitive computes on the head of its argument
  δ-base  : ∀ p b → DefEq (papp p (base b)) (base (onBase p b))
  δ-capp  : ∀ p c (A : Ty Γ ★) → DefEq (papp p (capp c A)) (resTy (onCon p c) A)
  δ-arr   : ∀ p q (A B : Ty Γ ★) → DefEq (papp p (arr q A B)) (base (onOther p))
  δ-prod  : ∀ p (A B : Ty Γ ★) → DefEq (papp p (A ⊗ B)) (base (onOther p))
  δ-sum   : ∀ p (A B : Ty Γ ★) → DefEq (papp p (A ⊕ B)) (base (onOther p))

-- A path is a conversion.
≡→DefEq : {t u : Ty Γ k} → t ≡ u → DefEq t u
≡→DefEq {t = t} p = subst (DefEq t) p d-refl

-- Conversion is stable under renaming.
DefEq-ren : (r : Ren Δ Γ) {t u : Ty Γ k} → DefEq t u → DefEq (ren r t) (ren r u)
DefEq-ren r d-refl          = d-refl
DefEq-ren r (d-sym d)       = d-sym (DefEq-ren r d)
DefEq-ren r (d-trans d e)   = d-trans (DefEq-ren r d) (DefEq-ren r e)
DefEq-ren r (d-beta b u)    =
  d-trans (d-beta (ren (ext r) b) (ren r u)) (≡→DefEq (sym (ren-β r b u)))
DefEq-ren r (d-capp d)      = d-capp (DefEq-ren r d)
DefEq-ren r (d-papp d)      = d-papp (DefEq-ren r d)
DefEq-ren r (d-arr d e)     = d-arr (DefEq-ren r d) (DefEq-ren r e)
DefEq-ren r (d-prod d e)    = d-prod (DefEq-ren r d) (DefEq-ren r e)
DefEq-ren r (d-sum d e)     = d-sum (DefEq-ren r d) (DefEq-ren r e)
DefEq-ren r (d-lam d)       = d-lam (DefEq-ren (ext r) d)
DefEq-ren r (d-app d e)     = d-app (DefEq-ren r d) (DefEq-ren r e)
DefEq-ren r (δ-base p b)    = δ-base p b
DefEq-ren r (δ-capp p c A)  =
  d-trans (δ-capp p c (ren r A)) (≡→DefEq (sym (ren-resTy r (onCon p c) A)))
DefEq-ren r (δ-arr p q A B) = δ-arr p q (ren r A) (ren r B)
DefEq-ren r (δ-prod p A B)  = δ-prod p (ren r A) (ren r B)
DefEq-ren r (δ-sum p A B)   = δ-sum p (ren r A) (ren r B)

{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded syntax.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Representational equivalence `≈` on closed normal types of kind ★:
-- the least congruence that contains newtype unfolding.
--
-- SPECIFICATION ONLY. Theorem statements use `≈`. No typing rule and no
-- kinding rule uses it (RELATION-LEDGER.adoc).
open import Wager.Role.Signature

module Wager.Role.RepEq (RS : RoleSig) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (Bool; true; false; if_then_else_)

open RoleSig RS using (isNewtype)
open import Wager.L1.Syntax (toSig RS)
open import Wager.L1.Normal (toSig RS)

private
  variable
    Γ : Ctx

-- Closed normal types of kind ★.
CNf : Type
CNf = Nf [] ★

infix 4 _≈_
data _≈_ : CNf → CNf → Type where
  ≈-refl   : ∀ {v} → v ≈ v
  ≈-sym    : ∀ {v w} → v ≈ w → w ≈ v
  ≈-trans  : ∀ {u v w} → u ≈ v → v ≈ w → u ≈ w
  -- Newtype unfolding: the newtype `A@s` and its representation A.
  ≈-unfold : ∀ s {v} → isNewtype s ≡ true → ncapp s v ≈ v
  -- Congruence for each type former of kind ★.
  ≈-capp   : ∀ c {v w} → v ≈ w → ncapp c v ≈ ncapp c w
  ≈-arr    : ∀ q {a a' b b'} → a ≈ a' → b ≈ b' → narr q a b ≈ narr q a' b'
  ≈-prod   : ∀ {a a' b b'} → a ≈ a' → b ≈ b' → (a n⊗ b) ≈ (a' n⊗ b')
  ≈-sum    : ∀ {a a' b b'} → a ≈ a' → b ≈ b' → (a n⊕ b) ≈ (a' n⊕ b')

≡→≈ : ∀ {v w} → v ≡ w → v ≈ w
≡→≈ {v} p = subst (v ≈_) p ≈-refl

-- The representation of a type: each newtype wrapper is removed.
strip : Nf Γ ★ → Nf Γ ★
strip (ne n)       = ne n
strip (nbase b)    = nbase b
strip (ncapp c v)  = if isNewtype c then strip v else ncapp c (strip v)
strip (narr q a b) = narr q (strip a) (strip b)
strip (a n⊗ b)     = strip a n⊗ strip b
strip (a n⊕ b)     = strip a n⊕ strip b

-- Equivalent types have the same representation. A proof that two
-- types are NOT equivalent uses this lemma.
≈→strip : ∀ {v w} → v ≈ w → strip v ≡ strip w
≈→strip ≈-refl          = refl
≈→strip (≈-sym e)       = sym (≈→strip e)
≈→strip (≈-trans e e')  = ≈→strip e ∙ ≈→strip e'
≈→strip (≈-unfold s {v} p) =
  cong (λ b → if b then strip v else ncapp s (strip v)) p
≈→strip (≈-capp c e)    = cong (λ z → if isNewtype c then z else ncapp c z) (≈→strip e)
≈→strip (≈-arr q e e')  = cong₂ (narr q) (≈→strip e) (≈→strip e')
≈→strip (≈-prod e e')   = cong₂ _n⊗_ (≈→strip e) (≈→strip e')
≈→strip (≈-sum e e')    = cong₂ _n⊕_ (≈→strip e) (≈→strip e')

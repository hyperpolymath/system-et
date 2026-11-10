{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded normal forms and on
-- typing derivations.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Type erasure of the target calculus (Stage 6, a lemma).
--
-- A typed target term erases to a term of the untyped calculus, and
-- that term has a simple type: the erased type of the target type.
-- The lemma holds for each signature and each set of grade operations.
--
--   erT    the erased type of a closed target type. It is read from the
--          normal form. A trope state vanishes, and a grade vanishes.
--   eraseᵗ the erasure of a target term. A type, a grade and a trope
--          transition vanish.
--
-- The target calculus has conversion only (`t-conv`). Two convertible
-- types have one normal form, so they have one erased type. This is the
-- reason why a target term cannot use a value at two erased types.
open import Wager.L1.Signature
open import Wager.Grade.Algebra
import Wager.L2.Signature

module Wager.L2.Erasure
  (S : Sig) (TS : Wager.L2.Signature.TSig S) (ops : GradeOps (Sig.TG S)) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)

open import Wager.L1.Syntax S
open import Wager.L1.Normal S
open import Wager.L1.Eval S
open import Wager.L1.Conversion S
open import Wager.L1.Equality S
open import Wager.L2.Typing S TS ops
open import Wager.Erased.Untyped
open Terms Lit
open Typing litTy

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Erased types.

-- The empty context has no neutral type.
noNe : ∀ {k} → Ne [] k → ⊥
noNe (napp m v)   = noNe m
noNe (nstuck p m) = noNe m

erN : Nf [] ★ → ETy Base
erN (ne m)       = ⊥.rec (noNe m)
erN (nbase b)    = ebase b
erN (ncapp c v)  = erN v
erN (narr q a b) = earr (erN a) (erN b)
erN (a n⊗ b)     = eprod (erN a) (erN b)
erN (a n⊕ b)     = esum (erN a) (erN b)

erT : Ty [] ★ → ETy Base
erT A = erN (nf A)

-- The state of a trope does not change the erased type.
er-at : ∀ A m → erT (A at m) ≡ erT A
er-at A nothing  = refl
er-at A (just s) = refl

------------------------------------------------------------------------
-- Erased terms.

eraseᵗ : Tm n → UTm n
eraseᵗ (tvar i)     = uvar i
eraseᵗ (tlam q A b) = ulam (eraseᵗ b)
eraseᵗ (tapp f a)   = uapp (eraseᵗ f) (eraseᵗ a)
eraseᵗ (pair s t)   = upair (eraseᵗ s) (eraseᵗ t)
eraseᵗ (letp s b)   = uletp (eraseᵗ s) (eraseᵗ b)
eraseᵗ (inj₁ t)     = uinl (eraseᵗ t)
eraseᵗ (inj₂ t)     = uinr (eraseᵗ t)
eraseᵗ (case s l r) = ucase (eraseᵗ s) (eraseᵗ l) (eraseᵗ r)
eraseᵗ (lit ℓ)      = ulit ℓ
eraseᵗ (step o t)   = eraseᵗ t

------------------------------------------------------------------------
-- Erasure preserves typing.

-- The erased context agrees with the target context.
Agree : ECx n → Cx n → Type
Agree Δ Γ = ∀ i → Δ i ≡ erT (Γ i)

agree-ext : ∀ {Δ : ECx n} {Γ : Cx n} A → Agree Δ Γ → Agree (Δ ▹ᵉ erT A) (Γ ▹ᶜ A)
agree-ext A h zero    = refl
agree-ext A h (suc i) = h i

erase-typed′ : ∀ {γ} {Γ : Cx n} {t A} → γ ▸ Γ ⊢ t ∶ A →
               (Δ : ECx n) → Agree Δ Γ → Δ ⊢ᵉ eraseᵗ t ∶ erT A
erase-typed′ (t-var i) Δ h = u-var i (h i)
erase-typed′ (t-lam {A = A} d) Δ h =
  u-lam (erase-typed′ d (Δ ▹ᵉ erT A) (agree-ext A h))
erase-typed′ (t-app d e) Δ h = u-app (erase-typed′ d Δ h) (erase-typed′ e Δ h)
erase-typed′ (t-pair d e) Δ h = u-pair (erase-typed′ d Δ h) (erase-typed′ e Δ h)
erase-typed′ (t-letp {A = A} {B = B} d e) Δ h =
  u-letp (erase-typed′ d Δ h)
         (erase-typed′ e (Δ ▹ᵉ erT A ▹ᵉ erT B) (agree-ext B (agree-ext A h)))
erase-typed′ (t-inj₁ d) Δ h = u-inl (erase-typed′ d Δ h)
erase-typed′ (t-inj₂ d) Δ h = u-inr (erase-typed′ d Δ h)
erase-typed′ (t-case {A = A} {B = B} d l r) Δ h =
  u-case (erase-typed′ d Δ h)
         (erase-typed′ l (Δ ▹ᵉ erT A) (agree-ext A h))
         (erase-typed′ r (Δ ▹ᵉ erT B) (agree-ext B h))
erase-typed′ (t-lit ℓ) Δ h = u-lit ℓ refl
-- A trope transition: the two states have one erased type.
erase-typed′ (t-step {t = t} o d) Δ h =
  subst (λ a → Δ ⊢ᵉ eraseᵗ t ∶ a)
        (er-at (carrier o) (from o) ∙ sym (er-at (carrier o) (to o)))
        (erase-typed′ d Δ h)
-- Conversion: the two types have one normal form.
erase-typed′ (t-conv {t = t} d e) Δ h =
  subst (λ a → Δ ⊢ᵉ eraseᵗ t ∶ a) (cong erN (defEq→nf e)) (erase-typed′ d Δ h)
erase-typed′ (t-sub d _) Δ h = erase-typed′ d Δ h

-- THE LEMMA.
erase-typed : ∀ {γ} {Γ : Cx n} {t A} → γ ▸ Γ ⊢ t ∶ A →
              (λ i → erT (Γ i)) ⊢ᵉ eraseᵗ t ∶ erT A
erase-typed d = erase-typed′ d _ (λ i → refl)

------------------------------------------------------------------------
-- A corollary: the target has no hypothetical equality.
--
-- A typed target term that erases to the identity function has an arrow
-- type, and the two sides of the arrow have one erased type.
identity-one-type : ∀ {γ} {Γ : Cx n} {t q A B} → γ ▸ Γ ⊢ t ∶ arr q A B →
                    eraseᵗ t ≡ ulam (uvar zero) → erT A ≡ erT B
identity-one-type {A = A} {B = B} d p =
  inv (subst (λ u → _ ⊢ᵉ u ∶ earr (erT A) (erT B)) p (erase-typed d))
  where
  inv : ∀ {Δ : ECx n} {a b} → Δ ⊢ᵉ ulam (uvar zero) ∶ earr a b → a ≡ b
  inv (u-lam (u-var zero e)) = e

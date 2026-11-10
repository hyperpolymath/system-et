{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on scoped terms.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The untyped calculus that a program erases to (Stage 3).
--
--   ETy    erased types: a base type, a function, a pair or a sum.
--          An erased type has no newtype and no type-level function.
--   UTm    untyped terms (de Bruijn). There is no coercion, no cast and
--          no trope transition in this syntax.
--   _⊢_⇓_  big-step evaluation, call by value, with closures.
--   _⊢ᵉ_∶_ typing of an untyped term with erased types.
--
-- The module does not depend on the source calculus or on the target
-- calculus. Each of the two erases into it.
module Wager.Erased.Untyped where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)

data ETy (B : Type) : Type where
  ebase : B → ETy B
  earr eprod esum : ETy B → ETy B → ETy B

------------------------------------------------------------------------
-- Terms, values and evaluation.

module Terms (Lit : Type) where

  private
    variable
      n m : ℕ

  data UTm : ℕ → Type where
    uvar  : Fin n → UTm n
    ulam  : UTm (suc n) → UTm n
    uapp  : UTm n → UTm n → UTm n
    upair : UTm n → UTm n → UTm n
    -- The body sees the first component at index 1 and the second at index 0.
    uletp : UTm n → UTm (suc (suc n)) → UTm n
    uinl  : UTm n → UTm n
    uinr  : UTm n → UTm n
    ucase : UTm n → UTm (suc n) → UTm (suc n) → UTm n
    ulit  : Lit → UTm n

  -- A value. A function value is a closure: an environment and a body.
  data UVal : Type where
    vclo  : (Fin n → UVal) → UTm (suc n) → UVal
    vpair : UVal → UVal → UVal
    vinl  : UVal → UVal
    vinr  : UVal → UVal
    vlit  : Lit → UVal

  UEnv : ℕ → Type
  UEnv n = Fin n → UVal

  infixr 5 _∷ᵉ_
  _∷ᵉ_ : UVal → UEnv n → UEnv (suc n)
  (v ∷ᵉ ρ) zero    = v
  (v ∷ᵉ ρ) (suc i) = ρ i

  -- The empty environment.
  ∅ᵉ : UEnv 0
  ∅ᵉ ()

  infix 3 _⊢_⇓_
  data _⊢_⇓_ : UEnv n → UTm n → UVal → Type where
    ⇓-var   : ∀ {ρ : UEnv n} i → ρ ⊢ uvar i ⇓ ρ i
    ⇓-lam   : ∀ {ρ : UEnv n} {b} → ρ ⊢ ulam b ⇓ vclo ρ b
    ⇓-app   : ∀ {ρ : UEnv n} {ρ' : UEnv m} {f a b w v} →
              ρ ⊢ f ⇓ vclo ρ' b → ρ ⊢ a ⇓ w → (w ∷ᵉ ρ') ⊢ b ⇓ v →
              ρ ⊢ uapp f a ⇓ v
    ⇓-pair  : ∀ {ρ : UEnv n} {s t v w} →
              ρ ⊢ s ⇓ v → ρ ⊢ t ⇓ w → ρ ⊢ upair s t ⇓ vpair v w
    ⇓-letp  : ∀ {ρ : UEnv n} {s b v w r} →
              ρ ⊢ s ⇓ vpair v w → (w ∷ᵉ v ∷ᵉ ρ) ⊢ b ⇓ r →
              ρ ⊢ uletp s b ⇓ r
    ⇓-inl   : ∀ {ρ : UEnv n} {t v} → ρ ⊢ t ⇓ v → ρ ⊢ uinl t ⇓ vinl v
    ⇓-inr   : ∀ {ρ : UEnv n} {t v} → ρ ⊢ t ⇓ v → ρ ⊢ uinr t ⇓ vinr v
    ⇓-casel : ∀ {ρ : UEnv n} {s l r v w} →
              ρ ⊢ s ⇓ vinl v → (v ∷ᵉ ρ) ⊢ l ⇓ w → ρ ⊢ ucase s l r ⇓ w
    ⇓-caser : ∀ {ρ : UEnv n} {s l r v w} →
              ρ ⊢ s ⇓ vinr v → (v ∷ᵉ ρ) ⊢ r ⇓ w → ρ ⊢ ucase s l r ⇓ w
    ⇓-lit   : ∀ {ρ : UEnv n} {ℓ} → ρ ⊢ ulit ℓ ⇓ vlit ℓ

------------------------------------------------------------------------
-- Typing of untyped terms with erased types.

module Typing {B Lit : Type} (litTy : Lit → B) where
  open Terms Lit

  private
    variable
      n : ℕ

  ECx : ℕ → Type
  ECx n = Fin n → ETy B

  infixl 5 _▹ᵉ_
  _▹ᵉ_ : ECx n → ETy B → ECx (suc n)
  (Δ ▹ᵉ a) zero    = a
  (Δ ▹ᵉ a) (suc i) = Δ i

  ∅ᶜ : ECx 0
  ∅ᶜ ()

  infix 3 _⊢ᵉ_∶_
  data _⊢ᵉ_∶_ : ECx n → UTm n → ETy B → Type where
    u-var  : ∀ {Δ : ECx n} {a} i → Δ i ≡ a → Δ ⊢ᵉ uvar i ∶ a
    u-lam  : ∀ {Δ : ECx n} {a b t} →
             (Δ ▹ᵉ a) ⊢ᵉ t ∶ b → Δ ⊢ᵉ ulam t ∶ earr a b
    u-app  : ∀ {Δ : ECx n} {a b f t} →
             Δ ⊢ᵉ f ∶ earr a b → Δ ⊢ᵉ t ∶ a → Δ ⊢ᵉ uapp f t ∶ b
    u-pair : ∀ {Δ : ECx n} {a b s t} →
             Δ ⊢ᵉ s ∶ a → Δ ⊢ᵉ t ∶ b → Δ ⊢ᵉ upair s t ∶ eprod a b
    u-letp : ∀ {Δ : ECx n} {a b c s t} →
             Δ ⊢ᵉ s ∶ eprod a b → (Δ ▹ᵉ a ▹ᵉ b) ⊢ᵉ t ∶ c →
             Δ ⊢ᵉ uletp s t ∶ c
    u-inl  : ∀ {Δ : ECx n} {a b t} → Δ ⊢ᵉ t ∶ a → Δ ⊢ᵉ uinl t ∶ esum a b
    u-inr  : ∀ {Δ : ECx n} {a b t} → Δ ⊢ᵉ t ∶ b → Δ ⊢ᵉ uinr t ∶ esum a b
    u-case : ∀ {Δ : ECx n} {a b c s l r} →
             Δ ⊢ᵉ s ∶ esum a b →
             (Δ ▹ᵉ a) ⊢ᵉ l ∶ c → (Δ ▹ᵉ b) ⊢ᵉ r ∶ c →
             Δ ⊢ᵉ ucase s l r ∶ c
    u-lit  : ∀ {Δ : ECx n} {b} ℓ → litTy ℓ ≡ b → Δ ⊢ᵉ ulit ℓ ∶ ebase b

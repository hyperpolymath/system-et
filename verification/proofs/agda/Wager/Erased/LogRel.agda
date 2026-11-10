{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on values.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Observational equality of untyped values, at an erased type
-- (Stage 4). It is a logical relation, by recursion on the erased type:
--
--   base type   the two values are one literal of that base type;
--   function    the two values are closures, and on related arguments
--               the two bodies evaluate to related results;
--   pair        the two values are pairs with related components;
--   sum         the two values have one injection and related contents.
--
-- The relation is used in theorem statements only (specification).
-- On a first-order type (no function) it is equality of values.
open import Cubical.Foundations.Prelude

module Wager.Erased.LogRel {B Lit : Type} (litTy : Lit → B) where

open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.Sigma using (_×_; _,_; Σ-syntax)

open import Wager.Erased.Untyped
open Terms Lit

private
  variable
    n m : ℕ

  VRel : Type₁
  VRel = UVal → UVal → Type

data RBase (b : B) : VRel where
  r-lit  : ∀ ℓ → litTy ℓ ≡ b → RBase b (vlit ℓ) (vlit ℓ)

data RArr (P Q : VRel) : VRel where
  r-clo  : ∀ {ρ : UEnv n} {t : UTm (suc n)} {ρ' : UEnv m} {t' : UTm (suc m)} →
           (∀ v w → P v w →
              Σ[ r ∈ UVal ] Σ[ s ∈ UVal ]
                ((v ∷ᵉ ρ) ⊢ t ⇓ r) × ((w ∷ᵉ ρ') ⊢ t' ⇓ s) × Q r s) →
           RArr P Q (vclo ρ t) (vclo ρ' t')

data RProd (P Q : VRel) : VRel where
  r-pair : ∀ {v₁ v₂ w₁ w₂} → P v₁ w₁ → Q v₂ w₂ → RProd P Q (vpair v₁ v₂) (vpair w₁ w₂)

data RSum (P Q : VRel) : VRel where
  r-inl  : ∀ {v w} → P v w → RSum P Q (vinl v) (vinl w)
  r-inr  : ∀ {v w} → Q v w → RSum P Q (vinr v) (vinr w)

-- THE RELATION.
𝒱 : ETy B → UVal → UVal → Type
𝒱 (ebase b)   = RBase b
𝒱 (earr a b)  = RArr (𝒱 a) (𝒱 b)
𝒱 (eprod a b) = RProd (𝒱 a) (𝒱 b)
𝒱 (esum a b)  = RSum (𝒱 a) (𝒱 b)

-- A term in an environment evaluates to a value that is related to v.
𝒞 : ETy B → UVal → UEnv n → UTm n → Type
𝒞 a v ρ t = Σ[ w ∈ UVal ] (ρ ⊢ t ⇓ w) × 𝒱 a v w

-- Two terms in two environments evaluate to related values.
ℰ : ETy B → UEnv n → UTm n → UEnv m → UTm m → Type
ℰ a ρ t ρ' t' = Σ[ v ∈ UVal ] (ρ ⊢ t ⇓ v) × 𝒞 a v ρ' t'

------------------------------------------------------------------------
-- First-order types: on them the relation is equality.

data FO : ETy B → Type where
  fo-base : ∀ {b} → FO (ebase b)
  fo-prod : ∀ {a b} → FO a → FO b → FO (eprod a b)
  fo-sum  : ∀ {a b} → FO a → FO b → FO (esum a b)

𝒱-fo : ∀ {a v w} → FO a → 𝒱 a v w → v ≡ w
𝒱-fo fo-base       (r-lit ℓ p)  = refl
𝒱-fo (fo-prod x y) (r-pair h k) = cong₂ vpair (𝒱-fo x h) (𝒱-fo y k)
𝒱-fo (fo-sum x y)  (r-inl h)    = cong vinl (𝒱-fo x h)
𝒱-fo (fo-sum x y)  (r-inr h)    = cong vinr (𝒱-fo y h)

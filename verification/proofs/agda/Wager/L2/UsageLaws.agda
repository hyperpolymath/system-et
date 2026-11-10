{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on `Fin`.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Laws of usage vectors and usage matrices, for an arbitrary grade
-- algebra. Each law comes from the laws of the algebra, pointwise,
-- and from function extensionality.
open import Cubical.Foundations.Prelude
open import Wager.Grade.Algebra

module Wager.L2.UsageLaws {R : Type} (A : GradeAlgebra R) where

open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)

open GradeAlgebra A
open import Wager.L2.Usage ops

private
  variable
    n m : ℕ

------------------------------------------------------------------------
-- Pointwise laws.

+ᵘ-comm : (γ δ : Usage n) → γ +ᵘ δ ≡ δ +ᵘ γ
+ᵘ-comm γ δ = funExt λ i → add-comm (γ i) (δ i)

+ᵘ-assoc : (γ δ ε : Usage n) → (γ +ᵘ δ) +ᵘ ε ≡ γ +ᵘ (δ +ᵘ ε)
+ᵘ-assoc γ δ ε = funExt λ i → add-assoc (γ i) (δ i) (ε i)

one-·ᵘ : (γ : Usage n) → 𝟙 ·ᵘ γ ≡ γ
one-·ᵘ γ = funExt λ i → one-mul (γ i)

≤ᵘ-refl : (γ : Usage n) → γ ≤ᵘ γ
≤ᵘ-refl γ i = le-refl (γ i)

≤ᵘ-trans : {γ δ ε : Usage n} → γ ≤ᵘ δ → δ ≤ᵘ ε → γ ≤ᵘ ε
≤ᵘ-trans p q i = le-trans _ _ _ (p i) (q i)

≡→≤ᵘ : {γ δ : Usage n} → γ ≡ δ → γ ≤ᵘ δ
≡→≤ᵘ {γ = γ} p = subst (γ ≤ᵘ_) p (≤ᵘ-refl γ)

+ᵘ-mono : {γ γ' δ δ' : Usage n} → γ ≤ᵘ γ' → δ ≤ᵘ δ' → (γ +ᵘ δ) ≤ᵘ (γ' +ᵘ δ')
+ᵘ-mono p q i = add-mono _ _ _ _ (p i) (q i)

private
  interchange : (a b c d : R) → (a + b) + (c + d) ≡ (a + c) + (b + d)
  interchange a b c d =
    add-assoc a b (c + d)
    ∙ cong (a +_) (sym (add-assoc b c d) ∙ cong (_+ d) (add-comm b c) ∙ add-assoc c b d)
    ∙ sym (add-assoc a c (b + d))

------------------------------------------------------------------------
-- The vector-matrix product.

⊛-zero : (Ψ : Mat n m) → 0ᵘ ⊛ Ψ ≡ 0ᵘ
⊛-zero {n = zero}  Ψ = refl
⊛-zero {n = suc n} Ψ = funExt λ j →
  cong₂ _+_ (zero-mul (Ψ zero j)) (funExt⁻ (⊛-zero (λ i → Ψ (suc i))) j) ∙ add-zero 𝟘

-- The unit vector at i selects the row i.
⊛-unit : (i : Fin n) (Ψ : Mat n m) → unit i ⊛ Ψ ≡ Ψ i
⊛-unit zero    Ψ = funExt λ j →
  cong₂ _+_ (one-mul (Ψ zero j)) (funExt⁻ (⊛-zero (λ i → Ψ (suc i))) j) ∙ add-zero (Ψ zero j)
⊛-unit (suc i) Ψ = funExt λ j →
  cong₂ _+_ (zero-mul (Ψ zero j)) (funExt⁻ (⊛-unit i (λ i → Ψ (suc i))) j)
  ∙ zero-add (Ψ (suc i) j)

-- The product is linear in the vector.
⊛-+ᵘ : (γ γ' : Usage n) (Ψ : Mat n m) → (γ +ᵘ γ') ⊛ Ψ ≡ (γ ⊛ Ψ) +ᵘ (γ' ⊛ Ψ)
⊛-+ᵘ {n = zero}  γ γ' Ψ = funExt λ j → sym (add-zero 𝟘)
⊛-+ᵘ {n = suc n} γ γ' Ψ = funExt λ j →
  cong₂ _+_ (right-distrib (γ zero) (γ' zero) (Ψ zero j))
            (funExt⁻ (⊛-+ᵘ (λ i → γ (suc i)) (λ i → γ' (suc i)) (λ i → Ψ (suc i))) j)
  ∙ interchange _ _ _ _

⊛-·ᵘ : (r : R) (γ : Usage n) (Ψ : Mat n m) → (r ·ᵘ γ) ⊛ Ψ ≡ r ·ᵘ (γ ⊛ Ψ)
⊛-·ᵘ {n = zero}  r γ Ψ = funExt λ j → sym (mul-zero r)
⊛-·ᵘ {n = suc n} r γ Ψ = funExt λ j →
  cong₂ _+_ (mul-assoc r (γ zero) (Ψ zero j))
            (funExt⁻ (⊛-·ᵘ r (λ i → γ (suc i)) (λ i → Ψ (suc i))) j)
  ∙ sym (left-distrib r _ _)

-- The product is monotone in the vector.
⊛-mono : {γ γ' : Usage n} (Ψ : Mat n m) → γ ≤ᵘ γ' → (γ ⊛ Ψ) ≤ᵘ (γ' ⊛ Ψ)
⊛-mono {n = zero}  Ψ h j = le-refl 𝟘
⊛-mono {n = suc n} Ψ h j =
  add-mono _ _ _ _ (mul-mono _ _ _ _ (h zero) (le-refl (Ψ zero j)))
                   (⊛-mono (λ i → Ψ (suc i)) (λ i → h (suc i)) j)

private
  shift-pt : (γ : Usage n) (Ψ : Mat n m) → ∀ j →
             (γ ⊛ (λ i → Ψ i ▹ 𝟘)) j ≡ ((γ ⊛ Ψ) ▹ 𝟘) j
  shift-pt {n = zero}  γ Ψ zero    = refl
  shift-pt {n = zero}  γ Ψ (suc j) = refl
  shift-pt {n = suc n} γ Ψ zero    =
    cong₂ _+_ (mul-zero (γ zero)) (shift-pt (λ i → γ (suc i)) (λ i → Ψ (suc i)) zero)
    ∙ add-zero 𝟘
  shift-pt {n = suc n} γ Ψ (suc j) =
    cong (γ zero · Ψ zero j +_) (shift-pt (λ i → γ (suc i)) (λ i → Ψ (suc i)) (suc j))

-- A matrix whose rows do not use a new variable.
⊛-shift : (γ : Usage n) (Ψ : Mat n m) → γ ⊛ (λ i → Ψ i ▹ 𝟘) ≡ (γ ⊛ Ψ) ▹ 𝟘
⊛-shift γ Ψ = funExt (shift-pt γ Ψ)

private
  lift-pt : (γ : Usage n) (q : R) (Ψ : Mat n m) → ∀ j →
            ((γ ▹ q) ⊛ liftM Ψ) j ≡ ((γ ⊛ Ψ) ▹ q) j
  lift-pt γ q Ψ zero    = cong₂ _+_ (mul-one q) (shift-pt γ Ψ zero) ∙ add-zero q
  lift-pt γ q Ψ (suc j) = cong₂ _+_ (mul-zero q) (shift-pt γ Ψ (suc j)) ∙ zero-add _

-- The product under one more binder.
⊛-lift : (γ : Usage n) (q : R) (Ψ : Mat n m) → (γ ▹ q) ⊛ liftM Ψ ≡ (γ ⊛ Ψ) ▹ q
⊛-lift γ q Ψ = funExt (lift-pt γ q Ψ)

private
  id-pt : (γ : Usage n) → ∀ j → (γ ⊛ unit) j ≡ γ j
  id-pt {n = suc n} γ zero    =
    cong₂ _+_ (mul-one (γ zero)) (shift-pt (λ i → γ (suc i)) unit zero) ∙ add-zero (γ zero)
  id-pt {n = suc n} γ (suc j) =
    cong₂ _+_ (mul-zero (γ zero))
              (shift-pt (λ i → γ (suc i)) unit (suc j) ∙ id-pt (λ i → γ (suc i)) j)
    ∙ zero-add (γ (suc j))

-- The identity matrix.
⊛-id : (γ : Usage n) → γ ⊛ unit ≡ γ
⊛-id γ = funExt (id-pt γ)

-- The matrix of weakening.
⊛-wk : (γ : Usage n) → γ ⊛ (λ i → unit (suc i)) ≡ γ ▹ 𝟘
⊛-wk γ = ⊛-shift γ unit ∙ cong (_▹ 𝟘) (⊛-id γ)


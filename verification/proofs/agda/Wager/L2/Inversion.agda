{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on typing derivations.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Inversion of typing for a variable, a literal and an application,
-- through `t-conv` and `t-sub`. The proofs that a program has NO
-- typing use these lemmas.
open import Wager.L1.Signature
open import Wager.Grade.Algebra
import Wager.L2.Signature

module Wager.L2.Inversion
  (S : Sig) (TS : Wager.L2.Signature.TSig S) (R : GradeAlgebra (Sig.TG S)) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Sigma using (_×_; Σ-syntax)

open import Wager.L1.Syntax S using (Ty; ★; []; TG; arr; base)
open import Wager.L1.Conversion S
open GradeAlgebra R
open import Wager.L2.Typing S TS ops
open import Wager.L2.UsageLaws R

private
  variable
    n : ℕ

inv-var : {γ : Usage n} {Γ : Cx n} {i : Fin n} {C : Ty [] ★} →
          γ ▸ Γ ⊢ tvar i ∶ C → (unit i ≤ᵘ γ) × DefEq (Γ i) C
inv-var (t-var i)    = ≤ᵘ-refl _ , d-refl
inv-var (t-conv d e) = let (le , c) = inv-var d in le , d-trans c e
inv-var (t-sub d le) = let (le' , c) = inv-var d in ≤ᵘ-trans le' le , c

inv-lit : {γ : Usage n} {Γ : Cx n} {ℓ : Lit} {C : Ty [] ★} →
          γ ▸ Γ ⊢ lit ℓ ∶ C → (0ᵘ ≤ᵘ γ) × DefEq (base (litTy ℓ)) C
inv-lit (t-lit ℓ)    = ≤ᵘ-refl _ , d-refl
inv-lit (t-conv d e) = let (le , c) = inv-lit d in le , d-trans c e
inv-lit (t-sub d le) = let (le' , c) = inv-lit d in ≤ᵘ-trans le' le , c

inv-app : {γ : Usage n} {Γ : Cx n} {f a : Tm n} {C : Ty [] ★} →
          γ ▸ Γ ⊢ tapp f a ∶ C →
          Σ[ q ∈ TG ] Σ[ A ∈ Ty [] ★ ] Σ[ B ∈ Ty [] ★ ] Σ[ γ₁ ∈ Usage n ] Σ[ γ₂ ∈ Usage n ]
            DefEq B C × ((γ₁ +ᵘ (q ·ᵘ γ₂)) ≤ᵘ γ)
            × (γ₁ ▸ Γ ⊢ f ∶ arr q A B) × (γ₂ ▸ Γ ⊢ a ∶ A)
inv-app (t-app d e)  = _ , _ , _ , _ , _ , d-refl , ≤ᵘ-refl _ , d , e
inv-app (t-conv d e) =
  let (q , A , B , γ₁ , γ₂ , c , le , d₁ , d₂) = inv-app d
  in q , A , B , γ₁ , γ₂ , d-trans c e , le , d₁ , d₂
inv-app (t-sub d le) =
  let (q , A , B , γ₁ , γ₂ , c , le' , d₁ , d₂) = inv-app d
  in q , A , B , γ₁ , γ₂ , c , ≤ᵘ-trans le' le , d₁ , d₂

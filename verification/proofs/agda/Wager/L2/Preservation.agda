{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on typing derivations.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- T0, preservation, for an arbitrary grade algebra.
--
-- Where a System FC proof inverts a coercion, this proof uses
-- "conversion is normalize-then-compare": the type formers are
-- injective up to `DefEq` (Wager.L1.Heads).
open import Wager.L1.Signature
open import Wager.Grade.Algebra
import Wager.L2.Signature

module Wager.L2.Preservation
  (S : Sig) (TS : Wager.L2.Signature.TSig S) (R : GradeAlgebra (Sig.TG S)) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Sigma using (_×_; Σ-syntax)
open import Cubical.Data.Empty as ⊥ using (⊥)

open import Wager.L1.Syntax S using (Ty; ★; []; TG; Con₁; arr; _⊗_; _⊕_; capp; base)
open import Wager.L1.Conversion S
open import Wager.L1.Heads S
open GradeAlgebra R
open import Wager.L2.Typing S TS ops
open import Wager.L2.UsageLaws R
open import Wager.L2.Renaming S TS R
open import Wager.L2.Substitution S TS R

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Inversion of the typing of a value form, through `t-conv` and `t-sub`.

inv-lam : {γ : Usage n} {Γ : Cx n} {q : TG} {A C : Ty [] ★} {b : Tm (suc n)} →
          γ ▸ Γ ⊢ tlam q A b ∶ C →
          Σ[ B ∈ Ty [] ★ ] Σ[ γ' ∈ Usage n ]
            DefEq (arr q A B) C × (γ' ≤ᵘ γ) × ((γ' ▹ q) ▸ (Γ ▹ᶜ A) ⊢ b ∶ B)
inv-lam (t-lam d)    = _ , _ , d-refl , ≤ᵘ-refl _ , d
inv-lam (t-conv d e) =
  let (B , γ' , c , le , d') = inv-lam d in B , γ' , d-trans c e , le , d'
inv-lam (t-sub d le) =
  let (B , γ' , c , le' , d') = inv-lam d in B , γ' , c , ≤ᵘ-trans le' le , d'

inv-pair : {γ : Usage n} {Γ : Cx n} {C : Ty [] ★} {s t : Tm n} →
           γ ▸ Γ ⊢ pair s t ∶ C →
           Σ[ A ∈ Ty [] ★ ] Σ[ B ∈ Ty [] ★ ] Σ[ γ₁ ∈ Usage n ] Σ[ γ₂ ∈ Usage n ]
             DefEq (A ⊗ B) C × ((γ₁ +ᵘ γ₂) ≤ᵘ γ) × (γ₁ ▸ Γ ⊢ s ∶ A) × (γ₂ ▸ Γ ⊢ t ∶ B)
inv-pair (t-pair d e) = _ , _ , _ , _ , d-refl , ≤ᵘ-refl _ , d , e
inv-pair (t-conv d e) =
  let (A , B , γ₁ , γ₂ , c , le , d₁ , d₂) = inv-pair d
  in A , B , γ₁ , γ₂ , d-trans c e , le , d₁ , d₂
inv-pair (t-sub d le) =
  let (A , B , γ₁ , γ₂ , c , le' , d₁ , d₂) = inv-pair d
  in A , B , γ₁ , γ₂ , c , ≤ᵘ-trans le' le , d₁ , d₂

inv-inj₁ : {γ : Usage n} {Γ : Cx n} {C : Ty [] ★} {t : Tm n} →
           γ ▸ Γ ⊢ inj₁ t ∶ C →
           Σ[ A ∈ Ty [] ★ ] Σ[ B ∈ Ty [] ★ ] Σ[ γ' ∈ Usage n ]
             DefEq (A ⊕ B) C × (γ' ≤ᵘ γ) × (γ' ▸ Γ ⊢ t ∶ A)
inv-inj₁ (t-inj₁ d)   = _ , _ , _ , d-refl , ≤ᵘ-refl _ , d
inv-inj₁ (t-conv d e) =
  let (A , B , γ' , c , le , d') = inv-inj₁ d in A , B , γ' , d-trans c e , le , d'
inv-inj₁ (t-sub d le) =
  let (A , B , γ' , c , le' , d') = inv-inj₁ d in A , B , γ' , c , ≤ᵘ-trans le' le , d'

inv-inj₂ : {γ : Usage n} {Γ : Cx n} {C : Ty [] ★} {t : Tm n} →
           γ ▸ Γ ⊢ inj₂ t ∶ C →
           Σ[ A ∈ Ty [] ★ ] Σ[ B ∈ Ty [] ★ ] Σ[ γ' ∈ Usage n ]
             DefEq (A ⊕ B) C × (γ' ≤ᵘ γ) × (γ' ▸ Γ ⊢ t ∶ B)
inv-inj₂ (t-inj₂ d)   = _ , _ , _ , d-refl , ≤ᵘ-refl _ , d
inv-inj₂ (t-conv d e) =
  let (A , B , γ' , c , le , d') = inv-inj₂ d in A , B , γ' , d-trans c e , le , d'
inv-inj₂ (t-sub d le) =
  let (A , B , γ' , c , le' , d') = inv-inj₂ d in A , B , γ' , c , ≤ᵘ-trans le' le , d'

------------------------------------------------------------------------
-- The raw value under the transitions of a value in a trope state.

peel-typing : {γ : Usage n} {Γ : Cx n} {v : Tm n} {C : Ty [] ★} →
              Value v → γ ▸ Γ ⊢ v ∶ C →
              (m : Maybe Con₁) (A : Ty [] ★) → DefEq C (A at m) →
              γ ▸ Γ ⊢ peel m v ∶ A
peel-typing val d nothing A c = t-conv d c
peel-typing val (t-conv d e) (just s) A c = peel-typing val d (just s) A (d-trans e c)
peel-typing val (t-sub d le) (just s) A c = t-sub (peel-typing val d (just s) A c) le
peel-typing v-lam          (t-lam d)    (just s) A c = ⊥.rec (headClash c refl)
peel-typing (v-pair _ _)   (t-pair d e) (just s) A c = ⊥.rec (headClash c refl)
peel-typing (v-inj₁ _)     (t-inj₁ d)   (just s) A c = ⊥.rec (headClash c refl)
peel-typing (v-inj₂ _)     (t-inj₂ d)   (just s) A c = ⊥.rec (headClash c refl)
peel-typing v-lit          (t-lit ℓ)    (just s) A c = ⊥.rec (headClash c refl)
peel-typing (v-step val p) (t-step o d) (just s) A c =
  t-conv (peel-typing val d (from o) (carrier o) d-refl)
         (snd (capp-inj (subst (λ m → DefEq (carrier o at m) (capp s A)) p c)))

------------------------------------------------------------------------
-- Preservation.

private
  -- 𝟙·g₂ + (𝟙·g₁ + d) = (g₁ + g₂) + d
  pair-usage : (γ₁ γ₂ δ : Usage n) →
               ((𝟙 ·ᵘ γ₂) +ᵘ ((𝟙 ·ᵘ γ₁) +ᵘ δ)) ≡ ((γ₁ +ᵘ γ₂) +ᵘ δ)
  pair-usage γ₁ γ₂ δ =
    cong₂ (λ x y → x +ᵘ (y +ᵘ δ)) (one-·ᵘ γ₂) (one-·ᵘ γ₁)
    ∙ sym (+ᵘ-assoc γ₂ γ₁ δ)
    ∙ cong (_+ᵘ δ) (+ᵘ-comm γ₂ γ₁)

  -- d + 𝟙·g = g + d
  case-usage : (γ' δ : Usage n) → (δ +ᵘ (𝟙 ·ᵘ γ')) ≡ (γ' +ᵘ δ)
  case-usage γ' δ = cong (δ +ᵘ_) (one-·ᵘ γ') ∙ +ᵘ-comm δ γ'

preservation : {γ : Usage n} {Γ : Cx n} {t t' : Tm n} {A : Ty [] ★} →
               γ ▸ Γ ⊢ t ∶ A → t ⟶ t' → γ ▸ Γ ⊢ t' ∶ A
preservation (t-conv d e) r = t-conv (preservation d r) e
preservation (t-sub d le) r = t-sub (preservation d r) le
preservation (t-app d e) (ξ-app₁ r)   = t-app (preservation d r) e
preservation (t-app d e) (ξ-app₂ _ r) = t-app d (preservation e r)
preservation (t-app {γ = γ} {δ = δ} d e) (β-lam _) =
  let (B' , γ' , c , le , d') = inv-lam d
      (pq , cA , cB)          = arr-inj c
  in t-sub (t-conv (subst-lemma d' (t-conv e (d-sym cA))) cB)
           (+ᵘ-mono le (≡→≤ᵘ (cong (_·ᵘ δ) pq)))
preservation (t-pair d e) (ξ-pair₁ r)   = t-pair (preservation d r) e
preservation (t-pair d e) (ξ-pair₂ _ r) = t-pair d (preservation e r)
preservation (t-letp d e) (ξ-letp r) = t-letp (preservation d r) e
preservation (t-letp {δ = δ} d e) (β-pair _ _) =
  let (A' , B' , γ₁ , γ₂ , c , le , d₁ , d₂) = inv-pair d
      (cA , cB)                              = prod-inj c
  in t-sub (castU (pair-usage γ₁ γ₂ δ) (subst-lemma₂ e (t-conv d₁ cA) (t-conv d₂ cB)))
           (+ᵘ-mono le (≤ᵘ-refl δ))
preservation (t-inj₁ d) (ξ-inj₁ r) = t-inj₁ (preservation d r)
preservation (t-inj₂ d) (ξ-inj₂ r) = t-inj₂ (preservation d r)
preservation (t-case d l r) (ξ-case s) = t-case (preservation d s) l r
preservation (t-case {δ = δ} d l r) (β-inj₁ _) =
  let (A' , B' , γ' , c , le , d') = inv-inj₁ d
      (cA , cB)                    = sum-inj c
  in t-sub (castU (case-usage γ' δ) (subst-lemma l (t-conv d' cA)))
           (+ᵘ-mono le (≤ᵘ-refl δ))
preservation (t-case {δ = δ} d l r) (β-inj₂ _) =
  let (A' , B' , γ' , c , le , d') = inv-inj₂ d
      (cA , cB)                    = sum-inj c
  in t-sub (castU (case-usage γ' δ) (subst-lemma r (t-conv d' cB)))
           (+ᵘ-mono le (≤ᵘ-refl δ))
preservation (t-step o d) (ξ-step r) = t-step o (preservation d r)
preservation {γ = γ} {Γ} (t-step {t = v} o d) (β-strip val p) =
  subst (λ m → γ ▸ Γ ⊢ peel (from o) v ∶ carrier o at m) (sym p)
        (peel-typing val d (from o) (carrier o) d-refl)

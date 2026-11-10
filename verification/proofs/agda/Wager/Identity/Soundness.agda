{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on variables (Fin).
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The erasure of proofs is sound (Stage 6, part 2: theorem T7).
--
--   1. The target is a part of the extension (`emb-typed`, `emb-keep`,
--      `emb-erase`).
--   2. A conversion gives evidence (`intro`).
--   3. The fundamental lemma (`fund`): for a typed term, in two related
--      environments, the reference program and the program with no
--      evidence in its casts evaluate to related values. The case of a
--      cast uses the value of the evidence: it is a literal of the type
--      `Id A B`, so A and B have one erased type (`evidence`).
--   4. Closed terms: `erasure-sound`, `erasure-sound-fo`, `canonicity`.
--   5. The grade: `cast-free`, and the function `use-assumption`.
--
-- `fund` does not use the grade of the rule `t-cast`. `cast-free` does.
open import Wager.L1.Signature
open import Wager.Grade.Algebra
import Wager.L2.Signature
import Wager.Identity.Family
module Wager.Identity.Soundness
  (S : Sig) (TS : Wager.L2.Signature.TSig S) (ops : GradeOps (Sig.TG S))
  (F : Wager.Identity.Family.IdFamily S TS) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Sigma using (_×_; _,_; Σ-syntax)

open import Wager.L1.Syntax S
open import Wager.L1.Conversion S
open import Wager.L1.Equality S
import Wager.L2.Typing
open import Wager.L2.Term S TS using (Tm; tvar; tlam; tapp; pair; letp; inj₁; inj₂; case; lit; step)
open import Wager.L2.Erasure S TS ops using (erT; erN; er-at; eraseᵗ)
open import Wager.Identity.Typing S TS ops F
open import Wager.Erased.Untyped
open Terms Lit
open import Wager.Erased.LogRel litTy
open GradeOps ops

private
  module T = Wager.L2.Typing S TS ops

  variable
    n : ℕ

------------------------------------------------------------------------
-- 1. The target is a part of the extension.

emb-typed : ∀ {γ : Usage n} {Γ : Cx n} {t A} → γ T.▸ Γ ⊢ t ∶ A → γ ▸ Γ ⊢ⁱ emb t ∶ A
emb-typed (T.t-var i)      = t-var i
emb-typed (T.t-lam d)      = t-lam (emb-typed d)
emb-typed (T.t-app d e)    = t-app (emb-typed d) (emb-typed e)
emb-typed (T.t-pair d e)   = t-pair (emb-typed d) (emb-typed e)
emb-typed (T.t-letp d e)   = t-letp (emb-typed d) (emb-typed e)
emb-typed (T.t-inj₁ d)     = t-inj₁ (emb-typed d)
emb-typed (T.t-inj₂ d)     = t-inj₂ (emb-typed d)
emb-typed (T.t-case d l r) = t-case (emb-typed d) (emb-typed l) (emb-typed r)
emb-typed (T.t-lit ℓ)      = t-lit ℓ
emb-typed (T.t-step o d)   = t-step o (emb-typed d)
emb-typed (T.t-conv d e)   = t-conv (emb-typed d) e
emb-typed (T.t-sub d le)   = t-sub (emb-typed d) le

-- A target term has no cast, so its two erasures are its erasure.
emb-keep : (t : Tm n) → keepⁱ (emb t) ≡ eraseᵗ t
emb-keep (tvar i)       = refl
emb-keep (tlam q A b)   = cong ulam (emb-keep b)
emb-keep (tapp f a)     = cong₂ uapp (emb-keep f) (emb-keep a)
emb-keep (pair s t)     = cong₂ upair (emb-keep s) (emb-keep t)
emb-keep (letp s b)     = cong₂ uletp (emb-keep s) (emb-keep b)
emb-keep (inj₁ t)       = cong uinl (emb-keep t)
emb-keep (inj₂ t)       = cong uinr (emb-keep t)
emb-keep (case s l r) i = ucase (emb-keep s i) (emb-keep l i) (emb-keep r i)
emb-keep (lit ℓ)        = refl
emb-keep (step o t)     = emb-keep t

emb-erase : (t : Tm n) → eraseⁱ (emb t) ≡ eraseᵗ t
emb-erase (tvar i)       = refl
emb-erase (tlam q A b)   = cong ulam (emb-erase b)
emb-erase (tapp f a)     = cong₂ uapp (emb-erase f) (emb-erase a)
emb-erase (pair s t)     = cong₂ upair (emb-erase s) (emb-erase t)
emb-erase (letp s b)     = cong₂ uletp (emb-erase s) (emb-erase b)
emb-erase (inj₁ t)       = cong uinl (emb-erase t)
emb-erase (inj₂ t)       = cong uinr (emb-erase t)
emb-erase (case s l r) i = ucase (emb-erase s i) (emb-erase l i) (emb-erase r i)
emb-erase (lit ℓ)        = refl
emb-erase (step o t)     = emb-erase t

------------------------------------------------------------------------
-- 2. A conversion gives evidence.

intro : ∀ {Γ : Cx n} {A B} → DefEq A B → 0ᵘ ▸ Γ ⊢ⁱ ilit (rfl A) ∶ base (Id A B)
intro {A = A} d =
  t-conv (t-lit (rfl A)) (≡→DefEq (cong base (rfl-ty A ∙ Id-conv d-refl d)))

------------------------------------------------------------------------
-- 3. The fundamental lemma.

-- Two environments give related values to each variable.
EnvRel : Cx n → UEnv n → UEnv n → Type
EnvRel Γ ρ ρ' = ∀ i → 𝒱 (erT (Γ i)) (ρ i) (ρ' i)

env-ext : ∀ {Γ : Cx n} {ρ ρ' : UEnv n} {v w} A →
          EnvRel Γ ρ ρ' → 𝒱 (erT A) v w → EnvRel (Γ ▹ᶜ A) (v ∷ᵉ ρ) (w ∷ᵉ ρ')
env-ext A h hvw zero    = hvw
env-ext A h hvw (suc i) = h i

-- The value of evidence is a literal of the type `Id A B`. The family
-- has no literal off the diagonal, so A and B are convertible, and
-- they have one erased type.
evidence : ∀ {A B v w} → RBase (Id A B) v w → erT A ≡ erT B
evidence (r-lit ℓ p) = cong erN (defEq→nf (diagonal ℓ p))

fund : ∀ {γ : Usage n} {Γ : Cx n} {t A} → γ ▸ Γ ⊢ⁱ t ∶ A →
       {ρ ρ' : UEnv n} → EnvRel Γ ρ ρ' →
       ℰ (erT A) ρ (keepⁱ t) ρ' (eraseⁱ t)
fund (t-var i) h = _ , ⇓-var i , _ , ⇓-var i , h i
fund (t-lam {A = A} d) h =
    _ , ⇓-lam , _ , ⇓-lam
  , r-clo (λ v w hvw →
      let (r , dr , s , ds , hrs) = fund d (env-ext A h hvw)
      in r , s , dr , ds , hrs)
fund (t-app d e) h with fund d h | fund e h
... | _ , df , _ , df' , r-clo hf | va , da , wa , da' , ha =
  let (r , s , dr , ds , hrs) = hf va wa ha
  in r , ⇓-app df da dr , s , ⇓-app df' da' ds , hrs
fund (t-pair d e) h =
  let (v₁ , d₁ , w₁ , d₁' , h₁) = fund d h
      (v₂ , d₂ , w₂ , d₂' , h₂) = fund e h
  in vpair v₁ v₂ , ⇓-pair d₁ d₂ , vpair w₁ w₂ , ⇓-pair d₁' d₂' , r-pair h₁ h₂
fund (t-letp {A = A} {B = B} d e) h with fund d h
... | _ , ds , _ , ds' , r-pair h₁ h₂ =
  let (r , dr , r' , dr' , hr) = fund e (env-ext B (env-ext A h h₁) h₂)
  in r , ⇓-letp ds dr , r' , ⇓-letp ds' dr' , hr
fund (t-inj₁ d) h =
  let (v , dv , w , dw , hv) = fund d h
  in vinl v , ⇓-inl dv , vinl w , ⇓-inl dw , r-inl hv
fund (t-inj₂ d) h =
  let (v , dv , w , dw , hv) = fund d h
  in vinr v , ⇓-inr dv , vinr w , ⇓-inr dw , r-inr hv
fund (t-case {A = A} {B = B} d l r) h with fund d h
... | _ , ds , _ , ds' , r-inl hv =
  let (x , dx , x' , dx' , hx) = fund l (env-ext A h hv)
  in x , ⇓-casel ds dx , x' , ⇓-casel ds' dx' , hx
... | _ , ds , _ , ds' , r-inr hv =
  let (x , dx , x' , dx' , hx) = fund r (env-ext B h hv)
  in x , ⇓-caser ds dx , x' , ⇓-caser ds' dx' , hx
fund (t-lit ℓ) h = vlit ℓ , ⇓-lit , vlit ℓ , ⇓-lit , r-lit ℓ refl
-- A trope transition: the two states have one erased type.
fund (t-step {t = t} o d) {ρ} {ρ'} h =
  subst (λ a → ℰ a ρ (keepⁱ t) ρ' (eraseⁱ t))
        (er-at (carrier o) (from o) ∙ sym (er-at (carrier o) (to o)))
        (fund d h)
-- Conversion: the two types have one normal form.
fund (t-conv {t = t} d e) {ρ} {ρ'} h =
  subst (λ a → ℰ a ρ (keepⁱ t) ρ' (eraseⁱ t)) (cong erN (defEq→nf e)) (fund d h)
fund (t-sub d _) h = fund d h
-- THE CAST. The reference program evaluates the evidence, and the lemma
-- for the evidence gives its value. The other program has no evidence.
fund (t-cast de dt) h =
  let (ve , dke , we , dee , he) = fund de h
      (v , dv , w , dw , hv)     = fund dt h
  in v , ⇓-letp (⇓-pair dke dv) (⇓-var zero) , w , dw
   , subst (λ a → 𝒱 a v w) (evidence he) hv

------------------------------------------------------------------------
-- 4. Closed terms.

-- T7: the erasure of proofs is sound.
erasure-sound : ∀ {γ : Usage 0} {Γ : Cx 0} {t A} → γ ▸ Γ ⊢ⁱ t ∶ A →
  Σ[ v ∈ UVal ] Σ[ w ∈ UVal ]
    (∅ᵉ ⊢ keepⁱ t ⇓ v) × (∅ᵉ ⊢ eraseⁱ t ⇓ w) × 𝒱 (erT A) v w
erasure-sound d =
  let (v , dv , w , dw , h) = fund d {ρ = ∅ᵉ} {ρ' = ∅ᵉ} (λ ())
  in v , w , dv , dw , h

erasure-sound-fo : ∀ {γ : Usage 0} {Γ : Cx 0} {t A} → γ ▸ Γ ⊢ⁱ t ∶ A → FO (erT A) →
  Σ[ v ∈ UVal ] (∅ᵉ ⊢ keepⁱ t ⇓ v) × (∅ᵉ ⊢ eraseⁱ t ⇓ v)
erasure-sound-fo {t = t} d fo =
  let (v , w , dv , dw , h) = erasure-sound d
  in v , dv , subst (λ x → ∅ᵉ ⊢ eraseⁱ t ⇓ x) (sym (𝒱-fo fo h)) dw

-- Closed evidence gives a conversion.
canonicity : ∀ {γ : Usage 0} {Γ : Cx 0} {e A B} →
             γ ▸ Γ ⊢ⁱ e ∶ base (Id A B) → DefEq A B
canonicity d with erasure-sound d
... | _ , _ , _ , _ , r-lit ℓ p = diagonal ℓ p

------------------------------------------------------------------------
-- 5. The grade.

-- Evidence costs nothing: 𝟘 · γ + δ is δ.
cast-free : GradeLaws ops →
            ∀ {γ δ : Usage n} {Γ : Cx n} {e t A B} →
            γ ▸ Γ ⊢ⁱ e ∶ base (Id A B) → δ ▸ Γ ⊢ⁱ t ∶ A →
            δ ▸ Γ ⊢ⁱ cast e t ∶ B
cast-free laws {γ = γ} {δ = δ} {Γ = Γ} {e = e} {t = t} {B = B} de dt =
  subst (λ u → u ▸ Γ ⊢ⁱ cast e t ∶ B)
        (funExt (λ i → cong (_+ δ i) (zero-mul (γ i)) ∙ zero-add (δ i)))
        (t-cast de dt)
  where open GradeLaws laws

-- A local equality assumption is a variable at the grade 𝟘.
assumption : GradeLaws ops → ∀ (A B : Ty [] ★) {Γ : Cx 0} →
             0ᵘ ▸ Γ ⊢ⁱ use-assumption A B ∶ arr 𝟘 (base (Id A B)) (arr 𝟙 A B)
assumption laws A B {Γ} = t-lam (t-lam body)
  where
  Γ' : Cx 2
  Γ' = Γ ▹ᶜ base (Id A B) ▹ᶜ A

  -- The usage of the payload: the last variable once, no other variable.
  path : ∀ i → unit {n = 2} zero i ≡ (0ᵘ ▹ 𝟘 ▹ 𝟙) i
  path zero       = refl
  path (suc zero) = refl

  body : (0ᵘ ▹ 𝟘 ▹ 𝟙) ▸ Γ' ⊢ⁱ cast (ivar (suc zero)) (ivar zero) ∶ B
  body = subst (λ u → u ▸ Γ' ⊢ⁱ cast (ivar (suc zero)) (ivar zero) ∶ B)
               (funExt path)
               (cast-free laws (t-var (suc zero)) (t-var zero))

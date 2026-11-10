{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded syntax.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Nominal equality of the source becomes conversion in the target
-- (Stage 4, a lemma for the typing of translated casts).
--
-- The normal form of a translated type is a function of the nominal
-- value of the source type. Two source types with one nominal value
-- thus have translations with one normal form.
open import Cubical.Foundations.Prelude
open import Wager.FC.Signature
open import Wager.Grade.Algebra
import Wager.Trans.Scheme

module Wager.Trans.Nominal
  (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
  {R : Type} (ops : GradeOps R) where

open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)

open import Wager.Role.Role
open import Wager.Erased.Untyped using (ETy; ebase; earr; eprod; esum)
open import Wager.FC.Types SS
open import Wager.FC.Coercion SS
open import Wager.FC.RoleSoundness SS using (nom-sound)
open import Wager.Trans.Target SS Sc ops
open import Wager.L1.Conversion tSig
open import Wager.L1.Normal tSig
open import Wager.L1.Eval tSig
open import Wager.L1.Equality tSig
open GradeOps ops using (𝟙)

-- The normal form of the translated body, from the value of the
-- parameter and the normal form of the translated parameter.
TVB : Body Base Fam → VTy → Nf [] ★ → Nf [] ★
TVB bvar        v n = n
TVB (bbase b)   v n = nbase b
TVB (barr β γ)  v n = narr 𝟙 (TVB β v n) (TVB γ v n)
TVB (bprod β γ) v n = TVB β v n n⊗ TVB γ v n
TVB (bsum β γ)  v n = TVB β v n n⊕ TVB γ v n
TVB (bfam F β)  v n = nbase (applyF F (evB β v))

-- The normal form of the translation, from the nominal value.
TV : VTy → Nf [] ★
TV (vbase b)   = nbase b
TV (varr v w)  = narr 𝟙 (TV v) (TV w)
TV (vprod v w) = TV v n⊗ TV w
TV (vsum v w)  = TV v n⊕ TV w
TV (vnt₀ N)    = ncapp (inl N) (nf (TE (rep₀ N)))
TV (vnt₁ N v)  = ncapp (inr (N , idx N v)) (TVB (body N) v (TV v))

-- A target primitive computes the source function.
insp-V : ∀ F v → inspect F (TV v) ≡ nbase (applyF F v)
insp-V F (vbase b)   = refl
insp-V F (varr v w)  = refl
insp-V F (vprod v w) = refl
insp-V F (vsum v w)  = refl
insp-V F (vnt₀ N)    = refl
insp-V F (vnt₁ N v)  = cong nbase (obs-ok F N v)

insp-B : ∀ F β v → inspect F (TVB β v (TV v)) ≡ nbase (applyF F (evB β v))
insp-B F bvar        v = insp-V F v
insp-B F (bbase b)   v = refl
insp-B F (barr β γ)  v = refl
insp-B F (bprod β γ) v = refl
insp-B F (bsum β γ)  v = refl
insp-B F (bfam G β)  v = refl

nf-TB : ∀ β v (A : Ty [] ★) → nf A ≡ TV v → nf (TB β A) ≡ TVB β v (TV v)
nf-TB bvar        v A h = h
nf-TB (bbase b)   v A h = refl
nf-TB (barr β γ)  v A h = cong₂ (narr 𝟙) (nf-TB β v A h) (nf-TB γ v A h)
nf-TB (bprod β γ) v A h = cong₂ _n⊗_ (nf-TB β v A h) (nf-TB γ v A h)
nf-TB (bsum β γ)  v A h = cong₂ _n⊕_ (nf-TB β v A h) (nf-TB γ v A h)
nf-TB (bfam F β)  v A h = cong (inspect F) (nf-TB β v A h) ∙ insp-B F β v

nf-T : ∀ τ → nf (T τ) ≡ TV (ev τ)
nf-T (sbase b)  = refl
nf-T (τ ⇒ˢ σ)   = cong₂ (narr 𝟙) (nf-T τ) (nf-T σ)
nf-T (τ ×ˢ σ)   = cong₂ _n⊗_ (nf-T τ) (nf-T σ)
nf-T (τ +ˢ σ)   = cong₂ _n⊕_ (nf-T τ) (nf-T σ)
nf-T (nt₀ N)    = refl
nf-T (nt₁ N τ)  = cong (ncapp (inr (N , idx N (ev τ)))) (nf-TB (body N) (ev τ) (T τ) (nf-T τ))
nf-T (fam F τ)  = cong (inspect F) (nf-T τ) ∙ insp-V F (ev τ)

-- Two source types with one nominal value: the translations have one
-- normal form, so they are convertible.
value→nf : ∀ {τ σ} → ev τ ≡ ev σ → nf (T τ) ≡ nf (T σ)
value→nf {τ} {σ} p = nf-T τ ∙ cong TV p ∙ sym (nf-T σ)

nominal-nf : ∀ {τ σ} → Co nom τ σ → nf (T τ) ≡ nf (T σ)
nominal-nf γ = value→nf (nom-sound γ)

nominal-defeq : ∀ {τ σ} → Co nom τ σ → DefEq (T τ) (T σ)
nominal-defeq γ = nf→defEq (nominal-nf γ)

------------------------------------------------------------------------
-- The translation commutes with the instance of a body and with the
-- embedding of an erased type.

T-inst : ∀ β τ → T (inst β τ) ≡ TB β (T τ)
T-inst bvar        τ = refl
T-inst (bbase b)   τ = refl
T-inst (barr β γ)  τ = cong₂ (arr 𝟙) (T-inst β τ) (T-inst γ τ)
T-inst (bprod β γ) τ = cong₂ _⊗_ (T-inst β τ) (T-inst γ τ)
T-inst (bsum β γ)  τ = cong₂ _⊕_ (T-inst β τ) (T-inst γ τ)
T-inst (bfam F β)  τ = cong (papp F) (T-inst β τ)

T-embE : ∀ a → T (embE a) ≡ TE a
T-embE (ebase b)   = refl
T-embE (earr a b)  = cong₂ (arr 𝟙) (T-embE a) (T-embE b)
T-embE (eprod a b) = cong₂ _⊗_ (T-embE a) (T-embE b)
T-embE (esum a b)  = cong₂ _⊕_ (T-embE a) (T-embE b)

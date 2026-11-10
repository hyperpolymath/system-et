{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on coercions.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Soundness of the roles of the source calculus (Stage 3).
--
-- A coercion at the role r relates two types whose values are related
-- at r:
--   nom   the nominal values are equal;
--   rep   the erased types are equal;
--   ph    no condition.
-- The representational part needs the role check `WellRoled`.
open import Wager.FC.Signature

module Wager.FC.RoleSoundness (SS : SSig) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)

open import Wager.Grade.Finite using (false≢true)
open import Wager.Role.Role
open import Wager.Erased.Untyped using (ETy; ebase; earr; eprod; esum)
open import Wager.FC.Types SS
open import Wager.FC.Coercion SS

RelV : Role → VTy → VTy → Type
RelV ph  v w = Unit
RelV rep v w = erV v ≡ erV w
RelV nom v w = v ≡ w

-- A relation at a role gives the relation at each lower role.
RelV-anti : ∀ a b {v w} → leR a b ≡ true → RelV b v w → RelV a v w
RelV-anti ph  b   _ _ = tt
RelV-anti rep ph  p _ = ⊥.rec (false≢true p)
RelV-anti rep rep _ x = x
RelV-anti rep nom _ x = cong erV x
RelV-anti nom ph  p _ = ⊥.rec (false≢true p)
RelV-anti nom rep p _ = ⊥.rec (false≢true p)
RelV-anti nom nom _ x = x

private
  RelV-sym : ∀ r {v w} → RelV r v w → RelV r w v
  RelV-sym ph  _ = tt
  RelV-sym rep p = sym p
  RelV-sym nom p = sym p

  RelV-trans : ∀ r {u v w} → RelV r u v → RelV r v w → RelV r u w
  RelV-trans ph  _ _ = tt
  RelV-trans rep p q = p ∙ q
  RelV-trans nom p q = p ∙ q

  RelV-arr : ∀ r {a a' b b'} → RelV r a a' → RelV r b b' → RelV r (varr a b) (varr a' b')
  RelV-arr ph  _ _ = tt
  RelV-arr rep p q = cong₂ earr p q
  RelV-arr nom p q = cong₂ varr p q

  RelV-prod : ∀ r {a a' b b'} → RelV r a a' → RelV r b b' → RelV r (vprod a b) (vprod a' b')
  RelV-prod ph  _ _ = tt
  RelV-prod rep p q = cong₂ eprod p q
  RelV-prod nom p q = cong₂ vprod p q

  RelV-sum : ∀ r {a a' b b'} → RelV r a a' → RelV r b b' → RelV r (vsum a b) (vsum a' b')
  RelV-sum ph  _ _ = tt
  RelV-sum rep p q = cong₂ esum p q
  RelV-sum nom p q = cong₂ vsum p q

  -- Three facts about the composition `nominal · _` of the lawful table.
  nomZ-l : ∀ a b → leR (mulZ nom a) (mulZ nom (maxR a b)) ≡ true
  nomZ-l ph  b   = refl
  nomZ-l rep ph  = refl
  nomZ-l rep rep = refl
  nomZ-l rep nom = refl
  nomZ-l nom b   = refl

  nomZ-r : ∀ a b → leR (mulZ nom b) (mulZ nom (maxR a b)) ≡ true
  nomZ-r ph  ph  = refl
  nomZ-r ph  rep = refl
  nomZ-r ph  nom = refl
  nomZ-r rep ph  = refl
  nomZ-r rep rep = refl
  nomZ-r rep nom = refl
  nomZ-r nom ph  = refl
  nomZ-r nom rep = refl
  nomZ-r nom nom = refl

  nomZ-idem : ∀ a → mulZ nom (mulZ nom a) ≡ mulZ nom a
  nomZ-idem ph  = refl
  nomZ-idem rep = refl
  nomZ-idem nom = refl

------------------------------------------------------------------------
-- A body respects the inferred role of its parameter.

-- The nominal value of a body: equal for two arguments that are related
-- at `nominal · (inferred role)`.
body-nom : ∀ β {v w} → RelV (mulZ nom (roleOf β)) v w → evB β v ≡ evB β w
body-nom bvar        p = p
body-nom (bbase b)   p = refl
body-nom (barr β γ)  p =
  cong₂ varr (body-nom β (RelV-anti _ _ (nomZ-l (roleOf β) (roleOf γ)) p))
             (body-nom γ (RelV-anti _ _ (nomZ-r (roleOf β) (roleOf γ)) p))
body-nom (bprod β γ) p =
  cong₂ vprod (body-nom β (RelV-anti _ _ (nomZ-l (roleOf β) (roleOf γ)) p))
              (body-nom γ (RelV-anti _ _ (nomZ-r (roleOf β) (roleOf γ)) p))
body-nom (bsum β γ)  p =
  cong₂ vsum (body-nom β (RelV-anti _ _ (nomZ-l (roleOf β) (roleOf γ)) p))
             (body-nom γ (RelV-anti _ _ (nomZ-r (roleOf β) (roleOf γ)) p))
body-nom (bfam F β) {v} {w} p =
  cong (λ x → vbase (applyF F x))
       (body-nom β (subst (λ r → RelV r v w) (nomZ-idem (roleOf β)) p))

-- The erased type of a body: equal for two arguments that are related
-- at the inferred role.
body-rep : ∀ β {v w} → RelV (roleOf β) v w → erB β v (erV v) ≡ erB β w (erV w)
body-rep bvar        p = p
body-rep (bbase b)   p = refl
body-rep (barr β γ)  p =
  cong₂ earr (body-rep β (RelV-anti _ _ (max-upper-l (roleOf β) (roleOf γ)) p))
             (body-rep γ (RelV-anti _ _ (max-upper-r (roleOf β) (roleOf γ)) p))
body-rep (bprod β γ) p =
  cong₂ eprod (body-rep β (RelV-anti _ _ (max-upper-l (roleOf β) (roleOf γ)) p))
              (body-rep γ (RelV-anti _ _ (max-upper-r (roleOf β) (roleOf γ)) p))
body-rep (bsum β γ)  p =
  cong₂ esum (body-rep β (RelV-anti _ _ (max-upper-l (roleOf β) (roleOf γ)) p))
             (body-rep γ (RelV-anti _ _ (max-upper-r (roleOf β) (roleOf γ)) p))
body-rep (bfam F β)  p = cong (λ x → ebase (applyF F x)) (body-nom β p)

------------------------------------------------------------------------
-- Instances of a body, and the embedding of erased types.

ev-inst : ∀ β τ → ev (inst β τ) ≡ evB β (ev τ)
ev-inst bvar        τ = refl
ev-inst (bbase b)   τ = refl
ev-inst (barr β γ)  τ = cong₂ varr (ev-inst β τ) (ev-inst γ τ)
ev-inst (bprod β γ) τ = cong₂ vprod (ev-inst β τ) (ev-inst γ τ)
ev-inst (bsum β γ)  τ = cong₂ vsum (ev-inst β τ) (ev-inst γ τ)
ev-inst (bfam F β)  τ = cong (λ x → vbase (applyF F x)) (ev-inst β τ)

er-inst : ∀ β τ → er (inst β τ) ≡ erB β (ev τ) (er τ)
er-inst bvar        τ = refl
er-inst (bbase b)   τ = refl
er-inst (barr β γ)  τ = cong₂ earr (er-inst β τ) (er-inst γ τ)
er-inst (bprod β γ) τ = cong₂ eprod (er-inst β τ) (er-inst γ τ)
er-inst (bsum β γ)  τ = cong₂ esum (er-inst β τ) (er-inst γ τ)
er-inst (bfam F β)  τ = cong (λ x → ebase (applyF F x)) (ev-inst β τ)

er-embE : ∀ a → er (embE a) ≡ a
er-embE (ebase b)   = refl
er-embE (earr a b)  = cong₂ earr (er-embE a) (er-embE b)
er-embE (eprod a b) = cong₂ eprod (er-embE a) (er-embE b)
er-embE (esum a b)  = cong₂ esum (er-embE a) (er-embE b)

ev-resS : ∀ x τ → ev (resS x τ) ≡ vbase (resB x (λ G → applyF G (ev τ)))
ev-resS (inl b) τ = refl
ev-resS (inr G) τ = refl

------------------------------------------------------------------------
-- Soundness of nominal coercions. No role check is needed.

nom-sound : ∀ {τ σ} → Co nom τ σ → ev τ ≡ ev σ
nom-sound c-refl          = refl
nom-sound (c-sym γ)       = sym (nom-sound γ)
nom-sound (c-trans γ δ)   = nom-sound γ ∙ nom-sound δ
nom-sound (c-arr γ δ)     = cong₂ varr (nom-sound γ) (nom-sound δ)
nom-sound (c-prod γ δ)    = cong₂ vprod (nom-sound γ) (nom-sound δ)
nom-sound (c-sum γ δ)     = cong₂ vsum (nom-sound γ) (nom-sound δ)
nom-sound (c-nt₁ N γ)     = cong (vnt₁ N) (nom-sound γ)
nom-sound (c-fam F γ)     = cong (λ x → vbase (applyF F x)) (nom-sound γ)
nom-sound (c-fbase F b)   = refl
nom-sound (c-fnt₀ F N)    = refl
nom-sound (c-fnt₁ F N τ)  = sym (ev-resS (fNt₁ F N) τ)
nom-sound (c-farr F τ σ)  = refl
nom-sound (c-fprod F τ σ) = refl
nom-sound (c-fsum F τ σ)  = refl

------------------------------------------------------------------------
-- Soundness of coercions at each role, for a signature that passes the
-- role check.

module _ (wr : WellRoled) where

  private
    -- The congruence rule for a newtype. The representational case is
    -- the one place that uses the role check.
    nt-sound : ∀ r N {v w} → RelV (mulG r (role N)) v w → RelV r (vnt₁ N v) (vnt₁ N w)
    nt-sound ph  N p = tt
    nt-sound rep N p = body-rep (body N) (RelV-anti _ _ (wr N) p)
    nt-sound nom N p = cong (vnt₁ N) p

  sound : ∀ {r τ σ} → Co r τ σ → RelV r (ev τ) (ev σ)
  sound c-refl                = refl
  sound (c-sym {r = r} γ)     = RelV-sym r (sound γ)
  sound (c-trans {r = r} γ δ) = RelV-trans r (sound γ) (sound δ)
  sound (c-sub γ)             = cong erV (sound γ)
  sound c-ph                  = tt
  sound (c-arr {r = r} γ δ)   = RelV-arr r (sound γ) (sound δ)
  sound (c-prod {r = r} γ δ)  = RelV-prod r (sound γ) (sound δ)
  sound (c-sum {r = r} γ δ)   = RelV-sum r (sound γ) (sound δ)
  sound (c-nt₁ {r = r} N γ)   = nt-sound r N (sound γ)
  sound (c-fam F γ)           = cong (λ x → vbase (applyF F x)) (sound γ)
  sound (c-ax₀ N)             = sym (er-embE (rep₀ N))
  sound (c-ax₁ N τ)           = sym (er-inst (body N) τ)
  sound (c-fbase F b)         = refl
  sound (c-fnt₀ F N)          = refl
  sound (c-fnt₁ F N τ)        = sym (ev-resS (fNt₁ F N) τ)
  sound (c-farr F τ σ)        = refl
  sound (c-fprod F τ σ)       = refl
  sound (c-fsum F τ σ)        = refl

  -- The headline form: a representational coercion relates two types
  -- with one erased type.
  rep-sound : ∀ {τ σ} → Co rep τ σ → er τ ≡ er σ
  rep-sound = sound

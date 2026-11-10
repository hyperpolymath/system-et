{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded syntax.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Laws of renaming and substitution on L1 syntax.
-- Each law is a path. Paths between renamings or substitutions come
-- from function extensionality.
open import Wager.L1.Signature

module Wager.L1.SyntaxLemmas (S : Sig) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)

open import Wager.L1.Syntax S

private
  variable
    Γ Δ Θ Ξ : Ctx
    k j     : Kind

-- Pointwise equality of renamings / substitutions gives a path.
renExt : {r r' : Ren Δ Γ} → (∀ k x → r k x ≡ r' k x) → r ≡ r'
renExt h = funExt λ k → funExt (h k)

subExt : {σ σ' : TySub Δ Γ} → (∀ k x → σ k x ≡ σ' k x) → σ ≡ σ'
subExt h = funExt λ k → funExt (h k)

------------------------------------------------------------------------
-- Renaming is a functor.

ext-id : ∀ k (x : Var (j ∷ Γ) k) → ext idᵣ k x ≡ x
ext-id k vz     = refl
ext-id k (vs x) = refl

ren-id : (t : Ty Γ k) → ren idᵣ t ≡ t
ren-id (var x)     = refl
ren-id (base b)    = refl
ren-id (capp c a)  = cong (capp c) (ren-id a)
ren-id (papp p a)  = cong (papp p) (ren-id a)
ren-id (arr q a b) = cong₂ (arr q) (ren-id a) (ren-id b)
ren-id (a ⊗ b)     = cong₂ _⊗_ (ren-id a) (ren-id b)
ren-id (a ⊕ b)     = cong₂ _⊕_ (ren-id a) (ren-id b)
ren-id (lam b)     = cong lam (cong (λ r → ren r b) (renExt ext-id) ∙ ren-id b)
ren-id (app f a)   = cong₂ app (ren-id f) (ren-id a)

ext-comp : (r' : Ren Θ Δ) (r : Ren Δ Γ) → ∀ k (x : Var (j ∷ Γ) k) →
           ext r' k (ext r k x) ≡ ext (r' ∘ᵣ r) k x
ext-comp r' r k vz     = refl
ext-comp r' r k (vs x) = refl

ren-comp : (r' : Ren Θ Δ) (r : Ren Δ Γ) (t : Ty Γ k) →
           ren r' (ren r t) ≡ ren (r' ∘ᵣ r) t
ren-comp r' r (var x)     = refl
ren-comp r' r (base b)    = refl
ren-comp r' r (capp c a)  = cong (capp c) (ren-comp r' r a)
ren-comp r' r (papp p a)  = cong (papp p) (ren-comp r' r a)
ren-comp r' r (arr q a b) = cong₂ (arr q) (ren-comp r' r a) (ren-comp r' r b)
ren-comp r' r (a ⊗ b)     = cong₂ _⊗_ (ren-comp r' r a) (ren-comp r' r b)
ren-comp r' r (a ⊕ b)     = cong₂ _⊕_ (ren-comp r' r a) (ren-comp r' r b)
ren-comp r' r (lam b)     =
  cong lam (ren-comp (ext r') (ext r) b
            ∙ cong (λ s → ren s b) (renExt (ext-comp r' r)))
ren-comp r' r (app f a)   = cong₂ app (ren-comp r' r f) (ren-comp r' r a)

------------------------------------------------------------------------
-- Substitution: identity and fusion with renaming.

exts-ids : ∀ k (x : Var (j ∷ Γ) k) → exts ids k x ≡ ids k x
exts-ids k vz     = refl
exts-ids k (vs x) = refl

sub-id : (t : Ty Γ k) → sub ids t ≡ t
sub-id (var x)     = refl
sub-id (base b)    = refl
sub-id (capp c a)  = cong (capp c) (sub-id a)
sub-id (papp p a)  = cong (papp p) (sub-id a)
sub-id (arr q a b) = cong₂ (arr q) (sub-id a) (sub-id b)
sub-id (a ⊗ b)     = cong₂ _⊗_ (sub-id a) (sub-id b)
sub-id (a ⊕ b)     = cong₂ _⊕_ (sub-id a) (sub-id b)
sub-id (lam b)     = cong lam (cong (λ s → sub s b) (subExt exts-ids) ∙ sub-id b)
sub-id (app f a)   = cong₂ app (sub-id f) (sub-id a)

exts-ext : (σ : TySub Θ Δ) (r : Ren Δ Γ) → ∀ k (x : Var (j ∷ Γ) k) →
           exts σ k (ext r k x) ≡ exts (λ k y → σ k (r k y)) k x
exts-ext σ r k vz     = refl
exts-ext σ r k (vs x) = refl

-- sub after ren
sub-ren : (σ : TySub Θ Δ) (r : Ren Δ Γ) (t : Ty Γ k) →
          sub σ (ren r t) ≡ sub (λ k x → σ k (r k x)) t
sub-ren σ r (var x)     = refl
sub-ren σ r (base b)    = refl
sub-ren σ r (capp c a)  = cong (capp c) (sub-ren σ r a)
sub-ren σ r (papp p a)  = cong (papp p) (sub-ren σ r a)
sub-ren σ r (arr q a b) = cong₂ (arr q) (sub-ren σ r a) (sub-ren σ r b)
sub-ren σ r (a ⊗ b)     = cong₂ _⊗_ (sub-ren σ r a) (sub-ren σ r b)
sub-ren σ r (a ⊕ b)     = cong₂ _⊕_ (sub-ren σ r a) (sub-ren σ r b)
sub-ren σ r (lam b)     =
  cong lam (sub-ren (exts σ) (ext r) b
            ∙ cong (λ s → sub s b) (subExt (exts-ext σ r)))
sub-ren σ r (app f a)   = cong₂ app (sub-ren σ r f) (sub-ren σ r a)

ext-exts : (r : Ren Θ Δ) (σ : TySub Δ Γ) → ∀ k (x : Var (j ∷ Γ) k) →
           ren (ext r) (exts σ k x) ≡ exts (λ k y → ren r (σ k y)) k x
ext-exts r σ k vz     = refl
ext-exts r σ k (vs x) = ren-comp (ext r) wk (σ k x) ∙ sym (ren-comp wk r (σ k x))

-- ren after sub
ren-sub : (r : Ren Θ Δ) (σ : TySub Δ Γ) (t : Ty Γ k) →
          ren r (sub σ t) ≡ sub (λ k x → ren r (σ k x)) t
ren-sub r σ (var x)     = refl
ren-sub r σ (base b)    = refl
ren-sub r σ (capp c a)  = cong (capp c) (ren-sub r σ a)
ren-sub r σ (papp p a)  = cong (papp p) (ren-sub r σ a)
ren-sub r σ (arr q a b) = cong₂ (arr q) (ren-sub r σ a) (ren-sub r σ b)
ren-sub r σ (a ⊗ b)     = cong₂ _⊗_ (ren-sub r σ a) (ren-sub r σ b)
ren-sub r σ (a ⊕ b)     = cong₂ _⊕_ (ren-sub r σ a) (ren-sub r σ b)
ren-sub r σ (lam b)     =
  cong lam (ren-sub (ext r) (exts σ) b
            ∙ cong (λ s → sub s b) (subExt (ext-exts r σ)))
ren-sub r σ (app f a)   = cong₂ app (ren-sub r σ f) (ren-sub r σ a)

exts-exts : (τ : TySub Θ Δ) (σ : TySub Δ Γ) → ∀ k (x : Var (j ∷ Γ) k) →
            sub (exts τ) (exts σ k x) ≡ exts (λ k y → sub τ (σ k y)) k x
exts-exts τ σ k vz     = refl
exts-exts τ σ k (vs x) = sub-ren (exts τ) wk (σ k x) ∙ sym (ren-sub wk τ (σ k x))

-- sub after sub
sub-sub : (τ : TySub Θ Δ) (σ : TySub Δ Γ) (t : Ty Γ k) →
          sub τ (sub σ t) ≡ sub (λ k x → sub τ (σ k x)) t
sub-sub τ σ (var x)     = refl
sub-sub τ σ (base b)    = refl
sub-sub τ σ (capp c a)  = cong (capp c) (sub-sub τ σ a)
sub-sub τ σ (papp p a)  = cong (papp p) (sub-sub τ σ a)
sub-sub τ σ (arr q a b) = cong₂ (arr q) (sub-sub τ σ a) (sub-sub τ σ b)
sub-sub τ σ (a ⊗ b)     = cong₂ _⊗_ (sub-sub τ σ a) (sub-sub τ σ b)
sub-sub τ σ (a ⊕ b)     = cong₂ _⊕_ (sub-sub τ σ a) (sub-sub τ σ b)
sub-sub τ σ (lam b)     =
  cong lam (sub-sub (exts τ) (exts σ) b
            ∙ cong (λ s → sub s b) (subExt (exts-exts τ σ)))
sub-sub τ σ (app f a)   = cong₂ app (sub-sub τ σ f) (sub-sub τ σ a)

exts-var : (r : Ren Δ Γ) → ∀ k (x : Var (j ∷ Γ) k) →
           exts (λ k y → var (r k y)) k x ≡ var (ext r k x)
exts-var r k vz     = refl
exts-var r k (vs x) = refl

-- A substitution of variables is a renaming.
sub-var : (r : Ren Δ Γ) (t : Ty Γ k) → sub (λ k x → var (r k x)) t ≡ ren r t
sub-var r (var x)     = refl
sub-var r (base b)    = refl
sub-var r (capp c a)  = cong (capp c) (sub-var r a)
sub-var r (papp p a)  = cong (papp p) (sub-var r a)
sub-var r (arr q a b) = cong₂ (arr q) (sub-var r a) (sub-var r b)
sub-var r (a ⊗ b)     = cong₂ _⊗_ (sub-var r a) (sub-var r b)
sub-var r (a ⊕ b)     = cong₂ _⊕_ (sub-var r a) (sub-var r b)
sub-var r (lam b)     =
  cong lam (cong (λ s → sub s b) (subExt (exts-var r)) ∙ sub-var (ext r) b)
sub-var r (app f a)   = cong₂ app (sub-var r f) (sub-var r a)

------------------------------------------------------------------------
-- Consequences used by the conversion proofs.

private
  β-ren-pt : (r : Ren Δ Γ) (u : Ty Γ j) → ∀ k (x : Var (j ∷ Γ) k) →
             ren r ((u ∷ₛ ids) k x) ≡ (ren r u ∷ₛ ids) k (ext r k x)
  β-ren-pt r u k vz     = refl
  β-ren-pt r u k (vs x) = refl

-- Renaming commutes with β-substitution.
ren-β : (r : Ren Δ Γ) (b : Ty (j ∷ Γ) k) (u : Ty Γ j) →
        ren r (b [ u ]) ≡ ren (ext r) b [ ren r u ]
ren-β r b u =
  ren-sub r (u ∷ₛ ids) b
  ∙ cong (λ s → sub s b) (subExt (β-ren-pt r u))
  ∙ sym (sub-ren (ren r u ∷ₛ ids) (ext r) b)

private
  β-sub-pt : (r : Ren Δ Γ) (σ : TySub Γ Θ) (u : Ty Δ j) → ∀ k (x : Var (j ∷ Θ) k) →
             sub (u ∷ₛ ids) (ren (ext r) (exts σ k x)) ≡ (u ∷ₛ (λ k y → ren r (σ k y))) k x
  β-sub-pt r σ u k vz     = refl
  β-sub-pt r σ u k (vs x) =
    cong (sub (u ∷ₛ ids)) (ren-comp (ext r) wk (σ k x))
    ∙ sub-ren (u ∷ₛ ids) (ext r ∘ᵣ wk) (σ k x)
    ∙ sub-var r (σ k x)

-- A β-step on a renamed, substituted body is one substitution.
β-sub : (r : Ren Δ Γ) (σ : TySub Γ Θ) (b : Ty (j ∷ Θ) k) (u : Ty Δ j) →
        ren (ext r) (sub (exts σ) b) [ u ] ≡ sub (u ∷ₛ (λ k y → ren r (σ k y))) b
β-sub r σ b u =
  cong (sub (u ∷ₛ ids)) (ren-sub (ext r) (exts σ) b)
  ∙ sub-sub (u ∷ₛ ids) (λ k x → ren (ext r) (exts σ k x)) b
  ∙ cong (λ s → sub s b) (subExt (β-sub-pt r σ u))

ren-resTy : (r : Ren Δ Γ) (x : Base ⊎ Prim) (A : Ty Γ ★) →
            ren r (resTy x A) ≡ resTy x (ren r A)
ren-resTy r (inl b) A = refl
ren-resTy r (inr q) A = refl

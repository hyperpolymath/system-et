{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded syntax.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Soundness of the normalizer: each term converts to its normal form
-- (the other half of ET-2 for this language).
--
-- The proof uses a Kripke logical relation `Rel` between terms and
-- values. No η-law is needed, because a value of arrow kind carries
-- its own normal form.
open import Wager.L1.Signature

module Wager.L1.Soundness (S : Sig) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)

open import Wager.L1.Syntax S
open import Wager.L1.SyntaxLemmas S
open import Wager.L1.Conversion S
open import Wager.L1.Normal S
open import Wager.L1.Eval S

private
  variable
    Γ Δ Θ : Ctx
    k j   : Kind
    g     : KG

Rel : ∀ k → Ty Γ k → Val Γ k → Type
Rel ★ t v = DefEq t (embNf v)
Rel {Γ} (k ⇒[ g ] j) t (n , f) =
    DefEq t (embNf n)
  × ((Δ : Ctx) (r : Ren Δ Γ) (u : Ty Δ k) (a : Val Δ k) → Rel k u a →
       Rel j (app {g = g} (ren r t) u) (f Δ r a))

-- The relation is closed under conversion of the term.
Rel-conv : ∀ k {t t' : Ty Γ k} {v : Val Γ k} → DefEq t' t → Rel k t v → Rel k t' v
Rel-conv ★            d e       = d-trans d e
Rel-conv (k ⇒[ g ] j) d (p , h) =
    d-trans d p
  , (λ Δ r u a ua → Rel-conv j (d-app (DefEq-ren r d) d-refl) (h Δ r u a ua))

Rel-reify : ∀ k {t : Ty Γ k} {v : Val Γ k} → Rel k t v → DefEq t (embNf (reify k v))
Rel-reify ★            e = e
Rel-reify (k ⇒[ g ] j) e = fst e

Rel-ren : ∀ k (r : Ren Δ Γ) {t : Ty Γ k} {v : Val Γ k} → Rel k t v →
          Rel k (ren r t) (renVal k r v)
Rel-ren ★            r {v = v} e = d-trans (DefEq-ren r e) (≡→DefEq (sym (embNf-ren r v)))
Rel-ren (k ⇒[ g ] j) r {t = t} {v = n , f} (p , h) =
    d-trans (DefEq-ren r p) (≡→DefEq (sym (embNf-ren r n)))
  , (λ Δ r₁ u a ua →
       subst (λ z → Rel j (app z u) (f Δ (r₁ ∘ᵣ r) a)) (sym (ren-comp r₁ r t))
             (h Δ (r₁ ∘ᵣ r) u a ua))

Rel-reflect : ∀ k {t : Ty Γ k} {n : Ne Γ k} → DefEq t (embNe n) → Rel k t (reflect k n)
Rel-reflect ★            d = d
Rel-reflect (k ⇒[ g ] j) {n = n} d =
    d
  , (λ Δ r u a ua →
       Rel-reflect j
         (d-app (d-trans (DefEq-ren r d) (≡→DefEq (sym (embNe-ren r n))))
                (Rel-reify k ua)))

private
  res-sound : (x : Base ⊎ Prim) (v : Nf Γ ★) →
              (∀ q → DefEq (papp q (embNf v)) (embNf (inspect q v))) →
              DefEq (resTy x (embNf v)) (embNf (resNf x (λ q → inspect q v)))
  res-sound (inl b) v h = d-refl
  res-sound (inr q) v h = h q

-- A primitive application converts to the result of `inspect`.
inspect-sound : (p : Prim) (v : Nf Γ ★) → DefEq (papp p (embNf v)) (embNf (inspect p v))
inspect-sound p (ne n)       = d-refl
inspect-sound p (nbase b)    = δ-base p b
inspect-sound p (ncapp c v)  =
  d-trans (δ-capp p c (embNf v)) (res-sound (onCon p c) v (λ q → inspect-sound q v))
inspect-sound p (narr q a b) = δ-arr p q (embNf a) (embNf b)
inspect-sound p (a n⊗ b)     = δ-prod p (embNf a) (embNf b)
inspect-sound p (a n⊕ b)     = δ-sum p (embNf a) (embNf b)

SubRel : TySub Δ Γ → Env Δ Γ → Type
SubRel {Δ} {Γ} σ ρ = ∀ k (x : Var Γ k) → Rel k (σ k x) (ρ k x)

subRel-ext : {σ : TySub Δ Γ} {ρ : Env Δ Γ} → SubRel σ ρ → SubRel (exts {j = j} σ) (extEnv ρ)
subRel-ext {j = j} s k vz     = Rel-reflect j d-refl
subRel-ext         s k (vs x) = Rel-ren k wk (s k x)

subRel-cons : {σ : TySub Δ Γ} {ρ : Env Δ Γ} (r : Ren Θ Δ) {u : Ty Θ j} {a : Val Θ j} →
              SubRel σ ρ → Rel j u a →
              SubRel (u ∷ₛ (λ k y → ren r (σ k y))) (renEnv r ρ ,, a)
subRel-cons r s ua k vz     = ua
subRel-cons r s ua k (vs x) = Rel-ren k r (s k x)

-- The fundamental lemma.
fund : (t : Ty Γ k) {σ : TySub Δ Γ} {ρ : Env Δ Γ} → SubRel σ ρ → Rel k (sub σ t) (eval t ρ)
fund (var x)     s = s _ x
fund (base b)    s = d-refl
fund (capp c a)  s = d-capp (fund a s)
fund (papp p a) {ρ = ρ} s = d-trans (d-papp (fund a s)) (inspect-sound p (eval a ρ))
fund (arr q a b) s = d-arr (fund a s) (fund b s)
fund (a ⊗ b)     s = d-prod (fund a s) (fund b s)
fund (a ⊕ b)     s = d-sum (fund a s) (fund b s)
fund (lam {j = j} b) {σ = σ} s =
    d-lam (Rel-reify j (fund b (subRel-ext s)))
  , (λ Δ r u a ua →
       Rel-conv j (d-trans (d-beta (ren (ext r) (sub (exts σ) b)) u)
                           (≡→DefEq (β-sub r σ b u)))
                  (fund b (subRel-cons r s ua)))
fund (app {j = j} f a) {σ = σ} {ρ = ρ} s =
  subst (λ z → Rel j (app z (sub σ a)) (snd (eval f ρ) _ idᵣ (eval a ρ)))
        (ren-id (sub σ f))
        (snd (fund f s) _ idᵣ (sub σ a) (eval a ρ) (fund a s))

idRel : SubRel (ids {Γ}) idEnv
idRel k x = Rel-reflect k d-refl

-- Each term converts to its normal form.
soundness : (t : Ty Γ k) → DefEq t (embNf (nf t))
soundness {k = k} t =
  subst (λ z → DefEq z (embNf (nf t))) (sub-id t) (Rel-reify k (fund t idRel))

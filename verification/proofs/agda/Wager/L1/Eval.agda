{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded syntax.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The L1 normalizer `nf` (ET-1 evidence for this language).
--
-- The Lean development uses hereditary substitution. This file uses
-- evaluation into a Kripke model (DESIGN-CHOICES.adoc, DC-1.2). Each
-- function here is structurally recursive, so Agda accepts `nf` as
-- total with no termination pragma. That is the Totality Gate for
-- this language.
--
-- A value of arrow kind is a pair: its normal form, and its action
-- on arguments in each extended context. The pair gives β-normal
-- forms with no η-expansion.
open import Wager.L1.Signature

module Wager.L1.Eval (S : Sig) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)

open import Wager.L1.Syntax S
open import Wager.L1.Normal S

private
  variable
    Γ Δ Θ : Ctx
    k j   : Kind
    g     : KG

Val : Ctx → Kind → Type
Val Γ ★              = Nf Γ ★
Val Γ (k ⇒[ g ] j)   = Nf Γ (k ⇒[ g ] j) × (∀ Δ → Ren Δ Γ → Val Δ k → Val Δ j)

reify : ∀ k → Val Γ k → Nf Γ k
reify ★            v = v
reify (k ⇒[ g ] j) v = fst v

reflect : ∀ k → Ne Γ k → Val Γ k
reflect ★            n = ne n
reflect (k ⇒[ g ] j) n = ne n , λ Δ r v → reflect j (napp (renNe r n) (reify k v))

renVal : ∀ k → Ren Δ Γ → Val Γ k → Val Δ k
renVal ★            r v       = renNf r v
renVal (k ⇒[ g ] j) r (n , f) = renNf r n , λ Θ r' v → f Θ (r' ∘ᵣ r) v

-- Environments.
Env : Ctx → Ctx → Type
Env Δ Γ = ∀ k → Var Γ k → Val Δ k

renEnv : Ren Θ Δ → Env Δ Γ → Env Θ Γ
renEnv r ρ k x = renVal k r (ρ k x)

infixl 5 _,,_
_,,_ : Env Δ Γ → Val Δ j → Env Δ (j ∷ Γ)
(ρ ,, v) k vz     = v
(ρ ,, v) k (vs x) = ρ k x

extEnv : Env Δ Γ → Env (j ∷ Δ) (j ∷ Γ)
extEnv {j = j} ρ = renEnv wk ρ ,, reflect j (nvar vz)

eval : Ty Γ k → Env Δ Γ → Val Δ k
eval (var x)     ρ = ρ _ x
eval (base b)    ρ = nbase b
eval (capp c a)  ρ = ncapp c (eval a ρ)
eval (papp p a)  ρ = inspect p (eval a ρ)
eval (arr q a b) ρ = narr q (eval a ρ) (eval b ρ)
eval (a ⊗ b)     ρ = eval a ρ n⊗ eval b ρ
eval (a ⊕ b)     ρ = eval a ρ n⊕ eval b ρ
eval (lam {j = j} b) ρ =
  nlam (reify j (eval b (extEnv ρ))) , λ Θ r v → eval b (renEnv r ρ ,, v)
eval (app f a)   ρ = snd (eval f ρ) _ idᵣ (eval a ρ)

idEnv : Env Γ Γ
idEnv k x = reflect k (nvar x)

-- The normalizer.
nf : Ty Γ k → Nf Γ k
nf {k = k} t = reify k (eval t idEnv)

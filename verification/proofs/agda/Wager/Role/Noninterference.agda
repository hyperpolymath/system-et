{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinding derivations.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Noninterference for roles (the proof of T2), for a composition
-- table T and a signature that respects its declared grades.
--
-- The proof is a logical relation on closed values, indexed by the
-- role of an observer. It uses three properties of the table
-- (associativity, the right unit, monotonicity) and one property of
-- the role order that is not a grade law: a ≤ a + b.
-- It does not use `a · 𝟘 = 𝟘`.
open import Wager.Role.Signature
open import Wager.Role.Table

module Wager.Role.Noninterference (RS : RoleSig) (T : RoleTable) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (_×_)

open import Wager.Grade.Finite using (false≢true)
open import Wager.Role.Role
open RoleTable T
open import Wager.L1.Syntax (toSig RS)
open import Wager.L1.Normal (toSig RS)
open import Wager.L1.Eval (toSig RS)
open import Wager.L1.Completeness (toSig RS) using (renVal-id)
open import Wager.L1.Kinding (toSig RS) (tableOps T)
open import Wager.Role.RepEq RS
open import Wager.Role.Validity RS mul

private
  variable
    Γ   : Ctx
    k j : Kind

------------------------------------------------------------------------
-- The observers.

R★-refl : ∀ ρ (v : CNf) → R★ ρ v v
R★-refl ph  v = tt
R★-refl rep v = ≈-refl
R★-refl nom v = refl

-- A weaker observer tells fewer types apart.
R★-anti : ∀ ρ ρ' {v w : CNf} → leR ρ ρ' ≡ true → R★ ρ' v w → R★ ρ v w
R★-anti ph  ρ'  le h = tt
R★-anti rep ph  le h = ⊥.rec (false≢true le)
R★-anti rep rep le h = h
R★-anti rep nom le h = ≡→≈ h
R★-anti nom ph  le h = ⊥.rec (false≢true le)
R★-anti nom rep le h = ⊥.rec (false≢true le)
R★-anti nom nom le h = h

R★-arr : ∀ ρ q {a a' b b' : CNf} → R★ ρ a a' → R★ ρ b b' →
         R★ ρ (narr q a b) (narr q a' b')
R★-arr ph  q h h' = tt
R★-arr rep q h h' = ≈-arr q h h'
R★-arr nom q h h' = cong₂ (narr q) h h'

R★-prod : ∀ ρ {a a' b b' : CNf} → R★ ρ a a' → R★ ρ b b' → R★ ρ (a n⊗ b) (a' n⊗ b')
R★-prod ph  h h' = tt
R★-prod rep h h' = ≈-prod h h'
R★-prod nom h h' = cong₂ _n⊗_ h h'

R★-sum : ∀ ρ {a a' b b' : CNf} → R★ ρ a a' → R★ ρ b b' → R★ ρ (a n⊕ b) (a' n⊕ b')
R★-sum ph  h h' = tt
R★-sum rep h h' = ≈-sum h h'
R★-sum nom h h' = cong₂ _n⊕_ h h'

------------------------------------------------------------------------
-- The logical relation on closed values.

LR : Role → ∀ k → Val [] k → Val [] k → Type
LR ρ ★            v w = R★ ρ v w
LR ρ (k ⇒[ g ] j) F G =
  ∀ ρ₁ → leR ρ₁ ρ ≡ true → (a a' : Val [] k) → LR (mul ρ₁ g) k a a' →
  LR ρ₁ j (snd F [] idᵣ a) (snd G [] idᵣ a')

LR-anti : ∀ k ρ ρ' {v w : Val [] k} → leR ρ ρ' ≡ true → LR ρ' k v w → LR ρ k v w
LR-anti ★            ρ ρ' le h = R★-anti ρ ρ' le h
LR-anti (k ⇒[ g ] j) ρ ρ' le h =
  λ ρ₁ le₁ a a' ha → h ρ₁ (leR-trans ρ₁ ρ ρ' le₁ le) a a' ha

-- Two environments that the observer cannot tell apart, variable by
-- variable, at the grade of each variable.
EnvLR : Role → KUsage Γ → Env [] Γ → Env [] Γ → Type
EnvLR {Γ} ρ γ η η' = ∀ k (x : Var Γ k) → LR (mul ρ (γ k x)) k (η k x) (η' k x)

private
  mul-mono-r : ∀ ρ a b → leR a b ≡ true → leR (mul ρ a) (mul ρ b) ≡ true
  mul-mono-r ρ a b le = mul-mono ρ ρ a b (leR-refl ρ) le

  mul-mono-l : ∀ ρ₁ ρ g → leR ρ₁ ρ ≡ true → leR (mul ρ₁ g) (mul ρ g) ≡ true
  mul-mono-l ρ₁ ρ g le = mul-mono ρ₁ ρ g g le (leR-refl g)

  unit-self : (x : Var Γ k) → unitᵏ x k x ≡ rep
  unit-self vz     = refl
  unit-self (vs x) = unit-self x

  lam-env : ∀ {g : Role} {γ : KUsage Γ} {η η' : Env [] Γ} (ρ ρ₁ : Role) →
            leR ρ₁ ρ ≡ true → EnvLR ρ γ η η' →
            {a a' : Val [] j} → LR (mul ρ₁ g) j a a' →
            EnvLR ρ₁ (γ ▹ᵏ g) (renEnv idᵣ η ,, a) (renEnv idᵣ η' ,, a')
  lam-env ρ ρ₁ le e ha k vz     = ha
  lam-env {γ = γ} {η} {η'} ρ ρ₁ le e ha k (vs x) =
    subst2 (LR (mul ρ₁ (γ k x)) k)
           (sym (renVal-id k (η k x))) (sym (renVal-id k (η' k x)))
           (LR-anti k _ _ (mul-mono-l ρ₁ ρ (γ k x) le) (e k x))

------------------------------------------------------------------------
-- The fundamental lemma, for a signature that respects its grades.

module _ (V : Valid) where
  open Valid V

  fund : {γ : KUsage Γ} {t : Ty Γ k} → γ ⊢ᵏ t →
         ∀ ρ {η η' : Env [] Γ} → EnvLR ρ γ η η' → LR ρ k (eval t η) (eval t η')
  fund {k = k} (k-var x) ρ {η} {η'} e =
    subst (λ r → LR r k (η k x) (η' k x)) (cong (mul ρ) (unit-self x) ∙ mul-one ρ) (e k x)
  fund (k-base b) ρ e = R★-refl ρ (nbase b)
  fund (k-capp {γ = γ} c d) ρ {η} {η'} e =
    cvalid c ρ
      (fund d (mul ρ (cgrade c))
         (λ k x → subst (λ r → LR r k (η k x) (η' k x))
                        (sym (mul-assoc ρ (cgrade c) (γ k x))) (e k x)))
  fund (k-papp {γ = γ} p d) ρ {η} {η'} e =
    pvalid p ρ
      (fund d (mul ρ (pgrade p))
         (λ k x → subst (λ r → LR r k (η k x) (η' k x))
                        (sym (mul-assoc ρ (pgrade p) (γ k x))) (e k x)))
  fund (k-arr {γ = γ} {δ = δ} {q = q} d d') ρ e =
    R★-arr ρ q
      (fund d  ρ (λ k x → LR-anti k _ _ (mul-mono-r ρ _ _ (max-upper-l (γ k x) (δ k x))) (e k x)))
      (fund d' ρ (λ k x → LR-anti k _ _ (mul-mono-r ρ _ _ (max-upper-r (γ k x) (δ k x))) (e k x)))
  fund (k-prod {γ = γ} {δ = δ} d d') ρ e =
    R★-prod ρ
      (fund d  ρ (λ k x → LR-anti k _ _ (mul-mono-r ρ _ _ (max-upper-l (γ k x) (δ k x))) (e k x)))
      (fund d' ρ (λ k x → LR-anti k _ _ (mul-mono-r ρ _ _ (max-upper-r (γ k x) (δ k x))) (e k x)))
  fund (k-sum {γ = γ} {δ = δ} d d') ρ e =
    R★-sum ρ
      (fund d  ρ (λ k x → LR-anti k _ _ (mul-mono-r ρ _ _ (max-upper-l (γ k x) (δ k x))) (e k x)))
      (fund d' ρ (λ k x → LR-anti k _ _ (mul-mono-r ρ _ _ (max-upper-r (γ k x) (δ k x))) (e k x)))
  fund (k-lam d) ρ e =
    λ ρ₁ le₁ a a' ha → fund d ρ₁ (lam-env ρ ρ₁ le₁ e ha)
  fund (k-app {k = k} {g = g} {γ = γ} {δ = δ} {a = a} d d') ρ {η} {η'} e =
    fund d ρ
      (λ k₁ x → LR-anti k₁ _ _
                  (mul-mono-r ρ _ _ (max-upper-l (γ k₁ x) (mul g (δ k₁ x)))) (e k₁ x))
      ρ (leR-refl ρ) (eval a η) (eval a η')
      (fund d' (mul ρ g)
         (λ k₁ x → subst (λ r → LR r k₁ (η k₁ x) (η' k₁ x))
                         (sym (mul-assoc ρ g (δ k₁ x)))
                         (LR-anti k₁ _ _
                            (mul-mono-r ρ _ _ (max-upper-r (γ k₁ x) (mul g (δ k₁ x))))
                            (e k₁ x))))
  fund (k-sub d le) ρ e =
    fund d ρ (λ k x → LR-anti k _ _ (mul-mono-r ρ _ _ (le k x)) (e k x))

  -- Noninterference for a closed type function of kind ★ ⇒[ r ] ★.
  noninterference :
    ∀ {r : Role} (F : Ty [] (★ ⇒[ r ] ★)) {γ : KUsage []} → γ ⊢ᵏ F →
    (ρ : Role) (A B : Ty [] ★) →
    R★ (mul ρ r) (nf A) (nf B) → R★ ρ (nf (app F A)) (nf (app F B))
  noninterference F d ρ A B h =
    fund d ρ {idEnv} {idEnv} (λ k ()) ρ (leR-refl ρ) (nf A) (nf B) h

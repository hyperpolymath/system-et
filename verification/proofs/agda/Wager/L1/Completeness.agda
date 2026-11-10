{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded syntax.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Completeness of the normalizer: convertible terms have equal
-- normal forms (one half of ET-2 for this language).
--
-- The proof uses a Kripke partial equivalence relation `SemEq` on
-- values. Two values of arrow kind are related when their normal
-- forms are equal, they send related arguments to related results,
-- and they commute with renaming.
open import Wager.L1.Signature

module Wager.L1.Completeness (S : Sig) where

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
    Γ Δ Θ Ξ : Ctx
    k j     : Kind
    g       : KG

------------------------------------------------------------------------
-- Path lemmas about values.

renVal-id : ∀ k (v : Val Γ k) → renVal k idᵣ v ≡ v
renVal-id ★            v       = renNf-id v
renVal-id (k ⇒[ g ] j) (n , f) = λ i → renNf-id n i , f

renVal-comp : ∀ k (r' : Ren Θ Δ) (r : Ren Δ Γ) (v : Val Γ k) →
              renVal k r' (renVal k r v) ≡ renVal k (r' ∘ᵣ r) v
renVal-comp ★            r' r v       = renNf-comp r' r v
renVal-comp (k ⇒[ g ] j) r' r (n , f) =
  λ i → renNf-comp r' r n i , λ Θ r'' v → f Θ (r'' ∘ᵣ r' ∘ᵣ r) v

reify-ren : ∀ k (r : Ren Δ Γ) (v : Val Γ k) → renNf r (reify k v) ≡ reify k (renVal k r v)
reify-ren ★            r v = refl
reify-ren (k ⇒[ g ] j) r v = refl

reflect-ren : ∀ k (r : Ren Δ Γ) (n : Ne Γ k) → renVal k r (reflect k n) ≡ reflect k (renNe r n)
reflect-ren ★            r n = refl
reflect-ren (k ⇒[ g ] j) r n =
  λ i → ne (renNe r n) , λ Θ r' v → reflect j (napp (renNe-comp r' r n (~ i)) (reify k v))

envExt : {ρ ρ' : Env Δ Γ} → (∀ k x → ρ k x ≡ ρ' k x) → ρ ≡ ρ'
envExt h = funExt λ k → funExt (h k)

------------------------------------------------------------------------
-- The Kripke partial equivalence relation.

SemEq : ∀ k → Val Γ k → Val Γ k → Type
SemEq ★ v v' = v ≡ v'
SemEq {Γ} (k ⇒[ g ] j) (n , f) (n' , f') =
    (n ≡ n')
  × ((Δ : Ctx) (r : Ren Δ Γ) (v v' : Val Δ k) → SemEq k v v' →
       SemEq j (f Δ r v) (f' Δ r v'))
  × ((Δ Θ : Ctx) (r : Ren Δ Γ) (r' : Ren Θ Δ) (v v' : Val Δ k) → SemEq k v v' →
       SemEq j (renVal j r' (f Δ r v)) (f' Θ (r' ∘ᵣ r) (renVal k r' v')))

≡≈ : ∀ k {v w w' : Val Γ k} → v ≡ w → SemEq k w w' → SemEq k v w'
≡≈ k {w' = w'} p e = subst (λ z → SemEq k z w') (sym p) e

≈≡ : ∀ k {v v' w : Val Γ k} → SemEq k v v' → v' ≡ w → SemEq k v w
≈≡ k {v = v} e p = subst (SemEq k v) p e

≈-ren : ∀ k (r : Ren Δ Γ) {v v' : Val Γ k} → SemEq k v v' →
        SemEq k (renVal k r v) (renVal k r v')
≈-ren ★            r e            = cong (renNf r) e
≈-ren (k ⇒[ g ] j) r (p , h , h') =
    cong (renNf r) p
  , (λ Δ r₁ v v' e → h Δ (r₁ ∘ᵣ r) v v' e)
  , (λ Δ Θ r₁ r' v v' e → h' Δ Θ (r₁ ∘ᵣ r) r' v v' e)

≈-sym   : ∀ k {v v' : Val Γ k} → SemEq k v v' → SemEq k v' v
≈-trans : ∀ k {v v' v'' : Val Γ k} → SemEq k v v' → SemEq k v' v'' → SemEq k v v''

≈-sym ★            e            = sym e
≈-sym (k ⇒[ g ] j) (p , h , h') =
    sym p
  , (λ Δ r v v' e → ≈-sym j (h Δ r v' v (≈-sym k e)))
  , (λ Δ Θ r r' v v' e →
       let e'  = ≈-sym k e
           e'' = ≈-trans k e' e
       in ≈-trans j (≈-sym j (≈-ren j r' (h Δ r v' v e')))
         (≈-trans j (h' Δ Θ r r' v' v' e'')
                    (≈-sym j (h Θ (r' ∘ᵣ r) (renVal k r' v') (renVal k r' v')
                                (≈-ren k r' e'')))))

≈-trans ★            e e'                       = e ∙ e'
≈-trans (k ⇒[ g ] j) (p , h , h') (q , i , i') =
    p ∙ q
  , (λ Δ r v v'' e →
       ≈-trans j (h Δ r v v'' e) (i Δ r v'' v'' (≈-trans k (≈-sym k e) e)))
  , (λ Δ Θ r r' v v'' e →
       ≈-trans j (h' Δ Θ r r' v v'' e)
                 (i Θ (r' ∘ᵣ r) (renVal k r' v'') (renVal k r' v'')
                    (≈-ren k r' (≈-trans k (≈-sym k e) e))))

≈-refl-l : ∀ k {v v' : Val Γ k} → SemEq k v v' → SemEq k v v
≈-refl-l k e = ≈-trans k e (≈-sym k e)

≈-refl-r : ∀ k {v v' : Val Γ k} → SemEq k v v' → SemEq k v' v'
≈-refl-r k e = ≈-trans k (≈-sym k e) e

≈-reify : ∀ k {v v' : Val Γ k} → SemEq k v v' → reify k v ≡ reify k v'
≈-reify ★            e = e
≈-reify (k ⇒[ g ] j) e = fst e

≈-reflect : ∀ k {n n' : Ne Γ k} → n ≡ n' → SemEq k (reflect k n) (reflect k n')
≈-reflect ★            p = cong ne p
≈-reflect (k ⇒[ g ] j) {n} {n'} p =
    cong ne p
  , (λ Δ r v v' e → ≈-reflect j (cong₂ napp (cong (renNe r) p) (≈-reify k e)))
  , (λ Δ Θ r r' v v' e →
       ≡≈ j (reflect-ren j r' (napp (renNe r n) (reify k v)))
            (≈-reflect j (cong₂ napp
               (renNe-comp r' r n ∙ cong (renNe (r' ∘ᵣ r)) p)
               (reify-ren k r' v ∙ ≈-reify k (≈-ren k r' e)))))

------------------------------------------------------------------------
-- Related environments.

EnvEq : Env Δ Γ → Env Δ Γ → Type
EnvEq {Δ} {Γ} ρ ρ' = ∀ k (x : Var Γ k) → SemEq k (ρ k x) (ρ' k x)

envEq-sym : {ρ ρ' : Env Δ Γ} → EnvEq ρ ρ' → EnvEq ρ' ρ
envEq-sym e k x = ≈-sym k (e k x)

envEq-refl-l : {ρ ρ' : Env Δ Γ} → EnvEq ρ ρ' → EnvEq ρ ρ
envEq-refl-l e k x = ≈-refl-l k (e k x)

envEq-refl-r : {ρ ρ' : Env Δ Γ} → EnvEq ρ ρ' → EnvEq ρ' ρ'
envEq-refl-r e k x = ≈-refl-r k (e k x)

envEq-ren : (r : Ren Θ Δ) {ρ ρ' : Env Δ Γ} → EnvEq ρ ρ' → EnvEq (renEnv r ρ) (renEnv r ρ')
envEq-ren r e k x = ≈-ren k r (e k x)

envEq-,, : {ρ ρ' : Env Δ Γ} {v v' : Val Δ j} → EnvEq ρ ρ' → SemEq j v v' →
           EnvEq (ρ ,, v) (ρ' ,, v')
envEq-,, e ev k vz     = ev
envEq-,, e ev k (vs x) = e k x

envEq-ext : {ρ ρ' : Env Δ Γ} → EnvEq ρ ρ' → EnvEq (extEnv {j = j} ρ) (extEnv ρ')
envEq-ext {j = j} e = envEq-,, (envEq-ren wk e) (≈-reflect j refl)

-- Pointwise paths between environments.
env-push : (r' : Ren Θ Δ) (r : Ren Δ Ξ) (ρ : Env Ξ Γ) (v : Val Δ j) → ∀ k x →
           renEnv r' (renEnv r ρ ,, v) k x ≡ (renEnv (r' ∘ᵣ r) ρ ,, renVal j r' v) k x
env-push r' r ρ v k vz     = refl
env-push r' r ρ v k (vs x) = renVal-comp k r' r (ρ k x)

env-split : (r' : Ren Θ Δ) (r : Ren Δ Ξ) (ρ : Env Ξ Γ) (v : Val Θ j) → ∀ k x →
            (renEnv (r' ∘ᵣ r) ρ ,, v) k x ≡ (renEnv r' (renEnv r ρ) ,, v) k x
env-split r' r ρ v k vz     = refl
env-split r' r ρ v k (vs x) = sym (renVal-comp k r' r (ρ k x))

renEnv-ext : (r : Ren Θ Δ) (ρ : Env Δ Γ) → ∀ k (x : Var (j ∷ Γ) k) →
             renEnv (ext r) (extEnv ρ) k x ≡ extEnv (renEnv r ρ) k x
renEnv-ext {j = j} r ρ k vz     = reflect-ren j (ext r) (nvar vz)
renEnv-ext r ρ k (vs x) =
  renVal-comp k (ext r) wk (ρ k x) ∙ sym (renVal-comp k wk r (ρ k x))

------------------------------------------------------------------------
-- Evaluation respects related environments and commutes with renaming.

eval-≈   : (t : Ty Γ k) {ρ ρ' : Env Δ Γ} → EnvEq ρ ρ' → SemEq k (eval t ρ) (eval t ρ')
eval-nat : (t : Ty Γ k) (r : Ren Θ Δ) {ρ ρ' : Env Δ Γ} → EnvEq ρ ρ' →
           SemEq k (renVal k r (eval t ρ)) (eval t (renEnv r ρ'))

eval-≈ (var x)     e = e _ x
eval-≈ (base b)    e = refl
eval-≈ (capp c a)  e = cong (ncapp c) (eval-≈ a e)
eval-≈ (papp p a)  e = cong (inspect p) (eval-≈ a e)
eval-≈ (arr q a b) e = cong₂ (narr q) (eval-≈ a e) (eval-≈ b e)
eval-≈ (a ⊗ b)     e = cong₂ _n⊗_ (eval-≈ a e) (eval-≈ b e)
eval-≈ (a ⊕ b)     e = cong₂ _n⊕_ (eval-≈ a e) (eval-≈ b e)
eval-≈ (lam {k = k} {j = j} b) {ρ} {ρ'} e =
    cong nlam (≈-reify j (eval-≈ b (envEq-ext e)))
  , (λ Δ r v v' ev → eval-≈ b (envEq-,, (envEq-ren r e) ev))
  , (λ Δ Θ r r' v v' ev →
       ≈≡ j (eval-nat b r' (envEq-,, (envEq-ren r e) ev))
            (cong (eval b) (envExt (env-push r' r ρ' v'))))
eval-≈ (app f a)   e = fst (snd (eval-≈ f e)) _ idᵣ _ _ (eval-≈ a e)

eval-nat (var x)     r e = ≈-ren _ r (e _ x)
eval-nat (base b)    r e = refl
eval-nat (capp c a)  r e = cong (ncapp c) (eval-nat a r e)
eval-nat (papp p a)  r {ρ} e = inspect-ren r p (eval a ρ) ∙ cong (inspect p) (eval-nat a r e)
eval-nat (arr q a b) r e = cong₂ (narr q) (eval-nat a r e) (eval-nat b r e)
eval-nat (a ⊗ b)     r e = cong₂ _n⊗_ (eval-nat a r e) (eval-nat b r e)
eval-nat (a ⊕ b)     r e = cong₂ _n⊕_ (eval-nat a r e) (eval-nat b r e)
eval-nat (lam {k = k} {j = j} b) r {ρ} {ρ'} e =
    cong nlam
      (reify-ren j (ext r) (eval b (extEnv ρ))
       ∙ ≈-reify j (≈≡ j (eval-nat b (ext r) (envEq-ext e))
                         (cong (eval b) (envExt (renEnv-ext r ρ')))))
  , (λ Δ r₁ v v' ev →
       ≈≡ j (eval-≈ b (envEq-,, (envEq-ren (r₁ ∘ᵣ r) e) ev))
            (cong (eval b) (envExt (env-split r₁ r ρ' v'))))
  , (λ Δ Θ r₁ r' v v' ev →
       ≈≡ j (eval-nat b r' (envEq-,, (envEq-ren (r₁ ∘ᵣ r) e) ev))
            (cong (eval b)
               (envExt (λ k x → env-push r' (r₁ ∘ᵣ r) ρ' v' k x
                               ∙ env-split (r' ∘ᵣ r₁) r ρ' (renVal _ r' v') k x))))
eval-nat (app {k = k} {j = j} f a) r {ρ} {ρ'} e =
  ≈-trans j
    (snd (snd (eval-≈ f (envEq-refl-l e))) _ _ idᵣ r _ _ (eval-≈ a (envEq-refl-l e)))
    (fst (snd (eval-nat f r e)) _ idᵣ _ _ (eval-nat a r e))

------------------------------------------------------------------------
-- Evaluation commutes with renaming and substitution of the term.

private
  ren-env₁ : (r : Ren Δ Γ) (ρ : Env Θ Δ) → ∀ k (x : Var (j ∷ Γ) k) →
             extEnv ρ k (ext r k x) ≡ extEnv (λ k y → ρ k (r k y)) k x
  ren-env₁ r ρ k vz     = refl
  ren-env₁ r ρ k (vs x) = refl

  ren-env₂ : (r : Ren Δ Γ) (ρ : Env Θ Δ) (v : Val Θ j) → ∀ k (x : Var (j ∷ Γ) k) →
             (ρ ,, v) k (ext r k x) ≡ ((λ k y → ρ k (r k y)) ,, v) k x
  ren-env₂ r ρ v k vz     = refl
  ren-env₂ r ρ v k (vs x) = refl

eval-ren : (t : Ty Γ k) (r : Ren Δ Γ) (ρ : Env Θ Δ) →
           eval (ren r t) ρ ≡ eval t (λ k x → ρ k (r k x))
eval-ren (var x)     r ρ = refl
eval-ren (base b)    r ρ = refl
eval-ren (capp c a)  r ρ = cong (ncapp c) (eval-ren a r ρ)
eval-ren (papp p a)  r ρ = cong (inspect p) (eval-ren a r ρ)
eval-ren (arr q a b) r ρ = cong₂ (narr q) (eval-ren a r ρ) (eval-ren b r ρ)
eval-ren (a ⊗ b)     r ρ = cong₂ _n⊗_ (eval-ren a r ρ) (eval-ren b r ρ)
eval-ren (a ⊕ b)     r ρ = cong₂ _n⊕_ (eval-ren a r ρ) (eval-ren b r ρ)
eval-ren (lam {j = j} b) r ρ =
  λ i → nlam (reify j ((eval-ren b (ext r) (extEnv ρ)
                        ∙ cong (eval b) (envExt (ren-env₁ r ρ))) i))
      , λ Θ r₁ v → (eval-ren b (ext r) (renEnv r₁ ρ ,, v)
                    ∙ cong (eval b) (envExt (ren-env₂ r (renEnv r₁ ρ) v))) i
eval-ren (app f a)   r ρ = λ i → snd (eval-ren f r ρ i) _ idᵣ (eval-ren a r ρ i)

eval-sub : (t : Ty Γ k) (σ : TySub Δ Γ) {ρ ρ' : Env Θ Δ} → EnvEq ρ ρ' →
           SemEq k (eval (sub σ t) ρ) (eval t (λ k x → eval (σ k x) ρ'))
eval-sub (var x)     σ e = eval-≈ (σ _ x) e
eval-sub (base b)    σ e = refl
eval-sub (capp c a)  σ e = cong (ncapp c) (eval-sub a σ e)
eval-sub (papp p a)  σ e = cong (inspect p) (eval-sub a σ e)
eval-sub (arr q a b) σ e = cong₂ (narr q) (eval-sub a σ e) (eval-sub b σ e)
eval-sub (a ⊗ b)     σ e = cong₂ _n⊗_ (eval-sub a σ e) (eval-sub b σ e)
eval-sub (a ⊕ b)     σ e = cong₂ _n⊕_ (eval-sub a σ e) (eval-sub b σ e)
eval-sub {Θ = Θ} (lam {k = k} {j = j} b) σ {ρ} {ρ'} e =
    cong nlam (≈-reify j (≈-trans j (eval-sub b (exts σ) (envEq-ext e)) (eval-≈ b envA)))
  , (λ Δ r v v' ev →
       ≈-trans j (eval-sub b (exts σ) (envEq-,, (envEq-ren r e) ev))
                 (eval-≈ b (envB r v' (≈-refl-r k ev))))
  , (λ Δ Ξ r r' v v' ev →
       ≈-trans j (eval-nat (sub (exts σ) b) r' (envEq-,, (envEq-ren r e) ev))
      (≈-trans j (eval-sub b (exts σ)
                    (envEq-ren r' (envEq-,, (envEq-ren r (envEq-refl-r e)) (≈-refl-r k ev))))
                 (eval-≈ b (envC r r' v' (≈-refl-r k ev)))))
  where
  e' : EnvEq ρ' ρ'
  e' = envEq-refl-r e

  envA : EnvEq (λ k x → eval (exts σ k x) (extEnv ρ')) (extEnv (λ k x → eval (σ k x) ρ'))
  envA k₁ vz     = ≈-reflect k refl
  envA k₁ (vs x) =
    ≡≈ k₁ (eval-ren (σ k₁ x) wk (extEnv ρ')) (≈-sym k₁ (eval-nat (σ k₁ x) wk e'))

  envB : ∀ {Δ} (r : Ren Δ Θ) (v' : Val Δ k) → SemEq k v' v' →
         EnvEq (λ k x → eval (exts σ k x) (renEnv r ρ' ,, v'))
               (renEnv r (λ k x → eval (σ k x) ρ') ,, v')
  envB r v' ev' k₁ vz     = ev'
  envB r v' ev' k₁ (vs x) =
    ≡≈ k₁ (eval-ren (σ k₁ x) wk (renEnv r ρ' ,, v')) (≈-sym k₁ (eval-nat (σ k₁ x) r e'))

  envC : ∀ {Δ Ξ} (r : Ren Δ Θ) (r' : Ren Ξ Δ) (v' : Val Δ k) → SemEq k v' v' →
         EnvEq (λ k x → eval (exts σ k x) (renEnv r' (renEnv r ρ' ,, v')))
               (renEnv (r' ∘ᵣ r) (λ k x → eval (σ k x) ρ') ,, renVal k r' v')
  envC r r' v' ev' k₁ vz     = ≈-ren k r' ev'
  envC r r' v' ev' k₁ (vs x) =
    ≡≈ k₁ (eval-ren (σ k₁ x) wk (renEnv r' (renEnv r ρ' ,, v'))
           ∙ cong (eval (σ k₁ x)) (envExt (λ k y → renVal-comp k r' r (ρ' k y))))
          (≈-sym k₁ (eval-nat (σ k₁ x) (r' ∘ᵣ r) e'))
eval-sub (app f a)   σ e = fst (snd (eval-sub f σ e)) _ idᵣ _ _ (eval-sub a σ e)

------------------------------------------------------------------------
-- Completeness.

private
  res-eval : (x : Base ⊎ Prim) (v : Nf Δ ★) (A : Ty Γ ★) (ρ' : Env Δ Γ) → v ≡ eval A ρ' →
             resNf x (λ q → inspect q v) ≡ eval (resTy x A) ρ'
  res-eval (inl b) v A ρ' h = refl
  res-eval (inr q) v A ρ' h = cong (inspect q) h

  β-env : (u : Ty Γ j) {ρ ρ' : Env Δ Γ} → EnvEq ρ ρ' →
          EnvEq (renEnv idᵣ ρ ,, eval u ρ) (λ k x → eval ((u ∷ₛ ids) k x) ρ')
  β-env u e k vz     = eval-≈ u e
  β-env u {ρ} e k (vs x) = ≡≈ k (renVal-id k (ρ k x)) (e k x)

complete : {t u : Ty Γ k} → DefEq t u → {ρ ρ' : Env Δ Γ} → EnvEq ρ ρ' →
           SemEq k (eval t ρ) (eval u ρ')
complete (d-refl {t = t}) e = eval-≈ t e
complete (d-sym d)        e = ≈-sym _ (complete d (envEq-sym e))
complete (d-trans d d')   e = ≈-trans _ (complete d (envEq-refl-l e)) (complete d' e)
complete (d-beta {j = j} b u) e =
  ≈-trans j (eval-≈ b (β-env u e))
            (≈-sym j (eval-sub b (u ∷ₛ ids) (envEq-refl-r e)))
complete (d-capp {c = c} d) e = cong (ncapp c) (complete d e)
complete (d-papp {p = p} d) e = cong (inspect p) (complete d e)
complete (d-arr {q = q} d d') e = cong₂ (narr q) (complete d e) (complete d' e)
complete (d-prod d d')    e = cong₂ _n⊗_ (complete d e) (complete d' e)
complete (d-sum d d')     e = cong₂ _n⊕_ (complete d e) (complete d' e)
complete (d-lam {k = k} {j = j} {b = b} d) {ρ} {ρ'} e =
    cong nlam (≈-reify j (complete d (envEq-ext e)))
  , (λ Δ r v v' ev → complete d (envEq-,, (envEq-ren r e) ev))
  , (λ Δ Θ r r' v v' ev →
       ≈-trans j
         (eval-nat b r' (envEq-,, (envEq-ren r (envEq-refl-l e)) (≈-refl-l k ev)))
         (complete d (λ k₁ x →
            ≈≡ k₁ (envEq-ren r' (envEq-,, (envEq-ren r e) ev) k₁ x)
                  (env-push r' r ρ' v' k₁ x))))
complete (d-app d d')     e = fst (snd (complete d e)) _ idᵣ _ _ (complete d' e)
complete (δ-base p b)     e = refl
complete (δ-capp p c A) {ρ} {ρ'} e = res-eval (onCon p c) (eval A ρ) A ρ' (eval-≈ A e)
complete (δ-arr p q A B)  e = refl
complete (δ-prod p A B)   e = refl
complete (δ-sum p A B)    e = refl

idEnv-≈ : EnvEq (idEnv {Γ}) idEnv
idEnv-≈ k x = ≈-reflect k refl

-- Convertible terms have equal normal forms.
completeness : {t u : Ty Γ k} → DefEq t u → nf t ≡ nf u
completeness {k = k} d = ≈-reify k (complete d idEnv-≈)

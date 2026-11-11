{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Stage 8. Coercions at open types. Definitions only.
--
-- An open source type has type variables. Its other leaves are closed
-- source types. An open coercion is built from:
--   the identity, at each open type;
--   each closed representational coercion of `Wager.FC.Coercion`;
--   symmetry, transitivity, and congruence for a function, a pair and
--   a sum.
-- Its translation is ONE open term of `Wager.Poly.Term`.
--
-- A newtype that is applied to a type variable is not an open source
-- type here. The reason is in `T8-No-Uniform-Unwrap`: a trope operation
-- has a closed carrier (`Wager.L2.Signature.TSig`).
open import Cubical.Foundations.Prelude
open import Wager.FC.Signature
open import Wager.Grade.Algebra
import Wager.Trans.Scheme

module Wager.Poly.Coercion
  (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
  {R : Type} (ops : GradeOps R) where

open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)
open import Cubical.Data.List.Base using (_++_)

open import Wager.Role.Role
open import Wager.FC.Types SS hiding (inst)
open import Wager.FC.Coercion SS
open import Wager.Trans.Target SS Sc ops
open import Wager.Trans.Coercion SS Sc ops using (Tm; Iso; coI; coerceT)
import Wager.L2.Term tSig tTSig as C
open import Wager.Poly.Term tSig tTSig public
open GradeOps ops using (𝟙)

private
  variable
    n : ℕ
    Δ : Ctx
    τ σ : STy

------------------------------------------------------------------------
-- Open source types.

infixr 20 _⇒ᵒ_
infixr 30 _+ᵒ_
infixr 40 _×ᵒ_

data OTy (Δ : Ctx) : Type where
  ovar : Var Δ ★ → OTy Δ
  -- A closed source type.
  clo  : STy → OTy Δ
  _⇒ᵒ_ : OTy Δ → OTy Δ → OTy Δ
  _×ᵒ_ : OTy Δ → OTy Δ → OTy Δ
  _+ᵒ_ : OTy Δ → OTy Δ → OTy Δ

private
  variable
    θ θ' φ φ' χ : OTy Δ

-- An instantiation of the source: a closed source type for each type
-- variable of the kind ★.
SInst : Ctx → Type
SInst Δ = Var Δ ★ → STy

infix 45 _⟦_⟧
_⟦_⟧ : OTy Δ → SInst Δ → STy
ovar x   ⟦ ρ ⟧ = ρ x
clo τ    ⟦ ρ ⟧ = τ
(θ ⇒ᵒ φ) ⟦ ρ ⟧ = θ ⟦ ρ ⟧ ⇒ˢ φ ⟦ ρ ⟧
(θ ×ᵒ φ) ⟦ ρ ⟧ = θ ⟦ ρ ⟧ ×ˢ φ ⟦ ρ ⟧
(θ +ᵒ φ) ⟦ ρ ⟧ = θ ⟦ ρ ⟧ +ˢ φ ⟦ ρ ⟧

-- The translation of an open source type: an open type of the target.
Tᵒ : OTy Δ → Ty Δ ★
Tᵒ (ovar x) = var x
Tᵒ (clo τ)  = ⇑ (T τ)
Tᵒ (θ ⇒ᵒ φ) = arr 𝟙 (Tᵒ θ) (Tᵒ φ)
Tᵒ (θ ×ᵒ φ) = Tᵒ θ ⊗ Tᵒ φ
Tᵒ (θ +ᵒ φ) = Tᵒ θ ⊕ Tᵒ φ

-- A substitution of the target agrees with an instantiation of the
-- source when it gives each type variable of the kind ★ the
-- translation of its source type.
Agrees : TySub [] Δ → SInst Δ → Type
Agrees {Δ} s ρ = (x : Var Δ ★) → s ★ x ≡ T (ρ x)

------------------------------------------------------------------------
-- Open representational coercions.

data Coᵒ {Δ : Ctx} : OTy Δ → OTy Δ → Type where
  o-refl  : Coᵒ θ θ
  o-clo   : Co rep τ σ → Coᵒ (clo τ) (clo σ)
  o-sym   : Coᵒ θ φ → Coᵒ φ θ
  o-trans : Coᵒ θ φ → Coᵒ φ χ → Coᵒ θ χ
  o-arr   : Coᵒ θ θ' → Coᵒ φ φ' → Coᵒ (θ ⇒ᵒ φ) (θ' ⇒ᵒ φ')
  o-prod  : Coᵒ θ θ' → Coᵒ φ φ' → Coᵒ (θ ×ᵒ φ) (θ' ×ᵒ φ')
  o-sum   : Coᵒ θ θ' → Coᵒ φ φ' → Coᵒ (θ +ᵒ φ) (θ' +ᵒ φ')

-- Each instance of an open coercion is a closed representational
-- coercion of the source calculus.
infix 45 _⟦_⟧ᶜ
_⟦_⟧ᶜ : {θ φ : OTy Δ} → Coᵒ θ φ → (ρ : SInst Δ) → Co rep (θ ⟦ ρ ⟧) (φ ⟦ ρ ⟧)
o-refl      ⟦ ρ ⟧ᶜ = c-sub c-refl
o-clo γ     ⟦ ρ ⟧ᶜ = γ
o-sym c     ⟦ ρ ⟧ᶜ = c-sym (c ⟦ ρ ⟧ᶜ)
o-trans c d ⟦ ρ ⟧ᶜ = c-trans (c ⟦ ρ ⟧ᶜ) (d ⟦ ρ ⟧ᶜ)
o-arr c d   ⟦ ρ ⟧ᶜ = c-arr (c ⟦ ρ ⟧ᶜ) (d ⟦ ρ ⟧ᶜ)
o-prod c d  ⟦ ρ ⟧ᶜ = c-prod (c ⟦ ρ ⟧ᶜ) (d ⟦ ρ ⟧ᶜ)
o-sum c d   ⟦ ρ ⟧ᶜ = c-sum (c ⟦ ρ ⟧ᶜ) (d ⟦ ρ ⟧ᶜ)

------------------------------------------------------------------------
-- Term transformers on open terms. Each definition has the text of its
-- definition in `Wager.Trans.Coercion`, with the types in Δ.

Trᵖ : Ctx → Type
Trᵖ Δ = ∀ {n} → Tmᵖ Δ n → Tmᵖ Δ n

record Isoᵖ (Δ : Ctx) : Type where
  constructor isoᵖ
  field
    fwdᵖ : Trᵖ Δ
    bwdᵖ : Trᵖ Δ
open Isoᵖ public

idIsoᵖ : Isoᵖ Δ
idIsoᵖ = isoᵖ (λ t → t) (λ t → t)

swapIsoᵖ : Isoᵖ Δ → Isoᵖ Δ
swapIsoᵖ i = isoᵖ (bwdᵖ i) (fwdᵖ i)

compIsoᵖ : Isoᵖ Δ → Isoᵖ Δ → Isoᵖ Δ
compIsoᵖ i j = isoᵖ (λ t → fwdᵖ j (fwdᵖ i t)) (λ t → bwdᵖ i (bwdᵖ j t))

arrMapᵖ : (X A : Ty Δ ★) → Trᵖ Δ → Trᵖ Δ → Trᵖ Δ
arrMapᵖ X A h g t =
  tapp (tlam 𝟙 X (tlam 𝟙 A (g (tapp (tvar (suc zero)) (h (tvar zero)))))) t

arrIsoᵖ : (A A' B B' : Ty Δ ★) → Isoᵖ Δ → Isoᵖ Δ → Isoᵖ Δ
arrIsoᵖ A A' B B' i j =
  isoᵖ (arrMapᵖ (arr 𝟙 A B) A' (bwdᵖ i) (fwdᵖ j))
       (arrMapᵖ (arr 𝟙 A' B') A (fwdᵖ i) (bwdᵖ j))

prodMapᵖ : Trᵖ Δ → Trᵖ Δ → Trᵖ Δ
prodMapᵖ f g t = letp t (pair (f (tvar (suc zero))) (g (tvar zero)))

prodIsoᵖ : Isoᵖ Δ → Isoᵖ Δ → Isoᵖ Δ
prodIsoᵖ i j = isoᵖ (prodMapᵖ (fwdᵖ i) (fwdᵖ j)) (prodMapᵖ (bwdᵖ i) (bwdᵖ j))

sumMapᵖ : Trᵖ Δ → Trᵖ Δ → Trᵖ Δ
sumMapᵖ f g t = case t (inj₁ (f (tvar zero))) (inj₂ (g (tvar zero)))

sumIsoᵖ : Isoᵖ Δ → Isoᵖ Δ → Isoᵖ Δ
sumIsoᵖ i j = isoᵖ (sumMapᵖ (fwdᵖ i) (fwdᵖ j)) (sumMapᵖ (bwdᵖ i) (bwdᵖ j))

-- The two trope transitions of a newtype instance. The instance is
-- closed: an operation of the signature has a closed carrier.
stepIsoᵖ : Inst → Isoᵖ Δ
stepIsoᵖ x = isoᵖ (λ t → step (unwrap , x) t) (λ t → step (wrap , x) t)

bodyIsoᵖ : Body Base Fam → (X Y : Ty [] ★) → Isoᵖ Δ → Isoᵖ Δ
bodyIsoᵖ bvar        X Y i = i
bodyIsoᵖ (bbase b)   X Y i = idIsoᵖ
bodyIsoᵖ (barr β γ)  X Y i =
  arrIsoᵖ (⇑ (TB β X)) (⇑ (TB β Y)) (⇑ (TB γ X)) (⇑ (TB γ Y))
          (bodyIsoᵖ β X Y i) (bodyIsoᵖ γ X Y i)
bodyIsoᵖ (bprod β γ) X Y i = prodIsoᵖ (bodyIsoᵖ β X Y i) (bodyIsoᵖ γ X Y i)
bodyIsoᵖ (bsum β γ)  X Y i = sumIsoᵖ (bodyIsoᵖ β X Y i) (bodyIsoᵖ γ X Y i)
bodyIsoᵖ (bfam F β)  X Y i = idIsoᵖ

ntIsoᵖ : (N : N₁) (τ σ : STy) → Isoᵖ Δ → Isoᵖ Δ
ntIsoᵖ N τ σ i =
  isoᵖ (λ t → step (wrap , inr (N , σ)) (fwdᵖ b (step (unwrap , inr (N , τ)) t)))
       (λ t → step (wrap , inr (N , τ)) (bwdᵖ b (step (unwrap , inr (N , σ)) t)))
  where b = bodyIsoᵖ (body N) (T τ) (T σ) i

-- A closed coercion, as a transformer of open terms.
coIᵖ : (r : Role) → Co r τ σ → Isoᵖ Δ
coIᵖ nom γ = idIsoᵖ
coIᵖ ph  γ = idIsoᵖ
coIᵖ rep (c-sym γ)     = swapIsoᵖ (coIᵖ rep γ)
coIᵖ rep (c-trans γ δ) = compIsoᵖ (coIᵖ rep γ) (coIᵖ rep δ)
coIᵖ rep (c-sub γ)     = idIsoᵖ
coIᵖ rep (c-arr {τ = τ} {τ' = τ'} {σ = σ} {σ' = σ'} γ δ) =
  arrIsoᵖ (⇑ (T τ)) (⇑ (T τ')) (⇑ (T σ)) (⇑ (T σ')) (coIᵖ rep γ) (coIᵖ rep δ)
coIᵖ rep (c-prod γ δ)  = prodIsoᵖ (coIᵖ rep γ) (coIᵖ rep δ)
coIᵖ rep (c-sum γ δ)   = sumIsoᵖ (coIᵖ rep γ) (coIᵖ rep δ)
coIᵖ rep (c-nt₁ {τ = τ} {σ = σ} N γ) = ntIsoᵖ N τ σ (coIᵖ (mulG rep (role N)) γ)
coIᵖ rep (c-ax₀ N)     = stepIsoᵖ (inl N)
coIᵖ rep (c-ax₁ N τ)   = stepIsoᵖ (inr (N , τ))

-- THE TRANSLATION OF AN OPEN COERCION.
coIᵒ : {θ φ : OTy Δ} → Coᵒ θ φ → Isoᵖ Δ
coIᵒ o-refl        = idIsoᵖ
coIᵒ (o-clo γ)     = coIᵖ rep γ
coIᵒ (o-sym c)     = swapIsoᵖ (coIᵒ c)
coIᵒ (o-trans c d) = compIsoᵖ (coIᵒ c) (coIᵒ d)
coIᵒ (o-arr {θ = θ} {θ' = θ'} {φ = φ} {φ' = φ'} c d) =
  arrIsoᵖ (Tᵒ θ) (Tᵒ θ') (Tᵒ φ) (Tᵒ φ') (coIᵒ c) (coIᵒ d)
coIᵒ (o-prod c d)  = prodIsoᵖ (coIᵒ c) (coIᵒ d)
coIᵒ (o-sum c d)   = sumIsoᵖ (coIᵒ c) (coIᵒ d)

-- The open coercion as one open function of the target.
coerceᵒ : {θ φ : OTy Δ} → Coᵒ θ φ → Tmᵖ Δ n
coerceᵒ {θ = θ} c = tlam 𝟙 (Tᵒ θ) (fwdᵖ (coIᵒ c) (tvar zero))

------------------------------------------------------------------------
-- The trope operations of a term, in the order of the text.

opsOf : Tm n → List C.Op
opsOf (C.tvar i)     = []
opsOf (C.tlam q A b) = opsOf b
opsOf (C.tapp f a)   = opsOf f ++ opsOf a
opsOf (C.pair s t)   = opsOf s ++ opsOf t
opsOf (C.letp s b)   = opsOf s ++ opsOf b
opsOf (C.inj₁ t)     = opsOf t
opsOf (C.inj₂ t)     = opsOf t
opsOf (C.case s l r) = opsOf s ++ (opsOf l ++ opsOf r)
opsOf (C.lit ℓ)      = []
opsOf (C.step o t)   = o ∷ opsOf t

opsOfᵖ : Tmᵖ Δ n → List C.Op
opsOfᵖ (tvar i)     = []
opsOfᵖ (tlam q A b) = opsOfᵖ b
opsOfᵖ (tapp f a)   = opsOfᵖ f ++ opsOfᵖ a
opsOfᵖ (pair s t)   = opsOfᵖ s ++ opsOfᵖ t
opsOfᵖ (letp s b)   = opsOfᵖ s ++ opsOfᵖ b
opsOfᵖ (inj₁ t)     = opsOfᵖ t
opsOfᵖ (inj₂ t)     = opsOfᵖ t
opsOfᵖ (case s l r) = opsOfᵖ s ++ (opsOfᵖ l ++ opsOfᵖ r)
opsOfᵖ (lit ℓ)      = []
opsOfᵖ (step o t)   = o ∷ opsOfᵖ t

{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on coercions and on typed terms.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The translation of coercions and of terms (Stage 4).
--
-- A representational coercion becomes a pair of term transformers
-- (forwards and backwards). A transformer is built from:
--   trope transitions   wrap and unwrap of a newtype instance;
--   functorial maps     for a function, a pair and a sum;
--   composition and the identity.
-- A nominal coercion becomes the identity transformer: the two
-- translated types are convertible, and no term remains.
--
-- There is no cast in the target. The translation of `cast γ e` is the
-- transformer of γ on the translation of e.
open import Cubical.Foundations.Prelude
open import Wager.FC.Signature
open import Wager.Grade.Algebra
import Wager.Trans.Scheme

module Wager.Trans.Coercion
  (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
  {R : Type} (ops : GradeOps R) where

open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)

open import Wager.Role.Role
open import Wager.FC.Types SS
open import Wager.FC.Coercion SS
open import Wager.FC.Term SS
open import Wager.Trans.Target SS Sc ops
open import Wager.L2.Term tSig tTSig hiding (Lit; litTy) public
open GradeOps ops using (𝟙)

private
  variable
    n : ℕ
    τ σ : STy

-- A term transformer works in each scope.
Tr : Type
Tr = ∀ {n} → Tm n → Tm n

record Iso : Type where
  constructor iso
  field
    fwd : Tr
    bwd : Tr
open Iso public

idIso : Iso
idIso = iso (λ t → t) (λ t → t)

swapIso : Iso → Iso
swapIso i = iso (bwd i) (fwd i)

compIso : Iso → Iso → Iso
compIso i j = iso (λ t → fwd j (fwd i t)) (λ t → bwd i (bwd j t))

-- The map of a function: (λf. λx. g (f (h x))) t.
-- X is the type of t, and A is the type of x.
arrMap : (X A : Ty [] ★) → Tr → Tr → Tr
arrMap X A h g t =
  tapp (tlam 𝟙 X (tlam 𝟙 A (g (tapp (tvar (suc zero)) (h (tvar zero)))))) t

arrIso : (A A' B B' : Ty [] ★) → Iso → Iso → Iso
arrIso A A' B B' i j =
  iso (arrMap (arr 𝟙 A B) A' (bwd i) (fwd j))
      (arrMap (arr 𝟙 A' B') A (fwd i) (bwd j))

-- The map of a pair: let (x, y) = t in (f x, g y).
prodMap : Tr → Tr → Tr
prodMap f g t = letp t (pair (f (tvar (suc zero))) (g (tvar zero)))

prodIso : Iso → Iso → Iso
prodIso i j = iso (prodMap (fwd i) (fwd j)) (prodMap (bwd i) (bwd j))

-- The map of a sum: case t of { inl x → inl (f x) ; inr y → inr (g y) }.
sumMap : Tr → Tr → Tr
sumMap f g t = case t (inj₁ (f (tvar zero))) (inj₂ (g (tvar zero)))

sumIso : Iso → Iso → Iso
sumIso i j = iso (sumMap (fwd i) (fwd j)) (sumMap (bwd i) (bwd j))

-- The two trope transitions of a newtype instance.
-- Forwards is unwrap: from the newtype to its representation.
stepIso : Inst → Iso
stepIso x = iso (λ t → step (unwrap , x) t) (λ t → step (wrap , x) t)

-- The map of a body, from the map of its parameter. X and Y are the
-- two types of the parameter.
bodyIso : Body Base Fam → (X Y : Ty [] ★) → Iso → Iso
bodyIso bvar        X Y i = i
bodyIso (bbase b)   X Y i = idIso
bodyIso (barr β γ)  X Y i =
  arrIso (TB β X) (TB β Y) (TB γ X) (TB γ Y) (bodyIso β X Y i) (bodyIso γ X Y i)
bodyIso (bprod β γ) X Y i = prodIso (bodyIso β X Y i) (bodyIso γ X Y i)
bodyIso (bsum β γ)  X Y i = sumIso (bodyIso β X Y i) (bodyIso γ X Y i)
bodyIso (bfam F β)  X Y i = idIso

-- Congruence for a newtype: unwrap, map the body, wrap.
ntIso : (N : N₁) (τ σ : STy) → Iso → Iso
ntIso N τ σ i =
  iso (λ t → step (wrap , inr (N , σ)) (fwd b (step (unwrap , inr (N , τ)) t)))
      (λ t → step (wrap , inr (N , τ)) (bwd b (step (unwrap , inr (N , σ)) t)))
  where b = bodyIso (body N) (T τ) (T σ) i

-- The translation of a coercion. Only the role representational gives
-- a term.
coI : (r : Role) → Co r τ σ → Iso
coI nom γ = idIso
coI ph  γ = idIso
coI rep (c-sym γ)     = swapIso (coI rep γ)
coI rep (c-trans γ δ) = compIso (coI rep γ) (coI rep δ)
coI rep (c-sub γ)     = idIso
coI rep (c-arr {τ = τ} {τ' = τ'} {σ = σ} {σ' = σ'} γ δ) =
  arrIso (T τ) (T τ') (T σ) (T σ') (coI rep γ) (coI rep δ)
coI rep (c-prod γ δ)  = prodIso (coI rep γ) (coI rep δ)
coI rep (c-sum γ δ)   = sumIso (coI rep γ) (coI rep δ)
coI rep (c-nt₁ {τ = τ} {σ = σ} N γ) = ntIso N τ σ (coI (mulG rep (role N)) γ)
coI rep (c-ax₀ N)     = stepIso (inl N)
coI rep (c-ax₁ N τ)   = stepIso (inr (N , τ))

-- The translated coercion as a function of the target: λx. (coercion) x.
coerceT : Co rep τ σ → Tm n
coerceT {τ = τ} γ = tlam 𝟙 (T τ) (fwd (coI rep γ) (tvar zero))

------------------------------------------------------------------------
-- The translation of terms.

tr : ∀ {Γ : SCx n} → STm Γ τ → Tm n
tr (svar i)         = tvar i
tr (slam {τ = τ} b) = tlam 𝟙 (T τ) (tr b)
tr (sapp f a)       = tapp (tr f) (tr a)
tr (spair s t)      = pair (tr s) (tr t)
tr (sletp s b)      = letp (tr s) (tr b)
tr (sinl t)         = inj₁ (tr t)
tr (sinr t)         = inj₂ (tr t)
tr (scase s l r)    = case (tr s) (tr l) (tr r)
tr (slit ℓ)         = lit ℓ
tr (cast γ e)       = fwd (coI rep γ) (tr e)

------------------------------------------------------------------------
-- Erasure of the target: a trope transition vanishes.

eraseT : Tm n → UTm n
eraseT (tvar i)     = uvar i
eraseT (tlam q A b) = ulam (eraseT b)
eraseT (tapp f a)   = uapp (eraseT f) (eraseT a)
eraseT (pair s t)   = upair (eraseT s) (eraseT t)
eraseT (letp s b)   = uletp (eraseT s) (eraseT b)
eraseT (inj₁ t)     = uinl (eraseT t)
eraseT (inj₂ t)     = uinr (eraseT t)
eraseT (case s l r) = ucase (eraseT s) (eraseT l) (eraseT r)
eraseT (lit ℓ)      = ulit ℓ
eraseT (step o t)   = eraseT t

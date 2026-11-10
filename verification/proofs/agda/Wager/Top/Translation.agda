{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- A variant of the translation of Stage 4, with a grade q on each
-- arrow and on each binder that the translation of a source function
-- makes. Definitions only.
--
-- The translation of Stage 4 writes the grade 𝟙 there. The question:
-- is a top grade q enough for the typing of a whole program, in the
-- place of an unrestricted grade 𝟙?
--
-- The translation of types is the translation of Stage 4, read with q
-- in the place of 𝟙 (`opsq`). `opsq` is used for this reading only. The
-- typing judgement of the statements has the operations `ops`.
open import Cubical.Foundations.Prelude
open import Wager.FC.Signature
open import Wager.Grade.Algebra
import Wager.Trans.Scheme

module Wager.Top.Translation
  (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
  {R : Type} (ops : GradeOps R) (q : R) where

open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit)
open import Cubical.Data.Empty using (⊥)

open import Wager.Role.Role
open import Wager.FC.Types SS
open import Wager.FC.Coercion SS
open import Wager.FC.Term SS

-- The operations of `ops`, with q in the place of 𝟙.
opsq : GradeOps R
opsq = record
  { _+_ = GradeOps._+_ ops ; _·_ = GradeOps._·_ ops
  ; 𝟘 = GradeOps.𝟘 ops ; 𝟙 = q ; _≤_ = GradeOps._≤_ ops }

-- Types: `T (τ ⇒ˢ σ)` is `arr q (T τ) (T σ)`.
open import Wager.Trans.Target SS Sc opsq
-- Terms, and the transformers that name no grade.
open import Wager.Trans.Coercion SS Sc opsq
  hiding (arrMap; arrIso; bodyIso; ntIso; coI; coerceT; tr)
open GradeOps ops using (𝟙)

private
  variable
    n : ℕ
    τ σ : STy

-- The map of a function: (λf. λx. g (f (h x))) t.
-- The binder of f has the grade 𝟙: the map uses f one time.
-- The binder of x has the grade q: it is the binder of the result,
-- a function of the type `arr q A' B'`.
arrMapq : (X A : Ty [] ★) → Tr → Tr → Tr
arrMapq X A h g t =
  tapp (tlam 𝟙 X (tlam q A (g (tapp (tvar (suc zero)) (h (tvar zero)))))) t

arrIsoq : (A A' B B' : Ty [] ★) → Iso → Iso → Iso
arrIsoq A A' B B' i j =
  iso (arrMapq (arr q A B) A' (bwd i) (fwd j))
      (arrMapq (arr q A' B') A (fwd i) (bwd j))

bodyIsoq : Body Base Fam → (X Y : Ty [] ★) → Iso → Iso
bodyIsoq bvar        X Y i = i
bodyIsoq (bbase b)   X Y i = idIso
bodyIsoq (barr β γ)  X Y i =
  arrIsoq (TB β X) (TB β Y) (TB γ X) (TB γ Y) (bodyIsoq β X Y i) (bodyIsoq γ X Y i)
bodyIsoq (bprod β γ) X Y i = prodIso (bodyIsoq β X Y i) (bodyIsoq γ X Y i)
bodyIsoq (bsum β γ)  X Y i = sumIso (bodyIsoq β X Y i) (bodyIsoq γ X Y i)
bodyIsoq (bfam F β)  X Y i = idIso

ntIsoq : (N : N₁) (τ σ : STy) → Iso → Iso
ntIsoq N τ σ i =
  iso (λ t → step (wrap , inr (N , σ)) (fwd b (step (unwrap , inr (N , τ)) t)))
      (λ t → step (wrap , inr (N , τ)) (bwd b (step (unwrap , inr (N , σ)) t)))
  where b = bodyIsoq (body N) (T τ) (T σ) i

coIq : (r : Role) → Co r τ σ → Iso
coIq nom γ = idIso
coIq ph  γ = idIso
coIq rep (c-sym γ)     = swapIso (coIq rep γ)
coIq rep (c-trans γ δ) = compIso (coIq rep γ) (coIq rep δ)
coIq rep (c-sub γ)     = idIso
coIq rep (c-arr {τ = τ} {τ' = τ'} {σ = σ} {σ' = σ'} γ δ) =
  arrIsoq (T τ) (T τ') (T σ) (T σ') (coIq rep γ) (coIq rep δ)
coIq rep (c-prod γ δ)  = prodIso (coIq rep γ) (coIq rep δ)
coIq rep (c-sum γ δ)   = sumIso (coIq rep γ) (coIq rep δ)
coIq rep (c-nt₁ {τ = τ} {σ = σ} N γ) = ntIsoq N τ σ (coIq (mulG rep (role N)) γ)
coIq rep (c-ax₀ N)     = stepIso (inl N)
coIq rep (c-ax₁ N τ)   = stepIso (inr (N , τ))

-- The coercion as a function of the target, with the grade q.
coerceTq : Co rep τ σ → Tm n
coerceTq {τ = τ} γ = tlam q (T τ) (fwd (coIq rep γ) (tvar zero))

-- The translation of terms: each binder of a source function has the
-- grade q.
trq : ∀ {Γ : SCx n} → STm Γ τ → Tm n
trq (svar i)         = tvar i
trq (slam {τ = τ} b) = tlam q (T τ) (trq b)
trq (sapp f a)       = tapp (trq f) (trq a)
trq (spair s t)      = pair (trq s) (trq t)
trq (sletp s b)      = letp (trq s) (trq b)
trq (sinl t)         = inj₁ (trq t)
trq (sinr t)         = inj₂ (trq t)
trq (scase s l r)    = case (trq s) (trq l) (trq r)
trq (slit ℓ)         = lit ℓ
trq (cast γ e)       = fwd (coIq rep γ) (trq e)

-- A source term with no elimination of a pair and no `case`.
NoElim : ∀ {Γ : SCx n} → STm Γ τ → Type
NoElim (svar i)      = Unit
NoElim (slam b)      = NoElim b
NoElim (sapp f a)    = NoElim f × NoElim a
NoElim (spair s t)   = NoElim s × NoElim t
NoElim (sletp s b)   = ⊥
NoElim (sinl t)      = NoElim t
NoElim (sinr t)      = NoElim t
NoElim (scase s l r) = ⊥
NoElim (slit ℓ)      = Unit
NoElim (cast γ e)    = NoElim e

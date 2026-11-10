{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on normal forms and on coercions.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Stage 7 (the optional univalent cross-check): the model.
--
-- The types of the target of Stage 4 get an interpretation in the
-- cubical universe (DESIGN-CHOICES.adoc, DC-7.1):
--
--   a base constant b      the type `El b` (a parameter of the model)
--   a function, pair, sum  the function type, the product, the sum
--   a newtype instance     `Box X`: a wrapper of the interpretation X of
--                          its content. `Box X` is not X, and
--                          `unboxEquiv` is an equivalence `Box X ≃ X`.
--
-- A trope transition (wrap, unwrap) is thus an equivalence, and
-- univalence (`ua`) makes it a path between two types.
--
-- A term has no interpretation by itself. The model is a realisability
-- model: `𝓡 u v x` says that the untyped value v, the result of an
-- erased program, realises the element x of the interpretation of u.
-- A wrapper has no realiser of its own: v realises `box x` when v
-- realises x.
--
-- `Denotes X Y f g` says that the term transformer f denotes the
-- function g: on a term that evaluates to a realiser of x, the term
-- `f t` evaluates to a realiser of `g x`.
--
-- `pathOf γ` is the path of a representational coercion γ. It is made
-- from `ua unboxEquiv` (a newtype axiom), `sym`, composition, and
-- congruence of the type formers.
open import Cubical.Foundations.Prelude
open import Wager.FC.Signature
open import Wager.Grade.Algebra
import Wager.Trans.Scheme
module Wager.Univalent.Model
  (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
  {R : Type} (A : GradeAlgebra R)
  (El : SSig.Base SS → Type)
  (elLit : (ℓ : SSig.Lit SS) → El (SSig.litTy SS ℓ)) where

open import Cubical.Foundations.Equiv using (_≃_)
import Cubical.Foundations.Isomorphism as CI
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Bool.Base using (true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit*; tt*)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.Sigma using (_×_; _,_; Σ-syntax)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)

open import Wager.Grade.Finite using (false≢true)
open import Wager.Role.Role
open import Wager.FC.Types SS
open import Wager.FC.Coercion SS
open import Wager.Trans.Target SS Sc (GradeAlgebra.ops A)
open import Wager.Trans.Nominal SS Sc (GradeAlgebra.ops A) using (nominal-defeq; T-inst; T-embE)
open import Wager.Trans.Coercion SS Sc (GradeAlgebra.ops A) using (Tr; Tm; eraseT)
open import Wager.Trans.Typing SS Sc A using (body-defeq)
open import Wager.L1.Normal tSig
open import Wager.L1.Eval tSig using (nf)
open import Wager.L1.Conversion tSig
open import Wager.L1.Equality tSig using (defEq→nf)
open import Wager.Erased.Untyped
open Terms Lit

private
  variable
    X Y : Ty [] ★
    τ σ : STy

------------------------------------------------------------------------
-- The interpretation of types.

-- A newtype instance: a wrapper of its content.
record Box (Z : Type) : Type where
  constructor box
  field
    unbox : Z

open Box public

-- THE EQUIVALENCE OF A NEWTYPE TRANSITION.
unboxEquiv : {Z : Type} → Box Z ≃ Z
unboxEquiv = CI.isoToEquiv (CI.iso unbox box (λ _ → refl) (λ _ → refl))

-- A closed normal form of the kind ★. The empty context has no neutral
-- type (`Wager.L2.Erasure.noNe`), so the first clause is not used.
⟦_⟧ⁿ : Nf [] ★ → Type
⟦ ne m ⟧ⁿ       = ⊥
⟦ nbase b ⟧ⁿ    = El b
⟦ ncapp s u ⟧ⁿ  = Box ⟦ u ⟧ⁿ
⟦ narr q a b ⟧ⁿ = ⟦ a ⟧ⁿ → ⟦ b ⟧ⁿ
⟦ a n⊗ b ⟧ⁿ     = ⟦ a ⟧ⁿ × ⟦ b ⟧ⁿ
⟦ a n⊕ b ⟧ⁿ     = ⟦ a ⟧ⁿ ⊎ ⟦ b ⟧ⁿ

-- A closed type: the interpretation of its normal form. Two convertible
-- types thus have one interpretation.
⟦_⟧ : Ty [] ★ → Type
⟦ Z ⟧ = ⟦ nf Z ⟧ⁿ

------------------------------------------------------------------------
-- Realisers.

-- A literal ℓ realises its element `elLit ℓ`.
data RLit (b : Base) : UVal → El b → Type where
  r-lit : ∀ ℓ (p : litTy ℓ ≡ b) → RLit b (vlit ℓ) (subst El p (elLit ℓ))

-- A closure realises a function: on a realiser of x, its body evaluates
-- to a realiser of `f x`.
data RFun {P Q : Type} (𝒫 : UVal → P → Type) (𝒬 : UVal → Q → Type) :
          UVal → (P → Q) → Type where
  r-fun : ∀ {n} {ρ : UEnv n} {t : UTm (suc n)} {f : P → Q} →
          (∀ w x → 𝒫 w x → Σ[ r ∈ UVal ] ((w ∷ᵉ ρ) ⊢ t ⇓ r) × 𝒬 r (f x)) →
          RFun 𝒫 𝒬 (vclo ρ t) f

data RPair {P Q : Type} (𝒫 : UVal → P → Type) (𝒬 : UVal → Q → Type) :
           UVal → P × Q → Type where
  r-pair : ∀ {v w x y} → 𝒫 v x → 𝒬 w y → RPair 𝒫 𝒬 (vpair v w) (x , y)

data RSum {P Q : Type} (𝒫 : UVal → P → Type) (𝒬 : UVal → Q → Type) :
          UVal → P ⊎ Q → Type where
  r-inl : ∀ {v x} → 𝒫 v x → RSum 𝒫 𝒬 (vinl v) (inl x)
  r-inr : ∀ {v y} → 𝒬 v y → RSum 𝒫 𝒬 (vinr v) (inr y)

-- THE REALISABILITY RELATION. A wrapper is not seen at run time.
𝓡 : (u : Nf [] ★) → UVal → ⟦ u ⟧ⁿ → Type
𝓡 (ne m)       = λ v x → ⊥
𝓡 (nbase b)    = RLit b
𝓡 (ncapp s u)  = λ v x → 𝓡 u v (unbox x)
𝓡 (narr q a b) = RFun (𝓡 a) (𝓡 b)
𝓡 (a n⊗ b)     = RPair (𝓡 a) (𝓡 b)
𝓡 (a n⊕ b)     = RSum (𝓡 a) (𝓡 b)

-- An untyped term, in an environment, evaluates to a realiser of x.
Real : (Z : Ty [] ★) → ∀ {n} → UEnv n → UTm n → ⟦ Z ⟧ → Type
Real Z ρ u x = Σ[ v ∈ UVal ] (ρ ⊢ u ⇓ v) × 𝓡 (nf Z) v x

-- THE DENOTATION OF A TERM TRANSFORMER. The transformer f, from the
-- type X to the type Y, denotes the function g.
Denotes : (X Y : Ty [] ★) → Tr → (⟦ X ⟧ → ⟦ Y ⟧) → Type
Denotes X Y f g =
  ∀ {n} {ρ : UEnv n} (t : Tm n) (x : ⟦ X ⟧) →
  Real X ρ (eraseT t) x → Real Y ρ (eraseT (f t)) (g x)

------------------------------------------------------------------------
-- The path of a coercion.

-- Two convertible types have one interpretation.
nomPath : DefEq X Y → ⟦ X ⟧ ≡ ⟦ Y ⟧
nomPath e = cong ⟦_⟧ⁿ (defEq→nf e)

-- The path of a body, from the path of its parameter. The parameter is
-- used at the role d. Below a type-level function the two instances are
-- convertible (`body-defeq`).
module _ {d : Role} (hn : leR nom d ≡ true → DefEq X Y)
         (hv : leR rep d ≡ true → ⟦ X ⟧ ≡ ⟦ Y ⟧) where

  bodyPath : ∀ β → leR (roleOf β) d ≡ true → ⟦ TB β X ⟧ ≡ ⟦ TB β Y ⟧
  bodyPath bvar        le = hv le
  bodyPath (bbase b)   le = refl
  bodyPath (barr β γ)  le =
    cong₂ (λ P Q → P → Q)
      (bodyPath β (leR-trans _ _ _ (max-upper-l (roleOf β) (roleOf γ)) le))
      (bodyPath γ (leR-trans _ _ _ (max-upper-r (roleOf β) (roleOf γ)) le))
  bodyPath (bprod β γ) le =
    cong₂ _×_
      (bodyPath β (leR-trans _ _ _ (max-upper-l (roleOf β) (roleOf γ)) le))
      (bodyPath γ (leR-trans _ _ _ (max-upper-r (roleOf β) (roleOf γ)) le))
  bodyPath (bsum β γ)  le =
    cong₂ _⊎_
      (bodyPath β (leR-trans _ _ _ (max-upper-l (roleOf β) (roleOf γ)) le))
      (bodyPath γ (leR-trans _ _ _ (max-upper-r (roleOf β) (roleOf γ)) le))
  bodyPath (bfam F β)  le = nomPath (d-papp (body-defeq hn β le))

-- What a coercion at the role r gives: a path at the role
-- representational, and no data at the two other roles.
PathAt : Role → STy → STy → Type₁
PathAt rep τ σ = ⟦ T τ ⟧ ≡ ⟦ T σ ⟧
PathAt nom τ σ = Unit*
PathAt ph  τ σ = Unit*

-- Congruence for a newtype: the path of the body, below the wrapper.
ntPath : ∀ N d → leR (roleOf (body N)) d ≡ true →
         Co d τ σ → PathAt d τ σ → ⟦ T (nt₁ N τ) ⟧ ≡ ⟦ T (nt₁ N σ) ⟧
ntPath N rep le γ p =
  cong Box (bodyPath (λ q → ⊥.rec (false≢true q)) (λ _ → p) (body N) le)
ntPath N nom le γ _ =
  cong Box (bodyPath (λ _ → nominal-defeq γ) (λ _ → nomPath (nominal-defeq γ)) (body N) le)
ntPath N ph  le γ _ =
  cong Box (bodyPath (λ q → ⊥.rec (false≢true q)) (λ q → ⊥.rec (false≢true q)) (body N) le)

pathAt : WellRoled → ∀ r → Co r τ σ → PathAt r τ σ
pathAt wr nom γ = tt*
pathAt wr ph  γ = tt*
pathAt wr rep (c-sym γ)     = sym (pathAt wr rep γ)
pathAt wr rep (c-trans γ δ) = pathAt wr rep γ ∙ pathAt wr rep δ
pathAt wr rep (c-sub γ)     = nomPath (nominal-defeq γ)
pathAt wr rep (c-arr γ δ)   = cong₂ (λ P Q → P → Q) (pathAt wr rep γ) (pathAt wr rep δ)
pathAt wr rep (c-prod γ δ)  = cong₂ _×_ (pathAt wr rep γ) (pathAt wr rep δ)
pathAt wr rep (c-sum γ δ)   = cong₂ _⊎_ (pathAt wr rep γ) (pathAt wr rep δ)
pathAt wr rep (c-nt₁ N γ)   =
  ntPath N (mulG rep (role N)) (wr N) γ (pathAt wr (mulG rep (role N)) γ)
-- THE NEWTYPE AXIOMS: the path from `ua`.
pathAt wr rep (c-ax₀ N)     =
  subst (λ Z → ⟦ T (nt₀ N) ⟧ ≡ ⟦ Z ⟧) (sym (T-embE (rep₀ N))) (ua unboxEquiv)
pathAt wr rep (c-ax₁ N τ)   =
  subst (λ Z → ⟦ T (nt₁ N τ) ⟧ ≡ ⟦ Z ⟧) (sym (T-inst (body N) τ)) (ua unboxEquiv)

-- THE PATH OF A REPRESENTATIONAL COERCION.
pathOf : WellRoled → Co rep τ σ → ⟦ T τ ⟧ ≡ ⟦ T σ ⟧
pathOf wr γ = pathAt wr rep γ

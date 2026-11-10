{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Stage 8. Coercions at open types: proofs.
--
--   1. The translation of types commutes with instantiation.
--   2. Instantiation does not change a trope operation. So one open
--      term is not the unwrap of a newtype at each instance of a type
--      variable.
--   3. The translation of an open coercion is typed. The proof has the
--      shape of the proof of Stage 4 (`Wager.Trans.Typing`), with the
--      types in Δ.
--   4. Each closed instance of the translation of an open coercion is
--      the translation of the instance, as a term.
open import Cubical.Foundations.Prelude
open import Wager.FC.Signature
open import Wager.Grade.Algebra
import Wager.Trans.Scheme

module Wager.Poly.CoercionProofs
  (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
  {R : Type} (ops : GradeOps R) where

open import Cubical.Data.Bool.Base using (true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)
open import Cubical.Data.List.Base using (_++_)

open import Wager.Grade.Finite using (false≢true)
open import Wager.Role.Role
open import Wager.FC.Types SS hiding (inst)
open import Wager.FC.Coercion SS
open import Wager.Trans.Target SS Sc ops
open import Wager.Trans.Nominal SS Sc ops using (nominal-defeq; T-inst; T-embE)
open import Wager.Trans.Coercion SS Sc ops
  using ( Tm; Tr; Iso; fwd; bwd; idIso; swapIso; compIso; arrMap; arrIso
        ; prodMap; prodIso; sumMap; sumIso; stepIso; bodyIso; ntIso; coI; coerceT )
import Wager.L2.Term tSig tTSig as C
import Wager.Trans.Typing
open import Wager.L1.Conversion tSig
open import Wager.Poly.Coercion SS Sc ops
open import Wager.Poly.Typing tSig tTSig ops
  using ( Usage; 0ᵘ; _+ᵘ_; _·ᵘ_; _▹_; unit; Cxᵖ; _▹ᵖ_; _▸_⊢ᵖ_∶_
        ; t-var; t-lam; t-app; t-pair; t-letp; t-inj₁; t-inj₂; t-case
        ; t-step; t-conv )
open import Wager.Poly.Proofs tSig tTSig ops using (sub-⇑; ⇑-closed)
open import Wager.Poly.CoercionStatements SS Sc ops
open GradeOps ops

private
  variable
    n : ℕ
    Δ : Ctx

------------------------------------------------------------------------
-- 1. Types.

-- A closed type does not change under an instantiation.
private
  cl : (s : TySub [] Δ) (X : Ty [] ★) → sub s (⇑ X) ≡ X
  cl s X = sub-⇑ s X ∙ ⇑-closed X

t8-type-instance : T8-Type-Instance
t8-type-instance (ovar x) ρ s ag = ag x
t8-type-instance (clo τ)  ρ s ag = cl s (T τ)
t8-type-instance (θ ⇒ᵒ φ) ρ s ag =
  cong₂ (arr 𝟙) (t8-type-instance θ ρ s ag) (t8-type-instance φ ρ s ag)
t8-type-instance (θ ×ᵒ φ) ρ s ag =
  cong₂ _⊗_ (t8-type-instance θ ρ s ag) (t8-type-instance φ ρ s ag)
t8-type-instance (θ +ᵒ φ) ρ s ag =
  cong₂ _⊕_ (t8-type-instance θ ρ s ag) (t8-type-instance φ ρ s ag)

------------------------------------------------------------------------
-- 2. Trope operations.

t8-ops-rigid : T8-Ops-Rigid
t8-ops-rigid s (tvar i)     = refl
t8-ops-rigid s (tlam q A b) = t8-ops-rigid s b
t8-ops-rigid s (tapp f a)   = cong₂ _++_ (t8-ops-rigid s f) (t8-ops-rigid s a)
t8-ops-rigid s (pair t u)   = cong₂ _++_ (t8-ops-rigid s t) (t8-ops-rigid s u)
t8-ops-rigid s (letp t b)   = cong₂ _++_ (t8-ops-rigid s t) (t8-ops-rigid s b)
t8-ops-rigid s (inj₁ t)     = t8-ops-rigid s t
t8-ops-rigid s (inj₂ t)     = t8-ops-rigid s t
t8-ops-rigid s (case t l r) =
  cong₂ _++_ (t8-ops-rigid s t) (cong₂ _++_ (t8-ops-rigid s l) (t8-ops-rigid s r))
t8-ops-rigid s (lit ℓ)      = refl
t8-ops-rigid s (step o t)   = cong (o ∷_) (t8-ops-rigid s t)

private
  -- The source type in the first operation of a list, when the
  -- operation is on an instance of a newtype with a parameter.
  firstArg : STy → List C.Op → STy
  firstArg d ((_ , inr (_ , τ)) ∷ _) = τ
  firstArg d _                       = d

t8-no-uniform-unwrap : T8-No-Uniform-Unwrap
t8-no-uniform-unwrap N τ₁ τ₂ t s₁ s₂ p₁ p₂ =
  cong (firstArg τ₁)
    (sym (cong opsOf p₁) ∙ t8-ops-rigid s₁ t ∙ sym (t8-ops-rigid s₂ t) ∙ cong opsOf p₂)

------------------------------------------------------------------------
-- 3. Typing, for the laws of a grade algebra.

module Typed (laws : GradeLaws ops) (wr : WellRoled) where
  open GradeLaws laws
  private
    GA : GradeAlgebra R
    GA = record { ops = ops ; laws = laws }
  open Wager.Trans.Typing SS Sc GA using (body-defeq)

  private
    castUᵖ : {γ γ' : Usage n} {Γ : Cxᵖ Δ n} {t : Tmᵖ Δ n} {A : Ty Δ ★} →
             γ ≡ γ' → γ ▸ Γ ⊢ᵖ t ∶ A → γ' ▸ Γ ⊢ᵖ t ∶ A
    castUᵖ {Γ = Γ} {t} {A} p d = subst (λ z → z ▸ Γ ⊢ᵖ t ∶ A) p d

  -- A transformer that maps a term of the type X to a term of the type
  -- Y, with the same usage vector.
  TyTrᵖ : (X Y : Ty Δ ★) → Trᵖ Δ → Type
  TyTrᵖ {Δ} X Y f = ∀ {n} {γ : Usage n} {Γ : Cxᵖ Δ n} {t : Tmᵖ Δ n} →
                    γ ▸ Γ ⊢ᵖ t ∶ X → γ ▸ Γ ⊢ᵖ f t ∶ Y

  IsoTypedᵖ : Ty Δ ★ → Ty Δ ★ → Isoᵖ Δ → Type
  IsoTypedᵖ X Y i = TyTrᵖ X Y (fwdᵖ i) × TyTrᵖ Y X (bwdᵖ i)

  module _ {Δ : Ctx} where
    private
      variable
        X Y Z X' Y' : Ty Δ ★

    id-typedᵖ : DefEq X Y → IsoTypedᵖ X Y idIsoᵖ
    id-typedᵖ e = (λ d → t-conv d e) , (λ d → t-conv d (d-sym e))

    swap-typedᵖ : ∀ {i} → IsoTypedᵖ X Y i → IsoTypedᵖ Y X (swapIsoᵖ i)
    swap-typedᵖ (f , g) = g , f

    comp-typedᵖ : ∀ {i j} → IsoTypedᵖ X Y i → IsoTypedᵖ Y Z j →
                  IsoTypedᵖ X Z (compIsoᵖ i j)
    comp-typedᵖ (f , g) (f' , g') = (λ d → f' (f d)) , (λ d → g (g' d))

    arrMap-typedᵖ : ∀ {h g : Trᵖ Δ} → TyTrᵖ X' X h → TyTrᵖ Y Y' g →
                    TyTrᵖ (arr 𝟙 X Y) (arr 𝟙 X' Y') (arrMapᵖ (arr 𝟙 X Y) X' h g)
    arrMap-typedᵖ th tg {γ = γ} d =
      castUᵖ (funExt λ i → zero-add (𝟙 · γ i) ∙ one-mul (γ i))
        (t-app
          (t-lam {γ = 0ᵘ}
            (t-lam {γ = 0ᵘ ▹ 𝟙}
              (castUᵖ eq (tg (t-app (t-var (suc zero)) (th (t-var zero)))))))
          d)
      where
        eq : ∀ {n} → (unit {n = suc (suc n)} (suc zero) +ᵘ (𝟙 ·ᵘ unit zero)) ≡ (0ᵘ ▹ 𝟙 ▹ 𝟙)
        eq = funExt λ { zero          → zero-add (𝟙 · 𝟙) ∙ one-mul 𝟙
                      ; (suc zero)    → cong (𝟙 +_) (mul-zero 𝟙) ∙ add-zero 𝟙
                      ; (suc (suc i)) → cong (𝟘 +_) (mul-zero 𝟙) ∙ add-zero 𝟘 }

    arrIso-typedᵖ : ∀ {i j} → IsoTypedᵖ X X' i → IsoTypedᵖ Y Y' j →
                    IsoTypedᵖ (arr 𝟙 X Y) (arr 𝟙 X' Y') (arrIsoᵖ X X' Y Y' i j)
    arrIso-typedᵖ (f , g) (f' , g') = arrMap-typedᵖ g f' , arrMap-typedᵖ f g'

    prodMap-typedᵖ : ∀ {f g : Trᵖ Δ} → TyTrᵖ X X' f → TyTrᵖ Y Y' g →
                     TyTrᵖ (X ⊗ Y) (X' ⊗ Y') (prodMapᵖ f g)
    prodMap-typedᵖ tf tg {γ = γ} d =
      castUᵖ (funExt λ i → add-zero (γ i))
        (t-letp {δ = 0ᵘ} d
          (castUᵖ eq (t-pair (tf (t-var (suc zero))) (tg (t-var zero)))))
      where
        eq : ∀ {n} → (unit {n = suc (suc n)} (suc zero) +ᵘ unit zero) ≡ (0ᵘ ▹ 𝟙 ▹ 𝟙)
        eq = funExt λ { zero          → zero-add 𝟙
                      ; (suc zero)    → add-zero 𝟙
                      ; (suc (suc i)) → add-zero 𝟘 }

    prodIso-typedᵖ : ∀ {i j} → IsoTypedᵖ X X' i → IsoTypedᵖ Y Y' j →
                     IsoTypedᵖ (X ⊗ Y) (X' ⊗ Y') (prodIsoᵖ i j)
    prodIso-typedᵖ (f , g) (f' , g') = prodMap-typedᵖ f f' , prodMap-typedᵖ g g'

    sumMap-typedᵖ : ∀ {f g : Trᵖ Δ} → TyTrᵖ X X' f → TyTrᵖ Y Y' g →
                    TyTrᵖ (X ⊕ Y) (X' ⊕ Y') (sumMapᵖ f g)
    sumMap-typedᵖ tf tg {γ = γ} d =
      castUᵖ (funExt λ i → add-zero (γ i))
        (t-case {δ = 0ᵘ} d (t-inj₁ (tf (t-var zero))) (t-inj₂ (tg (t-var zero))))

    sumIso-typedᵖ : ∀ {i j} → IsoTypedᵖ X X' i → IsoTypedᵖ Y Y' j →
                    IsoTypedᵖ (X ⊕ Y) (X' ⊕ Y') (sumIsoᵖ i j)
    sumIso-typedᵖ (f , g) (f' , g') = sumMap-typedᵖ f f' , sumMap-typedᵖ g g'

    -- The two trope transitions of a newtype instance, by `t-step`.
    step-typedᵖ : (x : Inst) →
                  IsoTypedᵖ {Δ} (⇑ (capp (stateOf x) (carrierOf x))) (⇑ (carrierOf x))
                            (stepIsoᵖ x)
    step-typedᵖ x = (λ d → t-step (unwrap , x) d) , (λ d → t-step (wrap , x) d)

    -- The map of a body, for a parameter that is used at the role d.
    module _ {d : Role} {U V : Ty [] ★} (hn : leR nom d ≡ true → DefEq U V)
             {i : Isoᵖ Δ} (hv : leR rep d ≡ true → IsoTypedᵖ (⇑ U) (⇑ V) i) where

      body-typedᵖ : ∀ β → leR (roleOf β) d ≡ true →
                    IsoTypedᵖ (⇑ (TB β U)) (⇑ (TB β V)) (bodyIsoᵖ β U V i)
      body-typedᵖ bvar        le = hv le
      body-typedᵖ (bbase b)   le = id-typedᵖ d-refl
      body-typedᵖ (barr β γ)  le =
        arrIso-typedᵖ (body-typedᵖ β (leR-trans _ _ _ (max-upper-l (roleOf β) (roleOf γ)) le))
                      (body-typedᵖ γ (leR-trans _ _ _ (max-upper-r (roleOf β) (roleOf γ)) le))
      body-typedᵖ (bprod β γ) le =
        prodIso-typedᵖ (body-typedᵖ β (leR-trans _ _ _ (max-upper-l (roleOf β) (roleOf γ)) le))
                       (body-typedᵖ γ (leR-trans _ _ _ (max-upper-r (roleOf β) (roleOf γ)) le))
      body-typedᵖ (bsum β γ)  le =
        sumIso-typedᵖ (body-typedᵖ β (leR-trans _ _ _ (max-upper-l (roleOf β) (roleOf γ)) le))
                      (body-typedᵖ γ (leR-trans _ _ _ (max-upper-r (roleOf β) (roleOf γ)) le))
      body-typedᵖ (bfam F β)  le =
        id-typedᵖ (DefEq-ren εᵣ (d-papp (body-defeq hn β le)))

    -- What the translation of a closed coercion at the role r gives.
    SemTyᵖ : Role → STy → STy → Isoᵖ Δ → Type
    SemTyᵖ nom τ σ i = DefEq (T τ) (T σ)
    SemTyᵖ rep τ σ i = IsoTypedᵖ (⇑ (T τ)) (⇑ (T σ)) i
    SemTyᵖ ph  τ σ i = Unit

    private
      nt-wrapᵖ : ∀ N {τ σ} {i : Isoᵖ Δ} →
                 IsoTypedᵖ (⇑ (TB (body N) (T τ))) (⇑ (TB (body N) (T σ)))
                           (bodyIsoᵖ (body N) (T τ) (T σ) i) →
                 IsoTypedᵖ (⇑ (T (nt₁ N τ))) (⇑ (T (nt₁ N σ))) (ntIsoᵖ N τ σ i)
      nt-wrapᵖ N {τ} {σ} (f , g) =
          (λ d → t-step (wrap , inr (N , σ)) (f (t-step (unwrap , inr (N , τ)) d)))
        , (λ d → t-step (wrap , inr (N , τ)) (g (t-step (unwrap , inr (N , σ)) d)))

      nt-typedᵖ : ∀ N d {τ σ} → leR (roleOf (body N)) d ≡ true →
                  (γ : Co d τ σ) → SemTyᵖ d τ σ (coIᵖ {Δ = Δ} d γ) →
                  IsoTypedᵖ (⇑ (T (nt₁ N τ))) (⇑ (T (nt₁ N σ))) (ntIsoᵖ N τ σ (coIᵖ {Δ = Δ} d γ))
      nt-typedᵖ N rep le γ sem =
        nt-wrapᵖ N (body-typedᵖ (λ p → ⊥.rec (false≢true p)) {i = coIᵖ rep γ} (λ _ → sem) (body N) le)
      nt-typedᵖ N nom le γ sem =
        nt-wrapᵖ N (body-typedᵖ (λ _ → sem) {i = idIsoᵖ}
                                (λ _ → id-typedᵖ (DefEq-ren εᵣ sem)) (body N) le)
      nt-typedᵖ N ph  le γ sem =
        nt-wrapᵖ N (body-typedᵖ (λ p → ⊥.rec (false≢true p)) {i = idIsoᵖ}
                                (λ p → ⊥.rec (false≢true p)) (body N) le)

    coIᵖ-typed : ∀ r {τ σ} (γ : Co r τ σ) → SemTyᵖ r τ σ (coIᵖ {Δ = Δ} r γ)
    coIᵖ-typed nom γ = nominal-defeq γ
    coIᵖ-typed ph  γ = tt
    coIᵖ-typed rep (c-sym γ)     = swap-typedᵖ (coIᵖ-typed rep γ)
    coIᵖ-typed rep (c-trans γ δ) = comp-typedᵖ (coIᵖ-typed rep γ) (coIᵖ-typed rep δ)
    coIᵖ-typed rep (c-sub γ)     = id-typedᵖ (DefEq-ren εᵣ (nominal-defeq γ))
    coIᵖ-typed rep (c-arr γ δ)   = arrIso-typedᵖ (coIᵖ-typed rep γ) (coIᵖ-typed rep δ)
    coIᵖ-typed rep (c-prod γ δ)  = prodIso-typedᵖ (coIᵖ-typed rep γ) (coIᵖ-typed rep δ)
    coIᵖ-typed rep (c-sum γ δ)   = sumIso-typedᵖ (coIᵖ-typed rep γ) (coIᵖ-typed rep δ)
    coIᵖ-typed rep (c-nt₁ N γ)   =
      nt-typedᵖ N (mulG rep (role N)) (wr N) γ (coIᵖ-typed (mulG rep (role N)) γ)
    coIᵖ-typed rep (c-ax₀ N)     =
      subst (λ Z → IsoTypedᵖ (⇑ (T (nt₀ N))) (⇑ Z) (stepIsoᵖ (inl N)))
            (sym (T-embE (rep₀ N))) (step-typedᵖ (inl N))
    coIᵖ-typed rep (c-ax₁ N τ)   =
      subst (λ Z → IsoTypedᵖ (⇑ (T (nt₁ N τ))) (⇑ Z) (stepIsoᵖ (inr (N , τ))))
            (sym (T-inst (body N) τ)) (step-typedᵖ (inr (N , τ)))

    -- The typing of the translation of an open coercion.
    coIᵒ-typed : ∀ {θ φ : OTy Δ} (c : Coᵒ θ φ) → IsoTypedᵖ (Tᵒ θ) (Tᵒ φ) (coIᵒ c)
    coIᵒ-typed o-refl        = id-typedᵖ d-refl
    coIᵒ-typed (o-clo γ)     = coIᵖ-typed rep γ
    coIᵒ-typed (o-sym c)     = swap-typedᵖ (coIᵒ-typed c)
    coIᵒ-typed (o-trans c d) = comp-typedᵖ (coIᵒ-typed c) (coIᵒ-typed d)
    coIᵒ-typed (o-arr c d)   = arrIso-typedᵖ (coIᵒ-typed c) (coIᵒ-typed d)
    coIᵒ-typed (o-prod c d)  = prodIso-typedᵖ (coIᵒ-typed c) (coIᵒ-typed d)
    coIᵒ-typed (o-sum c d)   = sumIso-typedᵖ (coIᵒ-typed c) (coIᵒ-typed d)

t8-coercion-typed : T8-Coercion-Typed
t8-coercion-typed laws wr c Γ =
  t-lam {γ = 0ᵘ} (fst (Typed.coIᵒ-typed laws wr c) (t-var zero))

------------------------------------------------------------------------
-- 4. Instances. The instantiation s is fixed.

module Instance {Δ : Ctx} (s : TySub [] Δ) where

  -- The closed instance of an open term.
  ⟪_⟫ : Tmᵖ Δ n → Tm n
  ⟪ t ⟫ = ⌊ inst s t ⌋

  -- A transformer of open terms and a transformer of closed terms
  -- that agree on each instance.
  Nat : Tr → Trᵖ Δ → Type
  Nat f fᵖ = ∀ {n} (t : Tmᵖ Δ n) → ⟪ fᵖ t ⟫ ≡ f ⟪ t ⟫

  -- A record, so that Agda finds the two isomorphisms from the type.
  infixr 4 _,ⁿ_
  record NatIso (i : Iso) (iᵖ : Isoᵖ Δ) : Type where
    constructor _,ⁿ_
    field
      natF : Nat (fwd i) (fwdᵖ iᵖ)
      natB : Nat (bwd i) (bwdᵖ iᵖ)
  open NatIso

  id-nat : NatIso idIso idIsoᵖ
  id-nat = (λ t → refl) ,ⁿ (λ t → refl)

  swap-nat : ∀ {i iᵖ} → NatIso i iᵖ → NatIso (swapIso i) (swapIsoᵖ iᵖ)
  swap-nat (f ,ⁿ g) = g ,ⁿ f

  comp-nat : ∀ {i iᵖ j jᵖ} → NatIso i iᵖ → NatIso j jᵖ →
             NatIso (compIso i j) (compIsoᵖ iᵖ jᵖ)
  comp-nat {i} {iᵖ} {j} {jᵖ} (f ,ⁿ g) (f' ,ⁿ g') =
      (λ t → f' (fwdᵖ iᵖ t) ∙ cong (λ z → fwd j z) (f t))
    ,ⁿ (λ t → g (bwdᵖ jᵖ t) ∙ cong (λ z → bwd i z) (g' t))

  arrMap-nat : ∀ {X A : Ty [] ★} {Xᵖ Aᵖ : Ty Δ ★} {h g : Tr} {hᵖ gᵖ : Trᵖ Δ} →
               sub s Xᵖ ≡ X → sub s Aᵖ ≡ A → Nat h hᵖ → Nat g gᵖ →
               Nat (arrMap X A h g) (arrMapᵖ Xᵖ Aᵖ hᵖ gᵖ)
  arrMap-nat {h = h} {g} {hᵖ} {gᵖ} pX pA nh ng t i =
    C.tapp (C.tlam 𝟙 (pX i) (C.tlam 𝟙 (pA i) (inner i))) ⟪ t ⟫
    where
    inner : ⟪ gᵖ (tapp (tvar (suc zero)) (hᵖ (tvar zero))) ⟫
            ≡ g (C.tapp (C.tvar (suc zero)) (h (C.tvar zero)))
    inner = ng (tapp (tvar (suc zero)) (hᵖ (tvar zero)))
            ∙ cong (λ z → g (C.tapp (C.tvar (suc zero)) z)) (nh (tvar zero))

  arrIso-nat : ∀ {A A' B B' : Ty [] ★} {Aᵖ A'ᵖ Bᵖ B'ᵖ : Ty Δ ★} {i iᵖ j jᵖ} →
               sub s Aᵖ ≡ A → sub s A'ᵖ ≡ A' → sub s Bᵖ ≡ B → sub s B'ᵖ ≡ B' →
               NatIso i iᵖ → NatIso j jᵖ →
               NatIso (arrIso A A' B B' i j) (arrIsoᵖ Aᵖ A'ᵖ Bᵖ B'ᵖ iᵖ jᵖ)
  arrIso-nat {Aᵖ = Aᵖ} {A'ᵖ} {Bᵖ} {B'ᵖ} {i} {iᵖ} {j} {jᵖ} pA pA' pB pB' (f ,ⁿ g) (f' ,ⁿ g') =
      arrMap-nat {Xᵖ = arr 𝟙 Aᵖ Bᵖ} {Aᵖ = A'ᵖ}
                 {h = bwd i} {g = fwd j} {hᵖ = bwdᵖ iᵖ} {gᵖ = fwdᵖ jᵖ}
                 (cong₂ (arr 𝟙) pA pB) pA' g f'
    ,ⁿ arrMap-nat {Xᵖ = arr 𝟙 A'ᵖ B'ᵖ} {Aᵖ = Aᵖ}
                  {h = fwd i} {g = bwd j} {hᵖ = fwdᵖ iᵖ} {gᵖ = bwdᵖ jᵖ}
                  (cong₂ (arr 𝟙) pA' pB') pA f g'

  prodMap-nat : ∀ {f g : Tr} {fᵖ gᵖ : Trᵖ Δ} → Nat f fᵖ → Nat g gᵖ →
                Nat (prodMap f g) (prodMapᵖ fᵖ gᵖ)
  prodMap-nat nf ng t i =
    C.letp ⟪ t ⟫ (C.pair (nf (tvar (suc zero)) i) (ng (tvar zero) i))

  prodIso-nat : ∀ {i iᵖ j jᵖ} → NatIso i iᵖ → NatIso j jᵖ →
                NatIso (prodIso i j) (prodIsoᵖ iᵖ jᵖ)
  prodIso-nat {i} {iᵖ} {j} {jᵖ} (f ,ⁿ g) (f' ,ⁿ g') =
      prodMap-nat {f = fwd i} {g = fwd j} {fᵖ = fwdᵖ iᵖ} {gᵖ = fwdᵖ jᵖ} f f'
    ,ⁿ prodMap-nat {f = bwd i} {g = bwd j} {fᵖ = bwdᵖ iᵖ} {gᵖ = bwdᵖ jᵖ} g g'

  sumMap-nat : ∀ {f g : Tr} {fᵖ gᵖ : Trᵖ Δ} → Nat f fᵖ → Nat g gᵖ →
               Nat (sumMap f g) (sumMapᵖ fᵖ gᵖ)
  sumMap-nat nf ng t i =
    C.case ⟪ t ⟫ (C.inj₁ (nf (tvar zero) i)) (C.inj₂ (ng (tvar zero) i))

  sumIso-nat : ∀ {i iᵖ j jᵖ} → NatIso i iᵖ → NatIso j jᵖ →
               NatIso (sumIso i j) (sumIsoᵖ iᵖ jᵖ)
  sumIso-nat {i} {iᵖ} {j} {jᵖ} (f ,ⁿ g) (f' ,ⁿ g') =
      sumMap-nat {f = fwd i} {g = fwd j} {fᵖ = fwdᵖ iᵖ} {gᵖ = fwdᵖ jᵖ} f f'
    ,ⁿ sumMap-nat {f = bwd i} {g = bwd j} {fᵖ = bwdᵖ iᵖ} {gᵖ = bwdᵖ jᵖ} g g'

  step-nat : (x : Inst) → NatIso (stepIso x) (stepIsoᵖ x)
  step-nat x = (λ t → refl) ,ⁿ (λ t → refl)

  body-nat : ∀ β (X Y : Ty [] ★) {i iᵖ} → NatIso i iᵖ →
             NatIso (bodyIso β X Y i) (bodyIsoᵖ β X Y iᵖ)
  body-nat bvar        X Y ni = ni
  body-nat (bbase b)   X Y ni = id-nat
  body-nat (barr β γ)  X Y ni =
    arrIso-nat (cl s (TB β X)) (cl s (TB β Y)) (cl s (TB γ X)) (cl s (TB γ Y))
               (body-nat β X Y ni) (body-nat γ X Y ni)
  body-nat (bprod β γ) X Y ni = prodIso-nat (body-nat β X Y ni) (body-nat γ X Y ni)
  body-nat (bsum β γ)  X Y ni = sumIso-nat (body-nat β X Y ni) (body-nat γ X Y ni)
  body-nat (bfam F β)  X Y ni = id-nat

  nt-nat : ∀ N τ σ {i iᵖ} → NatIso i iᵖ → NatIso (ntIso N τ σ i) (ntIsoᵖ N τ σ iᵖ)
  nt-nat N τ σ ni =
      (λ t → cong (C.step (wrap , inr (N , σ))) (natF b (step (unwrap , inr (N , τ)) t)))
    ,ⁿ (λ t → cong (C.step (wrap , inr (N , τ))) (natB b (step (unwrap , inr (N , σ)) t)))
    where b = body-nat (body N) (T τ) (T σ) ni

  coIᵖ-nat : ∀ r {τ σ} (γ : Co r τ σ) → NatIso (coI r γ) (coIᵖ r γ)
  coIᵖ-nat nom γ = id-nat
  coIᵖ-nat ph  γ = id-nat
  coIᵖ-nat rep (c-sym γ)     = swap-nat (coIᵖ-nat rep γ)
  coIᵖ-nat rep (c-trans γ δ) = comp-nat (coIᵖ-nat rep γ) (coIᵖ-nat rep δ)
  coIᵖ-nat rep (c-sub γ)     = id-nat
  coIᵖ-nat rep (c-arr {τ = τ} {τ' = τ'} {σ = σ} {σ' = σ'} γ δ) =
    arrIso-nat (cl s (T τ)) (cl s (T τ')) (cl s (T σ)) (cl s (T σ'))
               (coIᵖ-nat rep γ) (coIᵖ-nat rep δ)
  coIᵖ-nat rep (c-prod γ δ)  = prodIso-nat (coIᵖ-nat rep γ) (coIᵖ-nat rep δ)
  coIᵖ-nat rep (c-sum γ δ)   = sumIso-nat (coIᵖ-nat rep γ) (coIᵖ-nat rep δ)
  coIᵖ-nat rep (c-nt₁ {τ = τ} {σ = σ} N γ) =
    nt-nat N τ σ (coIᵖ-nat (mulG rep (role N)) γ)
  coIᵖ-nat rep (c-ax₀ N)     = step-nat (inl N)
  coIᵖ-nat rep (c-ax₁ N τ)   = step-nat (inr (N , τ))

  module _ (ρ : SInst Δ) (ag : Agrees s ρ) where

    coIᵒ-nat : ∀ {θ φ : OTy Δ} (c : Coᵒ θ φ) → NatIso (coI rep (c ⟦ ρ ⟧ᶜ)) (coIᵒ c)
    coIᵒ-nat o-refl        = id-nat
    coIᵒ-nat (o-clo γ)     = coIᵖ-nat rep γ
    coIᵒ-nat (o-sym c)     = swap-nat (coIᵒ-nat c)
    coIᵒ-nat (o-trans c d) = comp-nat (coIᵒ-nat c) (coIᵒ-nat d)
    coIᵒ-nat (o-arr {θ = θ} {θ' = θ'} {φ = φ} {φ' = φ'} c d) =
      arrIso-nat (t8-type-instance θ ρ s ag) (t8-type-instance θ' ρ s ag)
                 (t8-type-instance φ ρ s ag) (t8-type-instance φ' ρ s ag)
                 (coIᵒ-nat c) (coIᵒ-nat d)
    coIᵒ-nat (o-prod c d)  = prodIso-nat (coIᵒ-nat c) (coIᵒ-nat d)
    coIᵒ-nat (o-sum c d)   = sumIso-nat (coIᵒ-nat c) (coIᵒ-nat d)

t8-coercion-instance : T8-Coercion-Instance
t8-coercion-instance {θ = θ} c ρ s ag i =
  C.tlam 𝟙 (t8-type-instance θ ρ s ag i)
         (Instance.NatIso.natF (Instance.coIᵒ-nat s ρ ag c) (tvar zero) i)

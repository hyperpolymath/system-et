{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on coercions and on typed terms.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The translation preserves typing (Stage 4, the typing part of T5).
--
--   1. The transformer of a representational coercion maps a term of
--      the type `T τ` to a term of the type `T σ`, with the same usage
--      vector. This holds in each grade algebra: a coercion uses each
--      variable one time.
--   2. The translation of a source term of the type τ has the type
--      `T τ`. This holds in each grade algebra in which the grade 𝟙 is
--      unrestricted (𝟘 ≤ 𝟙 and 𝟙 + 𝟙 ≤ 𝟙), because a source term has no
--      usage discipline.
open import Cubical.Foundations.Prelude
open import Wager.FC.Signature
open import Wager.Grade.Algebra
import Wager.Trans.Scheme

module Wager.Trans.Typing
  (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
  {R : Type} (A : GradeAlgebra R) where

open import Cubical.Data.Bool.Base using (true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)

open import Wager.Grade.Finite using (false≢true)
open import Wager.Role.Role
open GradeAlgebra A
open import Wager.FC.Types SS
open import Wager.FC.Coercion SS
open import Wager.FC.Term SS
open import Wager.FC.RoleSoundness SS using (nomZ-l; nomZ-r; nomZ-idem)
open import Wager.Trans.Target SS Sc ops
open import Wager.Trans.Nominal SS Sc ops
open import Wager.Trans.Coercion SS Sc ops
open import Wager.L1.Conversion tSig
open import Wager.L2.Typing tSig tTSig ops
  using ( Usage; 0ᵘ; _+ᵘ_; _·ᵘ_; _≤ᵘ_; _▹_; unit; Cx; _▹ᶜ_; _▸_⊢_∶_
        ; t-var; t-lam; t-app; t-pair; t-letp; t-inj₁; t-inj₂; t-case
        ; t-lit; t-step; t-conv; t-sub )
open import Wager.L2.Renaming tSig tTSig A using (castU; castT)

private
  variable
    n : ℕ
    X Y Z X' Y' : Ty [] ★

-- A transformer that maps a term of the type X to a term of the type
-- Y, with the same usage vector.
TyTr : (X Y : Ty [] ★) → Tr → Type
TyTr X Y f = ∀ {n} {γ : Usage n} {Γ : Cx n} {t : Tm n} →
             γ ▸ Γ ⊢ t ∶ X → γ ▸ Γ ⊢ f t ∶ Y

IsoTyped : Ty [] ★ → Ty [] ★ → Iso → Type
IsoTyped X Y i = TyTr X Y (fwd i) × TyTr Y X (bwd i)

------------------------------------------------------------------------
-- The typing of each building block.

id-typed : DefEq X Y → IsoTyped X Y idIso
id-typed e = (λ d → t-conv d e) , (λ d → t-conv d (d-sym e))

swap-typed : ∀ {i} → IsoTyped X Y i → IsoTyped Y X (swapIso i)
swap-typed (f , g) = g , f

comp-typed : ∀ {i j} → IsoTyped X Y i → IsoTyped Y Z j → IsoTyped X Z (compIso i j)
comp-typed (f , g) (f' , g') = (λ d → f' (f d)) , (λ d → g (g' d))

arrMap-typed : ∀ {h g : Tr} → TyTr X' X h → TyTr Y Y' g →
               TyTr (arr 𝟙 X Y) (arr 𝟙 X' Y') (arrMap (arr 𝟙 X Y) X' h g)
arrMap-typed th tg {γ = γ} d =
  castU (funExt λ i → zero-add (𝟙 · γ i) ∙ one-mul (γ i))
    (t-app
      (t-lam {γ = 0ᵘ}
        (t-lam {γ = 0ᵘ ▹ 𝟙}
          (castU eq (tg (t-app (t-var (suc zero)) (th (t-var zero)))))))
      d)
  where
    eq : ∀ {n} → (unit {n = suc (suc n)} (suc zero) +ᵘ (𝟙 ·ᵘ unit zero)) ≡ (0ᵘ ▹ 𝟙 ▹ 𝟙)
    eq = funExt λ { zero          → zero-add (𝟙 · 𝟙) ∙ one-mul 𝟙
                  ; (suc zero)    → cong (𝟙 +_) (mul-zero 𝟙) ∙ add-zero 𝟙
                  ; (suc (suc i)) → cong (𝟘 +_) (mul-zero 𝟙) ∙ add-zero 𝟘 }

arrIso-typed : ∀ {i j} → IsoTyped X X' i → IsoTyped Y Y' j →
               IsoTyped (arr 𝟙 X Y) (arr 𝟙 X' Y') (arrIso X X' Y Y' i j)
arrIso-typed (f , g) (f' , g') = arrMap-typed g f' , arrMap-typed f g'

prodMap-typed : ∀ {f g : Tr} → TyTr X X' f → TyTr Y Y' g →
                TyTr (X ⊗ Y) (X' ⊗ Y') (prodMap f g)
prodMap-typed tf tg {γ = γ} d =
  castU (funExt λ i → add-zero (γ i))
    (t-letp {δ = 0ᵘ} d
      (castU eq (t-pair (tf (t-var (suc zero))) (tg (t-var zero)))))
  where
    eq : ∀ {n} → (unit {n = suc (suc n)} (suc zero) +ᵘ unit zero) ≡ (0ᵘ ▹ 𝟙 ▹ 𝟙)
    eq = funExt λ { zero          → zero-add 𝟙
                  ; (suc zero)    → add-zero 𝟙
                  ; (suc (suc i)) → add-zero 𝟘 }

prodIso-typed : ∀ {i j} → IsoTyped X X' i → IsoTyped Y Y' j →
                IsoTyped (X ⊗ Y) (X' ⊗ Y') (prodIso i j)
prodIso-typed (f , g) (f' , g') = prodMap-typed f f' , prodMap-typed g g'

sumMap-typed : ∀ {f g : Tr} → TyTr X X' f → TyTr Y Y' g →
               TyTr (X ⊕ Y) (X' ⊕ Y') (sumMap f g)
sumMap-typed tf tg {γ = γ} d =
  castU (funExt λ i → add-zero (γ i))
    (t-case {δ = 0ᵘ} d (t-inj₁ (tf (t-var zero))) (t-inj₂ (tg (t-var zero))))

sumIso-typed : ∀ {i j} → IsoTyped X X' i → IsoTyped Y Y' j →
               IsoTyped (X ⊕ Y) (X' ⊕ Y') (sumIso i j)
sumIso-typed (f , g) (f' , g') = sumMap-typed f f' , sumMap-typed g g'

-- The two trope transitions of a newtype instance, by rule `t-step`.
step-typed : (x : Inst) → IsoTyped (capp (stateOf x) (carrierOf x)) (carrierOf x) (stepIso x)
step-typed x = (λ d → t-step (unwrap , x) d) , (λ d → t-step (wrap , x) d)

------------------------------------------------------------------------
-- The map of a body, for a parameter that is used at the role d.

module _ {d : Role} (hn : leR nom d ≡ true → DefEq X Y) where

  -- Below a type-level function the two instances are convertible.
  body-defeq : ∀ β → leR (mulZ nom (roleOf β)) d ≡ true → DefEq (TB β X) (TB β Y)
  body-defeq bvar        le = hn le
  body-defeq (bbase b)   le = d-refl
  body-defeq (barr β γ)  le =
    d-arr (body-defeq β (leR-trans _ _ _ (nomZ-l (roleOf β) (roleOf γ)) le))
          (body-defeq γ (leR-trans _ _ _ (nomZ-r (roleOf β) (roleOf γ)) le))
  body-defeq (bprod β γ) le =
    d-prod (body-defeq β (leR-trans _ _ _ (nomZ-l (roleOf β) (roleOf γ)) le))
           (body-defeq γ (leR-trans _ _ _ (nomZ-r (roleOf β) (roleOf γ)) le))
  body-defeq (bsum β γ)  le =
    d-sum (body-defeq β (leR-trans _ _ _ (nomZ-l (roleOf β) (roleOf γ)) le))
          (body-defeq γ (leR-trans _ _ _ (nomZ-r (roleOf β) (roleOf γ)) le))
  body-defeq (bfam F β)  le =
    d-papp (body-defeq β (subst (λ r → leR r d ≡ true) (nomZ-idem (roleOf β)) le))

  module _ {i : Iso} (hv : leR rep d ≡ true → IsoTyped X Y i) where

    body-typed : ∀ β → leR (roleOf β) d ≡ true →
                 IsoTyped (TB β X) (TB β Y) (bodyIso β X Y i)
    body-typed bvar        le = hv le
    body-typed (bbase b)   le = id-typed d-refl
    body-typed (barr β γ)  le =
      arrIso-typed (body-typed β (leR-trans _ _ _ (max-upper-l (roleOf β) (roleOf γ)) le))
                   (body-typed γ (leR-trans _ _ _ (max-upper-r (roleOf β) (roleOf γ)) le))
    body-typed (bprod β γ) le =
      prodIso-typed (body-typed β (leR-trans _ _ _ (max-upper-l (roleOf β) (roleOf γ)) le))
                    (body-typed γ (leR-trans _ _ _ (max-upper-r (roleOf β) (roleOf γ)) le))
    body-typed (bsum β γ)  le =
      sumIso-typed (body-typed β (leR-trans _ _ _ (max-upper-l (roleOf β) (roleOf γ)) le))
                   (body-typed γ (leR-trans _ _ _ (max-upper-r (roleOf β) (roleOf γ)) le))
    body-typed (bfam F β)  le = id-typed (d-papp (body-defeq β le))

------------------------------------------------------------------------
-- The typing of a translated coercion.

-- What the translation of a coercion at the role r gives.
SemTy : Role → STy → STy → Iso → Type
SemTy nom τ σ i = DefEq (T τ) (T σ)
SemTy rep τ σ i = IsoTyped (T τ) (T σ) i
SemTy ph  τ σ i = Unit

module _ (wr : WellRoled) where

  private
    nt-wrap : ∀ N {τ σ i} →
              IsoTyped (TB (body N) (T τ)) (TB (body N) (T σ)) (bodyIso (body N) (T τ) (T σ) i) →
              IsoTyped (T (nt₁ N τ)) (T (nt₁ N σ)) (ntIso N τ σ i)
    nt-wrap N {τ} {σ} (f , g) =
        (λ d → t-step (wrap , inr (N , σ)) (f (t-step (unwrap , inr (N , τ)) d)))
      , (λ d → t-step (wrap , inr (N , τ)) (g (t-step (unwrap , inr (N , σ)) d)))

    -- Congruence for a newtype. The role check gives: the inferred
    -- role of the body is at most the role d of the premise.
    nt-typed : ∀ N d {τ σ} → leR (roleOf (body N)) d ≡ true →
               (γ : Co d τ σ) → SemTy d τ σ (coI d γ) →
               IsoTyped (T (nt₁ N τ)) (T (nt₁ N σ)) (ntIso N τ σ (coI d γ))
    nt-typed N rep le γ sem =
      nt-wrap N (body-typed (λ p → ⊥.rec (false≢true p)) {i = coI rep γ} (λ _ → sem) (body N) le)
    nt-typed N nom le γ sem =
      nt-wrap N (body-typed (λ _ → sem) {i = idIso} (λ _ → id-typed sem) (body N) le)
    nt-typed N ph  le γ sem =
      nt-wrap N (body-typed (λ p → ⊥.rec (false≢true p)) {i = idIso}
                            (λ p → ⊥.rec (false≢true p)) (body N) le)

  coI-typed : ∀ r {τ σ} (γ : Co r τ σ) → SemTy r τ σ (coI r γ)
  coI-typed nom γ = nominal-defeq γ
  coI-typed ph  γ = tt
  coI-typed rep (c-sym γ)     = swap-typed (coI-typed rep γ)
  coI-typed rep (c-trans γ δ) = comp-typed (coI-typed rep γ) (coI-typed rep δ)
  coI-typed rep (c-sub γ)     = id-typed (nominal-defeq γ)
  coI-typed rep (c-arr γ δ)   = arrIso-typed (coI-typed rep γ) (coI-typed rep δ)
  coI-typed rep (c-prod γ δ)  = prodIso-typed (coI-typed rep γ) (coI-typed rep δ)
  coI-typed rep (c-sum γ δ)   = sumIso-typed (coI-typed rep γ) (coI-typed rep δ)
  coI-typed rep (c-nt₁ N γ)   =
    nt-typed N (mulG rep (role N)) (wr N) γ (coI-typed (mulG rep (role N)) γ)
  coI-typed rep (c-ax₀ N)     =
    subst (λ Z → IsoTyped (T (nt₀ N)) Z (stepIso (inl N)))
          (sym (T-embE (rep₀ N))) (step-typed (inl N))
  coI-typed rep (c-ax₁ N τ)   =
    subst (λ Z → IsoTyped (T (nt₁ N τ)) Z (stepIso (inr (N , τ))))
          (sym (T-inst (body N) τ)) (step-typed (inr (N , τ)))

  -- A representational coercion is an ordinary function of the target.
  coerce-typed : ∀ {τ σ} (γ : Co rep τ σ) {n} (Γ : Cx n) →
                 0ᵘ ▸ Γ ⊢ coerceT γ ∶ arr 𝟙 (T τ) (T σ)
  coerce-typed γ Γ = t-lam {γ = 0ᵘ} (fst (coI-typed rep γ) (t-var zero))

  ----------------------------------------------------------------------
  -- The typing of a translated term, when the grade 𝟙 is unrestricted.

  module _ (u0 : 𝟘 ≤ 𝟙) (u2 : (𝟙 + 𝟙) ≤ 𝟙) where

    private
      Ones : Usage n → Type
      Ones γ = ∀ i → γ i ≡ 𝟙

      ones-ext : {γ : Usage n} → Ones γ → Ones (γ ▹ 𝟙)
      ones-ext o zero    = refl
      ones-ext o (suc i) = o i

      unit-le : (i : Fin n) (γ : Usage n) → Ones γ → unit i ≤ᵘ γ
      unit-le zero    γ o zero    = subst (𝟙 ≤_) (sym (o zero)) (le-refl 𝟙)
      unit-le zero    γ o (suc j) = subst (𝟘 ≤_) (sym (o (suc j))) u0
      unit-le (suc i) γ o zero    = subst (𝟘 ≤_) (sym (o zero)) u0
      unit-le (suc i) γ o (suc j) = unit-le i (λ k → γ (suc k)) (λ k → o (suc k)) j

      zero-le : {γ : Usage n} → Ones γ → 0ᵘ ≤ᵘ γ
      zero-le o i = subst (𝟘 ≤_) (sym (o i)) u0

      dup-le : {γ : Usage n} → Ones γ → (γ +ᵘ γ) ≤ᵘ γ
      dup-le o i = subst (λ x → (x + x) ≤ x) (sym (o i)) u2

      app-le : {γ : Usage n} → Ones γ → (γ +ᵘ (𝟙 ·ᵘ γ)) ≤ᵘ γ
      app-le o i =
        subst (λ x → (x + 𝟙 · x) ≤ x) (sym (o i))
              (subst (λ y → (𝟙 + y) ≤ 𝟙) (sym (one-mul 𝟙)) u2)

      Agree : Cx n → SCx n → Type
      Agree Δ Γ = ∀ i → Δ i ≡ T (Γ i)

      agree-ext : ∀ {Δ : Cx n} {Γ : SCx n} τ → Agree Δ Γ → Agree (Δ ▹ᶜ T τ) (Γ ▹ˢ τ)
      agree-ext τ h zero    = refl
      agree-ext τ h (suc i) = h i

    tr-typed′ : ∀ {Γ : SCx n} {τ} (e : STm Γ τ) (γ : Usage n) (Δ : Cx n) →
                Ones γ → Agree Δ Γ → γ ▸ Δ ⊢ tr e ∶ T τ
    tr-typed′ (svar i) γ Δ o h = t-sub (castT (h i) (t-var i)) (unit-le i γ o)
    tr-typed′ (slam {τ = τ} b) γ Δ o h =
      t-lam (tr-typed′ b (γ ▹ 𝟙) (Δ ▹ᶜ T τ) (ones-ext o) (agree-ext τ h))
    tr-typed′ (sapp f a) γ Δ o h =
      t-sub (t-app (tr-typed′ f γ Δ o h) (tr-typed′ a γ Δ o h)) (app-le o)
    tr-typed′ (spair s t) γ Δ o h =
      t-sub (t-pair (tr-typed′ s γ Δ o h) (tr-typed′ t γ Δ o h)) (dup-le o)
    tr-typed′ (sletp {τ = τ} {σ = σ} s b) γ Δ o h =
      t-sub (t-letp {δ = γ} (tr-typed′ s γ Δ o h)
               (tr-typed′ b (γ ▹ 𝟙 ▹ 𝟙) (Δ ▹ᶜ T τ ▹ᶜ T σ)
                  (ones-ext (ones-ext o)) (agree-ext σ (agree-ext τ h))))
            (dup-le o)
    tr-typed′ (sinl t) γ Δ o h = t-inj₁ (tr-typed′ t γ Δ o h)
    tr-typed′ (sinr t) γ Δ o h = t-inj₂ (tr-typed′ t γ Δ o h)
    tr-typed′ (scase {τ = τ} {σ = σ} s l r) γ Δ o h =
      t-sub (t-case {δ = γ} (tr-typed′ s γ Δ o h)
               (tr-typed′ l (γ ▹ 𝟙) (Δ ▹ᶜ T τ) (ones-ext o) (agree-ext τ h))
               (tr-typed′ r (γ ▹ 𝟙) (Δ ▹ᶜ T σ) (ones-ext o) (agree-ext σ h)))
            (dup-le o)
    tr-typed′ (slit ℓ) γ Δ o h = t-sub (t-lit ℓ) (zero-le o)
    tr-typed′ (cast γ' e) γ Δ o h = fst (coI-typed rep γ') (tr-typed′ e γ Δ o h)

    tr-typed : ∀ {Γ : SCx n} {τ} (e : STm Γ τ) →
               (λ _ → 𝟙) ▸ (λ i → T (Γ i)) ⊢ tr e ∶ T τ
    tr-typed {Γ = Γ} e = tr-typed′ e (λ _ → 𝟙) (λ i → T (Γ i)) (λ i → refl) (λ i → refl)

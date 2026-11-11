{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- The variant of the translation with a grade q: proofs.
--
--   1. Typing of a coercion, in each grade algebra and for each q. The
--      proof has the shape of `Wager.Trans.Typing`. The map of a
--      function binds the function at 𝟙 and the argument at q.
--   2. Typing of a term with no pair elimination and no `case`, for a
--      top grade q.
--   3. The variant and the translation of Stage 4 have one erasure. So
--      the behaviour part of T5 holds for the variant.
--   4. T6 for the variant: the theorem of Stage 5, read with q in the
--      place of 𝟙.
open import Cubical.Foundations.Prelude
open import Wager.FC.Signature
open import Wager.Grade.Algebra
import Wager.Trans.Scheme

module Wager.Top.Proofs
  (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
  {R : Type} (ops : GradeOps R) (q : R) where

open import Cubical.Data.Bool.Base using (true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)

open import Wager.Grade.Finite using (false≢true)
open import Wager.Role.Role
open import Wager.FC.Types SS
open import Wager.FC.Coercion SS
open import Wager.FC.Term SS
open import Wager.FC.RoleSoundness SS using (nomZ-l; nomZ-r; nomZ-idem)
open import Wager.Top.Translation SS Sc ops q
open import Wager.Top.Statements SS Sc ops q
open import Wager.Trans.Target SS Sc opsq
open import Wager.Trans.Nominal SS Sc opsq using (nominal-defeq; nominal-nf; T-inst; T-embE)
open import Wager.Trans.Coercion SS Sc opsq
  hiding (arrMap; arrIso; bodyIso; ntIso; coI; coerceT; tr)
import Wager.Trans.Coercion SS Sc ops as S4
import Wager.Trans.Target SS Sc ops as T4
import Wager.Trans.Simulation
open import Wager.L1.Conversion tSig
open import Wager.L2.Typing tSig tTSig ops
  using ( Usage; 0ᵘ; _+ᵘ_; _·ᵘ_; _≤ᵘ_; _▹_; unit; Cx; _▹ᶜ_; _▸_⊢_∶_
        ; t-var; t-lam; t-app; t-pair; t-letp; t-inj₁; t-inj₂; t-case
        ; t-lit; t-step; t-conv; t-sub )
open import Wager.Erased.Untyped
open GradeOps ops

private
  variable
    n : ℕ
    X Y Z X' Y' : Ty [] ★

  castU : {γ γ' : Usage n} {Γ : Cx n} {t : Tm n} {A : Ty [] ★} →
          γ ≡ γ' → γ ▸ Γ ⊢ t ∶ A → γ' ▸ Γ ⊢ t ∶ A
  castU {Γ = Γ} {t} {A} p d = subst (λ z → z ▸ Γ ⊢ t ∶ A) p d

  castT : {γ : Usage n} {Γ : Cx n} {t : Tm n} {A B : Ty [] ★} →
          A ≡ B → γ ▸ Γ ⊢ t ∶ A → γ ▸ Γ ⊢ t ∶ B
  castT {γ = γ} {Γ} {t} p d = subst (λ z → γ ▸ Γ ⊢ t ∶ z) p d

------------------------------------------------------------------------
-- 1 and 2. Typing, for the laws of a grade algebra.

module Typed (laws : GradeLaws ops) where
  open GradeLaws laws

  TyTr : (X Y : Ty [] ★) → Tr → Type
  TyTr X Y f = ∀ {n} {γ : Usage n} {Γ : Cx n} {t : Tm n} →
               γ ▸ Γ ⊢ t ∶ X → γ ▸ Γ ⊢ f t ∶ Y

  IsoTyped : Ty [] ★ → Ty [] ★ → Iso → Type
  IsoTyped X Y i = TyTr X Y (fwd i) × TyTr Y X (bwd i)

  id-typed : DefEq X Y → IsoTyped X Y idIso
  id-typed e = (λ d → t-conv d e) , (λ d → t-conv d (d-sym e))

  swap-typed : ∀ {i} → IsoTyped X Y i → IsoTyped Y X (swapIso i)
  swap-typed (f , g) = g , f

  comp-typed : ∀ {i j} → IsoTyped X Y i → IsoTyped Y Z j → IsoTyped X Z (compIso i j)
  comp-typed (f , g) (f' , g') = (λ d → f' (f d)) , (λ d → g (g' d))

  -- The function f is bound at 𝟙 and used one time. The argument x is
  -- bound at q: the function f has an arrow of the grade q, so the use
  -- of x counts q · 𝟙.
  arrMapq-typed : ∀ {h g : Tr} → TyTr X' X h → TyTr Y Y' g →
                  TyTr (arr q X Y) (arr q X' Y') (arrMapq (arr q X Y) X' h g)
  arrMapq-typed th tg {γ = γ} d =
    castU (funExt λ i → zero-add (𝟙 · γ i) ∙ one-mul (γ i))
      (t-app
        (t-lam {γ = 0ᵘ}
          (t-lam {γ = 0ᵘ ▹ 𝟙}
            (castU eq (tg (t-app (t-var (suc zero)) (th (t-var zero)))))))
        d)
    where
      eq : ∀ {n} → (unit {n = suc (suc n)} (suc zero) +ᵘ (q ·ᵘ unit zero)) ≡ (0ᵘ ▹ 𝟙 ▹ q)
      eq = funExt λ { zero          → zero-add (q · 𝟙) ∙ mul-one q
                    ; (suc zero)    → cong (𝟙 +_) (mul-zero q) ∙ add-zero 𝟙
                    ; (suc (suc i)) → cong (𝟘 +_) (mul-zero q) ∙ add-zero 𝟘 }

  arrIsoq-typed : ∀ {i j} → IsoTyped X X' i → IsoTyped Y Y' j →
                  IsoTyped (arr q X Y) (arr q X' Y') (arrIsoq X X' Y Y' i j)
  arrIsoq-typed (f , g) (f' , g') = arrMapq-typed g f' , arrMapq-typed f g'

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

  step-typed : (x : Inst) → IsoTyped (capp (stateOf x) (carrierOf x)) (carrierOf x) (stepIso x)
  step-typed x = (λ d → t-step (unwrap , x) d) , (λ d → t-step (wrap , x) d)

  module _ {d : Role} (hn : leR nom d ≡ true → DefEq X Y) where

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
                   IsoTyped (TB β X) (TB β Y) (bodyIsoq β X Y i)
      body-typed bvar        le = hv le
      body-typed (bbase b)   le = id-typed d-refl
      body-typed (barr β γ)  le =
        arrIsoq-typed (body-typed β (leR-trans _ _ _ (max-upper-l (roleOf β) (roleOf γ)) le))
                      (body-typed γ (leR-trans _ _ _ (max-upper-r (roleOf β) (roleOf γ)) le))
      body-typed (bprod β γ) le =
        prodIso-typed (body-typed β (leR-trans _ _ _ (max-upper-l (roleOf β) (roleOf γ)) le))
                      (body-typed γ (leR-trans _ _ _ (max-upper-r (roleOf β) (roleOf γ)) le))
      body-typed (bsum β γ)  le =
        sumIso-typed (body-typed β (leR-trans _ _ _ (max-upper-l (roleOf β) (roleOf γ)) le))
                     (body-typed γ (leR-trans _ _ _ (max-upper-r (roleOf β) (roleOf γ)) le))
      body-typed (bfam F β)  le = id-typed (d-papp (body-defeq β le))

  SemTy : Role → STy → STy → Iso → Type
  SemTy nom τ σ i = DefEq (T τ) (T σ)
  SemTy rep τ σ i = IsoTyped (T τ) (T σ) i
  SemTy ph  τ σ i = Unit

  module _ (wr : WellRoled) where

    private
      nt-wrap : ∀ N {τ σ i} →
                IsoTyped (TB (body N) (T τ)) (TB (body N) (T σ)) (bodyIsoq (body N) (T τ) (T σ) i) →
                IsoTyped (T (nt₁ N τ)) (T (nt₁ N σ)) (ntIsoq N τ σ i)
      nt-wrap N {τ} {σ} (f , g) =
          (λ d → t-step (wrap , inr (N , σ)) (f (t-step (unwrap , inr (N , τ)) d)))
        , (λ d → t-step (wrap , inr (N , τ)) (g (t-step (unwrap , inr (N , σ)) d)))

      nt-typed : ∀ N d {τ σ} → leR (roleOf (body N)) d ≡ true →
                 (γ : Co d τ σ) → SemTy d τ σ (coIq d γ) →
                 IsoTyped (T (nt₁ N τ)) (T (nt₁ N σ)) (ntIsoq N τ σ (coIq d γ))
      nt-typed N rep le γ sem =
        nt-wrap N (body-typed (λ p → ⊥.rec (false≢true p)) {i = coIq rep γ} (λ _ → sem) (body N) le)
      nt-typed N nom le γ sem =
        nt-wrap N (body-typed (λ _ → sem) {i = idIso} (λ _ → id-typed sem) (body N) le)
      nt-typed N ph  le γ sem =
        nt-wrap N (body-typed (λ p → ⊥.rec (false≢true p)) {i = idIso}
                              (λ p → ⊥.rec (false≢true p)) (body N) le)

    coIq-typed : ∀ r {τ σ} (γ : Co r τ σ) → SemTy r τ σ (coIq r γ)
    coIq-typed nom γ = nominal-defeq γ
    coIq-typed ph  γ = tt
    coIq-typed rep (c-sym γ)     = swap-typed (coIq-typed rep γ)
    coIq-typed rep (c-trans γ δ) = comp-typed (coIq-typed rep γ) (coIq-typed rep δ)
    coIq-typed rep (c-sub γ)     = id-typed (nominal-defeq γ)
    coIq-typed rep (c-arr γ δ)   = arrIsoq-typed (coIq-typed rep γ) (coIq-typed rep δ)
    coIq-typed rep (c-prod γ δ)  = prodIso-typed (coIq-typed rep γ) (coIq-typed rep δ)
    coIq-typed rep (c-sum γ δ)   = sumIso-typed (coIq-typed rep γ) (coIq-typed rep δ)
    coIq-typed rep (c-nt₁ N γ)   =
      nt-typed N (mulG rep (role N)) (wr N) γ (coIq-typed (mulG rep (role N)) γ)
    coIq-typed rep (c-ax₀ N)     =
      subst (λ Z → IsoTyped (T (nt₀ N)) Z (stepIso (inl N)))
            (sym (T-embE (rep₀ N))) (step-typed (inl N))
    coIq-typed rep (c-ax₁ N τ)   =
      subst (λ Z → IsoTyped (T (nt₁ N τ)) Z (stepIso (inr (N , τ))))
            (sym (T-inst (body N) τ)) (step-typed (inr (N , τ)))

    -- 2. A term with no pair elimination and no `case`, for a top grade.
    module _ (top : IsTop) where

      private
        Qs : Usage n → Type
        Qs γ = ∀ i → γ i ≡ q

        qs-ext : {γ : Usage n} → Qs γ → Qs (γ ▹ q)
        qs-ext o zero    = refl
        qs-ext o (suc i) = o i

        -- Each usage vector is below a vector of top grades.
        top-le : (δ : Usage n) {γ : Usage n} → Qs γ → δ ≤ᵘ γ
        top-le δ o i = subst (δ i ≤_) (sym (o i)) (top (δ i))

        Agree : Cx n → SCx n → Type
        Agree Δ Γ = ∀ i → Δ i ≡ T (Γ i)

        agree-ext : ∀ {Δ : Cx n} {Γ : SCx n} τ → Agree Δ Γ → Agree (Δ ▹ᶜ T τ) (Γ ▹ˢ τ)
        agree-ext τ h zero    = refl
        agree-ext τ h (suc i) = h i

      trq-typed′ : ∀ {Γ : SCx n} {τ} (e : STm Γ τ) → NoElim e →
                   (γ : Usage n) (Δ : Cx n) → Qs γ → Agree Δ Γ → γ ▸ Δ ⊢ trq e ∶ T τ
      trq-typed′ (svar i) ne γ Δ o h = t-sub (castT (h i) (t-var i)) (top-le _ o)
      trq-typed′ (slam {τ = τ} b) ne γ Δ o h =
        t-lam (trq-typed′ b ne (γ ▹ q) (Δ ▹ᶜ T τ) (qs-ext o) (agree-ext τ h))
      trq-typed′ (sapp f a) (nf , na) γ Δ o h =
        t-sub (t-app (trq-typed′ f nf γ Δ o h) (trq-typed′ a na γ Δ o h)) (top-le _ o)
      trq-typed′ (spair s t) (ns , nt) γ Δ o h =
        t-sub (t-pair (trq-typed′ s ns γ Δ o h) (trq-typed′ t nt γ Δ o h)) (top-le _ o)
      trq-typed′ (sinl t) ne γ Δ o h = t-inj₁ (trq-typed′ t ne γ Δ o h)
      trq-typed′ (sinr t) ne γ Δ o h = t-inj₂ (trq-typed′ t ne γ Δ o h)
      trq-typed′ (slit ℓ) ne γ Δ o h = t-sub (t-lit ℓ) (top-le _ o)
      trq-typed′ (cast c e) ne γ Δ o h = fst (coIq-typed rep c) (trq-typed′ e ne γ Δ o h)

top-coercion-typed : Top-Coercion-Typed
top-coercion-typed laws wr c d = fst (Typed.coIq-typed laws wr rep c) d

top-coerce-typed : Top-Coerce-Typed
top-coerce-typed laws wr le c Γ =
  t-lam {γ = 0ᵘ}
    (t-sub (fst (Typed.coIq-typed laws wr rep c) (t-var zero))
           (λ { zero → le ; (suc i) → GradeLaws.le-refl laws 𝟘 }))

top-typing : Top-Typing
top-typing laws wr top {Γ = Γ} e ne =
  Typed.trq-typed′ laws wr top e ne (λ _ → q) (λ i → T (Γ i)) (λ i → refl) (λ i → refl)

------------------------------------------------------------------------
-- 3. One erasure. The erasure does not read a grade or a type.

private
  -- A transformer of the variant and a transformer of Stage 4 that
  -- keep "the two terms have one erasure".
  Er : Tr → S4.Tr → Type
  Er f f4 = ∀ {n} (t : Tm n) (t4 : S4.Tm n) →
            eraseT t ≡ S4.eraseT t4 → eraseT (f t) ≡ S4.eraseT (f4 t4)

  infixr 4 _,ᵉ_
  record ErIso (i : Iso) (i4 : S4.Iso) : Type where
    constructor _,ᵉ_
    field
      eraF : Er (fwd i) (S4.fwd i4)
      eraB : Er (bwd i) (S4.bwd i4)
  open ErIso

  id-er : ErIso idIso S4.idIso
  id-er = (λ t t4 p → p) ,ᵉ (λ t t4 p → p)

  swap-er : ∀ {i i4} → ErIso i i4 → ErIso (swapIso i) (S4.swapIso i4)
  swap-er (f ,ᵉ g) = g ,ᵉ f

  comp-er : ∀ {i i4 j j4} → ErIso i i4 → ErIso j j4 →
            ErIso (compIso i j) (S4.compIso i4 j4)
  comp-er {i} {i4} {j} {j4} (f ,ᵉ g) (f' ,ᵉ g') =
      (λ t t4 p → f' (fwd i t) (S4.fwd i4 t4) (f t t4 p))
    ,ᵉ (λ t t4 p → g (bwd j t) (S4.bwd j4 t4) (g' t t4 p))

  arrMap-er : ∀ {X A : Ty [] ★} {X4 A4 : T4.Ty [] T4.★} {h g : Tr} {h4 g4 : S4.Tr} →
              Er h h4 → Er g g4 → Er (arrMapq X A h g) (S4.arrMap X4 A4 h4 g4)
  arrMap-er {h = h} {h4 = h4} eh eg t t4 p i =
    uapp (ulam (ulam (eg (tapp (tvar (suc zero)) (h (tvar zero)))
                         (S4.tapp (S4.tvar (suc zero)) (h4 (S4.tvar zero)))
                         (λ j → uapp (uvar (suc zero)) (eh (tvar zero) (S4.tvar zero) refl j)) i)))
         (p i)

  arrIso-er : ∀ {A A' B B' : Ty [] ★} {A4 A'4 B4 B'4 : T4.Ty [] T4.★} {i i4 j j4} →
              ErIso i i4 → ErIso j j4 →
              ErIso (arrIsoq A A' B B' i j) (S4.arrIso A4 A'4 B4 B'4 i4 j4)
  arrIso-er {A = A} {A'} {B} {B'} {A4} {A'4} {B4} {B'4} {i} {i4} {j} {j4} (f ,ᵉ g) (f' ,ᵉ g') =
      arrMap-er {X = arr q A B} {A = A'} {X4 = T4.arr 𝟙 A4 B4} {A4 = A'4}
                {h = bwd i} {g = fwd j} {h4 = S4.bwd i4} {g4 = S4.fwd j4} g f'
    ,ᵉ arrMap-er {X = arr q A' B'} {A = A} {X4 = T4.arr 𝟙 A'4 B'4} {A4 = A4}
                 {h = fwd i} {g = bwd j} {h4 = S4.fwd i4} {g4 = S4.bwd j4} f g'

  prodMap-er : ∀ {f g : Tr} {f4 g4 : S4.Tr} → Er f f4 → Er g g4 →
               Er (prodMap f g) (S4.prodMap f4 g4)
  prodMap-er ef eg t t4 p i =
    uletp (p i) (upair (ef (tvar (suc zero)) (S4.tvar (suc zero)) refl i)
                       (eg (tvar zero) (S4.tvar zero) refl i))

  prodIso-er : ∀ {i i4 j j4} → ErIso i i4 → ErIso j j4 →
               ErIso (prodIso i j) (S4.prodIso i4 j4)
  prodIso-er {i} {i4} {j} {j4} (f ,ᵉ g) (f' ,ᵉ g') =
      prodMap-er {f = fwd i} {g = fwd j} {f4 = S4.fwd i4} {g4 = S4.fwd j4} f f'
    ,ᵉ prodMap-er {f = bwd i} {g = bwd j} {f4 = S4.bwd i4} {g4 = S4.bwd j4} g g'

  sumMap-er : ∀ {f g : Tr} {f4 g4 : S4.Tr} → Er f f4 → Er g g4 →
              Er (sumMap f g) (S4.sumMap f4 g4)
  sumMap-er ef eg t t4 p i =
    ucase (p i) (uinl (ef (tvar zero) (S4.tvar zero) refl i))
                (uinr (eg (tvar zero) (S4.tvar zero) refl i))

  sumIso-er : ∀ {i i4 j j4} → ErIso i i4 → ErIso j j4 →
              ErIso (sumIso i j) (S4.sumIso i4 j4)
  sumIso-er {i} {i4} {j} {j4} (f ,ᵉ g) (f' ,ᵉ g') =
      sumMap-er {f = fwd i} {g = fwd j} {f4 = S4.fwd i4} {g4 = S4.fwd j4} f f'
    ,ᵉ sumMap-er {f = bwd i} {g = bwd j} {f4 = S4.bwd i4} {g4 = S4.bwd j4} g g'

  step-er : (x : Inst) → ErIso (stepIso x) (S4.stepIso x)
  step-er x = (λ t t4 p → p) ,ᵉ (λ t t4 p → p)

  body-er : ∀ β (X Y : Ty [] ★) (X4 Y4 : T4.Ty [] T4.★) {i i4} → ErIso i i4 →
            ErIso (bodyIsoq β X Y i) (S4.bodyIso β X4 Y4 i4)
  body-er bvar        X Y X4 Y4 e = e
  body-er (bbase b)   X Y X4 Y4 e = id-er
  body-er (barr β γ)  X Y X4 Y4 e = arrIso-er (body-er β X Y X4 Y4 e) (body-er γ X Y X4 Y4 e)
  body-er (bprod β γ) X Y X4 Y4 e = prodIso-er (body-er β X Y X4 Y4 e) (body-er γ X Y X4 Y4 e)
  body-er (bsum β γ)  X Y X4 Y4 e = sumIso-er (body-er β X Y X4 Y4 e) (body-er γ X Y X4 Y4 e)
  body-er (bfam F β)  X Y X4 Y4 e = id-er

  nt-er : ∀ N τ σ {i i4} → ErIso i i4 → ErIso (ntIsoq N τ σ i) (S4.ntIso N τ σ i4)
  nt-er N τ σ e =
      (λ t t4 p → eraF b (step (unwrap , inr (N , τ)) t) (S4.step (T4.unwrap , inr (N , τ)) t4) p)
    ,ᵉ (λ t t4 p → eraB b (step (unwrap , inr (N , σ)) t) (S4.step (T4.unwrap , inr (N , σ)) t4) p)
    where b = body-er (body N) (T τ) (T σ) (T4.T τ) (T4.T σ) e

  coI-er : ∀ r {τ σ} (γ : Co r τ σ) → ErIso (coIq r γ) (S4.coI r γ)
  coI-er nom γ = id-er
  coI-er ph  γ = id-er
  coI-er rep (c-sym γ)     = swap-er (coI-er rep γ)
  coI-er rep (c-trans γ δ) = comp-er (coI-er rep γ) (coI-er rep δ)
  coI-er rep (c-sub γ)     = id-er
  coI-er rep (c-arr γ δ)   = arrIso-er (coI-er rep γ) (coI-er rep δ)
  coI-er rep (c-prod γ δ)  = prodIso-er (coI-er rep γ) (coI-er rep δ)
  coI-er rep (c-sum γ δ)   = sumIso-er (coI-er rep γ) (coI-er rep δ)
  coI-er rep (c-nt₁ {τ = τ} {σ = σ} N γ) = nt-er N τ σ (coI-er (mulG rep (role N)) γ)
  coI-er rep (c-ax₀ N)     = step-er (inl N)
  coI-er rep (c-ax₁ N τ)   = step-er (inr (N , τ))

top-same-erasure : Top-Same-Erasure
top-same-erasure (svar i)      = refl
top-same-erasure (slam b)      = cong ulam (top-same-erasure b)
top-same-erasure (sapp f a)    = cong₂ uapp (top-same-erasure f) (top-same-erasure a)
top-same-erasure (spair s t)   = cong₂ upair (top-same-erasure s) (top-same-erasure t)
top-same-erasure (sletp s b)   = cong₂ uletp (top-same-erasure s) (top-same-erasure b)
top-same-erasure (sinl t)      = cong uinl (top-same-erasure t)
top-same-erasure (sinr t)      = cong uinr (top-same-erasure t)
top-same-erasure (scase s l r) i =
  ucase (top-same-erasure s i) (top-same-erasure l i) (top-same-erasure r i)
top-same-erasure (slit ℓ)      = refl
top-same-erasure (cast c e)    =
  ErIso.eraF (coI-er rep c) (trq e) (S4.tr e) (top-same-erasure e)

-- The behaviour part of T5, moved along the equality of the erasures.
top-behaviour : Top-Behaviour
top-behaviour wr e =
  let (v , w , d , d' , h) = Wager.Trans.Simulation.behaviour SS Sc ops wr e
  in v , w , d , subst (λ u → ∅ᵉ ⊢ u ⇓ w) (sym (top-same-erasure e)) d' , h

------------------------------------------------------------------------
-- 4. T6. The theorem of Stage 5 holds for each set of grade
-- operations, so it holds with q in the place of 𝟙.

top-nominal : Top-Nominal
top-nominal = nominal-nf

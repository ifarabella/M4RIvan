import Mathlib
universe u

suppress_compilation

open MvPolynomial

variable (R : Type ) [CommRing R]

open GradedAlgebra

open AlgebraicGeometry
attribute [instance] gradedAlgebra

variable (n : ℕ)

noncomputable abbrev Pn := Proj (homogeneousSubmodule (Fin (n + 1)) ℤ)

open Scheme

#check Hom (Spec (.of R)) $ Pn 7
--want 2nd functor, made up of 'locally rank n direct summands of Tⁿ⁺¹, K'
--define this as Tⁿ⁺¹⧸K is an invertible module
-- an invertible T - module is a f.g. locally free T-module of rank 1.
--locally free
--class InvertibleModule (R M : Type) [CommRing R] [AddCommMonoid M] [Module R M] :
        --Prop where
    --out : ∃ (h1 : Module.Finite R M) (h2 : Module.Projective R M),
    --∀ (p : Ideal R) (h4 : p.IsPrime),
    --(Module.rank ( (Localization.AtPrime p) (Module.LocalizedModule M p)) = 1)

open CategoryTheory
open TensorProduct

variable (d : ℕ) (V₀: Type) (R₀ : CommRingCat.{0}) [AddCommGroup V₀] [Module R₀ V₀]  --(x: Under R₀)
    [Module.Projective R₀ V₀]

def myFunctorish (R : Under R₀) : Type := {M : Submodule R (R ⊗[R₀] V₀) //
    Module.Projective R ((R ⊗[R₀] V₀)⧸M) ∧
    (∀ P : PrimeSpectrum R, Module.rankAtStalk ((R ⊗[R₀] V₀)⧸M) P = d)}

variable {R S : Under R₀} [Algebra R S] [IsScalarTower R₀ R S]

instance foo (M : Submodule R (R ⊗[R₀] V₀)) : AddCommMonoid ((R ⊗[R₀] V₀)⧸M) := by exact
  SubtractionCommMonoid.toAddCommMonoid

def myModA (M : Submodule R (R ⊗[R₀] V₀)) :
  Submodule R (S ⊗[R] (R ⊗[R₀] V₀)) :=
  LinearMap.range ((Submodule.subtype M).lTensor S)

/- **Might not need**
instance basechangequotProj (M : Submodule R (R ⊗[R₀] V₀)) [Module.Projective R ((R ⊗[R₀] V₀)⧸M)] :
  Module.Projective S (S ⊗[R₀] ((R ⊗[R₀] V₀)⧸M)) := by
  let _ : Module.Projective R₀ (R ⊗[↑R₀] V₀ ⧸ M) := by sorry -- **FALSE!**
  exact Module.Projective.tensorProduct
-/

--def myModB (M : Submodule R (R ⊗[R₀] V₀)) : Submodule S (S ⊗[R₀] V₀) :=
  --letI := f.right.toAlgebra
  --haveI : IsScalarTower R₀ R S := .of_algebraMap_eq' f.w
  --LinearMap.range (((AlgebraTensorModule.cancelBaseChange R₀ R R S V₀).toLinearMap) ∘ₗ ((Submodule.subtype M).lTensor S))
/-

def myquot1 (M : Submodule R (R ⊗[R₀] V₀)) [Module R S] :=
    ((S ⊗[R] (R ⊗[R₀] V₀))⧸(LinearMap.range ((Submodule.subtype M).lTensor S)))

instance (M : Submodule R (R ⊗[R₀] V₀)) [Module R S] : AddCommGroup (myquot1 V₀ R₀ M) := by sorry

instance (M : Submodule R (R ⊗[R₀] V₀)) [Module R S] : Module R₀ (myquot1 V₀ R₀ M) := by sorry
noncomputable def myequiv (M : Submodule R (R ⊗[R₀] V₀)) [Module.Projective R ((R ⊗[R₀] V₀)⧸M)] (f : R → S)
    [Module R S]
    [AddCommMonoid (↑S.right ⊗[↑R.right] ↑R.right ⊗[↑R₀] V₀ ⧸ LinearMap.range (LinearMap.lTensor (↑S.right) M.subtype))] : --shouldn't need [Module R S] or this
    (S ⊗[R] ((R ⊗[R₀] V₀)⧸M)) →ₗ[R] (myquot1 V₀ R₀ M)
    := by sorry

def myequivcancel (M : Submodule R (R ⊗[R₀] V₀)) [Module.Projective R ((R ⊗[R₀] V₀)⧸M)] (f : R → S)
    [Module R S]
    [AddCommMonoid (↑S.right ⊗[↑R.right] ↑R.right ⊗[↑R₀] V₀ ⧸ LinearMap.range (LinearMap.lTensor (↑S.right) M.subtype))] :
    ((S ⊗[R] (R ⊗[R₀] V₀))⧸(LinearMap.range ((Submodule.subtype M).lTensor S))) →ₗ[R] ((S ⊗[R₀] V₀)⧸((LinearMap.range ((Submodule.subtype M).lTensor S)))) := by sorry

lemma projBaseChange (M : Submodule R (R ⊗[R₀] V₀)) [Module.Projective R ((R ⊗[R₀] V₀)⧸M)] (f : R → S)
    [Module R S]
    [AddCommMonoid (↑S.right ⊗[↑R.right] ↑R.right ⊗[↑R₀] V₀ ⧸ LinearMap.range (LinearMap.lTensor (↑S.right) M.subtype))]
    [HasQuotient (↑S.right ⊗[↑R₀] V₀) (Submodule (↑R.right) (↑S.right ⊗[↑R.right] ↑R.right ⊗[↑R₀] V₀))] :
    Module.Projective (((S ⊗[R₀] V₀)⧸((LinearMap.range ((Submodule.subtype M).lTensor S))))) := by sorry

def myModMap (M : Submodule R (R ⊗[R₀] V₀)) : Submodule S (S ⊗[R₀] V₀) :=
    --LinearMap.range ((Submodule.subtype M).lTensor S)
-/
-- let R and S be R_0-algebras and let f: R → S be an R_0-algebra hom
-- myModMap is a function which eats an R-submod of R ⨂ V_0 and returns an S-submod of S ⊗ V_0
variable (S) in
def myModMap' (M : Submodule R (R ⊗[R₀] V₀)) : Submodule S (S ⊗[R₀] V₀) :=
  -- Commutative triangle R0 -> R -> S commutes
  -- and we tell this to the typeclass system
  -- `M` = R-submodule of `R ⊗[R0] V0`
  -- `M.subtype` = obvious injective R-linear map `M -> R ⊗[R0] V0`
  -- `M-subtype.baseChange S` = base-changed map `S ⊗[R] M -> S ⊗[R] (R ⊗[R0] V0)`
  -- We're going to compose this map with something else, which is the map
  -- `S ⊗[R] (R ⊗[R0] V0) ---(obvious)---> (S ⊗[R] R) ⊗[R0] V0 ---("mul_one")--> S ⊗[R0] V0`
  -- and we'll get a map `S ⊗[R] M -> S ⊗[R0] V0`
  -- Now take the image (LinearMap.range)
  LinearMap.range ((AlgebraTensorModule.cancelBaseChange R₀ R S S V₀).toLinearMap ∘ₗ (M.subtype.baseChange (S)))
--def myFunct (d : ℕ) : CommRingCat ⥤ Type _ where
  --obj R := {M : Submodule R ((Fin n) → R) // Module.Projective R ((Fin n → R)⧸M) ∧ (∀ P : PrimeSpectrum R, Module.rankAtStalk ((Fin n → R)⧸M) P = d) }
  --map {R S} f M := ⟨(M.subtype.lTensor S).range, _ ⟩ --LinearMap.lTensor
  --map_id := _
  --map_comp := _

variable (S) in
omit [Module.Projective (↑R₀) V₀] [IsScalarTower ↑R₀ ↑R.right ↑S.right] in
lemma mapsurj (M : Submodule R (R ⊗[R₀] V₀)) :
    Function.Surjective ((Submodule.mkQ M).baseChange S) :=
  LinearMap.lTensor_surjective (↑S.right) (Submodule.mkQ_surjective M )

variable (S) in
omit [Module.Projective (↑R₀) V₀] [IsScalarTower ↑R₀ ↑R.right ↑S.right] in
lemma mapexact (M : Submodule R (R ⊗[R₀] V₀)) :
    Function.Exact ((Submodule.subtype M).baseChange S) ((Submodule.mkQ M).baseChange S) := by
  have foo : Function.Exact (Submodule.subtype M) (Submodule.mkQ M) := LinearMap.exact_subtype_mkQ M
  have foo' : Function.Surjective (Submodule.mkQ M) := Submodule.mkQ_surjective M
  exact lTensor_exact S foo foo'
    --LinearMap.lTensor_exact' (↑R.right) (↑S.right) (↥M) (↑R.right ⊗[↑R₀] V₀) (↑R.right ⊗[↑R₀] V₀ ⧸ M)
      --M.subtype M.mkQ foo

-- instance :
--     Module R (S ⊗[R] (R ⊗[R₀] V₀)) :=
--     instModule

-- instance (M : Submodule R (R ⊗[R₀] V₀)) [Module R S] : Module R (LinearMap.range ((Submodule.subtype M).lTensor S)) :=
--   (LinearMap.range (LinearMap.lTensor (↑S.right) M.subtype)).module'

-- instance (M : Submodule R (R ⊗[R₀] V₀)) [Module R S] : ((LinearMap.range ((Submodule.subtype M).lTensor S)) : Submodule R (S ⊗[R] (R ⊗[R₀] V₀))) := by sorry

-- instance (M : Submodule R (R ⊗[R₀] V₀)) [Module R S] :
--     AddCommMonoid (↑S.right ⊗[↑R.right] ↑R.right ⊗[↑R₀] V₀ ⧸ LinearMap.range (LinearMap.lTensor (↑S.right) M.subtype)) := by sorry

-- instance (M : Submodule R (R ⊗[R₀] V₀)) [Module R S] :
--     Module (↑R.right) (↑S.right ⊗[↑R.right] ↑R.right ⊗[↑R₀] V₀ ⧸ LinearMap.range (LinearMap.lTensor (↑S.right) M.subtype)) := by sorry
/-
lemma equiv1 (M : Submodule R (R ⊗[R₀] V₀)) [Module R S] : ((S ⊗[R] (R ⊗[R₀] V₀)) ⧸ (LinearMap.range ((Submodule.subtype M).lTensor S)))
    ≃ₗ[R] (S ⊗[R] ((R ⊗[R₀] V₀) ⧸ M)) :=
  Function.Exact.linearEquivOfSurjective (mapexact V₀ R₀ M) (mapsurj V₀ R₀ M)
-/
lemma projlem {R M N : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Projective R M] (f : M ≃ₗ[R] N) : Module.Projective R N := by
  --apply Module.Projective.of_lifting_property''
  --intro g1 g2
  --have h : Module.Projective R M := inferInstance
  exact Module.Projective.of_equiv f

omit [Module.Projective (↑R₀) V₀] in
lemma mymodeq (M : Submodule R (R ⊗[R₀] V₀)) : Submodule.map (AlgebraTensorModule.cancelBaseChange (↑R₀) (↑R.right) (↑S.right) (↑S.right) V₀)
    (LinearMap.range (LinearMap.baseChange (↑S.right) M.subtype)) =
  myModMap' V₀ R₀ S M := by
  rw [myModMap', LinearMap.range_comp]
  rfl

omit [Module.Projective (↑R₀) V₀] in
lemma myModProj1 (M : Submodule R (R ⊗[R₀] V₀)) [Module.Projective R ((R ⊗[R₀] V₀)⧸M)] :
    Module.Projective S ((S ⊗[R₀] V₀) ⧸ (myModMap' V₀ R₀ S M)) := by
  refine Module.Projective.of_equiv  (?_ : S ⊗[R] ((R ⊗[R₀] V₀) ⧸ M) ≃ₗ[S] (S ⊗[R₀] V₀) ⧸ (myModMap' V₀ R₀ S M))
  --refine projlem (?_ : S ⊗[R] ((R ⊗[R₀] V₀) ⧸ M) ≃ₗ[S] (S ⊗[R₀] V₀) ⧸ (myModMap' V₀ R₀ S M))
  /-
  mapexact (V₀ : Type) (R₀ : CommRingCat) [AddCommGroup V₀] [Module (↑R₀) V₀] [Module.Projective (↑R₀) V₀]
  {R S : Under R₀} (M : Submodule (↑R.right) (↑R.right ⊗[↑R₀] V₀)) [Module ↑R.right ↑S.right] :
  -/
  have h1 := (mapexact V₀ R₀ S M)
  let foo := (Function.Exact.linearEquivOfSurjective (M := S ⊗[R] ↥M) (mapexact V₀ R₀ S M) (mapsurj V₀ R₀ S M)).symm
  -- want: S-module iso, have foo: R-module iso :-( **now its an S-module iso yay**
  -- `foo` not strong enough :-(
  refine foo ≪≫ₗ ?_
  let foo' := Submodule.Quotient.equiv
    (LinearMap.range (LinearMap.baseChange (↑S.right) M.subtype))
    (myModMap' V₀ R₀ S M)
    (AlgebraTensorModule.cancelBaseChange R₀ R S S V₀)
    (mymodeq V₀ R₀ M)
  exact foo'
  --refine ?_ ∘ₗ foo.symm
  --refine ?_ ∘ₗ (Function.Exact.linearEquivOfSurjective (mapexact V₀ R₀ S M) (mapsurj V₀ R₀ S M))

--  refine projlem ((LinearEquiv.symm
--    ((Submodule.Quotient.equiv ?_ ?_ ?_ ?_) ∘ₗ (Function.Exact.linearEquivOfSurjective (mapexact V₀ R₀ M) (mapsurj V₀ R₀ M)))))
  --need to insert a map from '(S ⊗[R] (R ⊗[R0] V0)) ⧸ myModmap'' to (S ⊗[R₀] V₀) ⧸ M
--projlem (basechangequotProj V₀ R₀ M) (LinearEquiv.symm ((Function.Exact.linearEquivOfSurjective (mapexact V₀ R₀ M) (mapsurj V₀ R₀ M))))

-- pull back prime of S to prime of R
variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (Q : PrimeSpectrum S) (P : PrimeSpectrum R)
    -- P = f^{-1}(Q) where f : R → S is `algebraMap R S`
    -- exact? found the way to pull back Q to Spec(R)
--    (h : P = (algebraMap R S).specComap Q)
    (h' : P.asIdeal = Ideal.comap (algebraMap R S) Q.asIdeal)

noncomputable example : Localization.AtPrime P.asIdeal →+*
    Localization.AtPrime Q.asIdeal :=
  -- `exact?` found the map from R_P to S_Q if P := f^{-1}(Q), f : R → S
  Localization.localRingHom P.asIdeal Q.asIdeal (algebraMap R S) <| h'

-- R_P is automatically an R-algebra
#synth Algebra R (Localization.AtPrime P.asIdeal)

#synth Algebra R (Localization.AtPrime Q.asIdeal) -- in fact S_Q is an R-algebra already!



-- is this right? Not entirely sure. It *works* but there's no API for it.
example : R →+* Localization.AtPrime P.asIdeal := OreLocalization.numeratorRingHom
-- Question: is there a better name for R -> R_P when R is commutative?
-- Answer yes: R_P is known by typeclass inference to be an R-algebra automatically
-- so it's actually called
example : R →+* Localization.AtPrime P.asIdeal := algebraMap R (Localization.AtPrime P.asIdeal)

#check Localization.localRingHom_to_map P.asIdeal Q.asIdeal (algebraMap R S) h'
/-
∀ (x : R),
  (Localization.localRingHom P.asIdeal Q.asIdeal (algebraMap R S) ⋯)
      ((algebraMap R (Localization.AtPrime P.asIdeal)) x) =
    (algebraMap S (Localization.AtPrime Q.asIdeal)) ((algebraMap R S) x)

i.e. the map R -> R_P and then the map R_P -> S_Q equals the map R -> S and then the map S -> S_Q
all evaluated at x

-/
-- square R -> S -> S_Q and R -> R_P -> S_Q commutes
example : ((algebraMap S (Localization.AtPrime Q.asIdeal)).comp (algebraMap R S) :
    R →+* Localization.AtPrime Q.asIdeal) =
    (Localization.localRingHom P.asIdeal Q.asIdeal (algebraMap R S) <| h').comp
      (algebraMap R (Localization.AtPrime P.asIdeal)) := by
  ext x
  symm
  apply Localization.localRingHom_to_map P.asIdeal Q.asIdeal
  exact h'


lemma myModConstRank (M : Submodule R (R ⊗[R₀] V₀)) [Module.Projective R ((R ⊗[R₀] V₀)⧸M)]
    (h : ∀ P : PrimeSpectrum R, Module.rankAtStalk ((R ⊗[R₀] V₀)⧸M) P = d) :
    ∀ P : PrimeSpectrum S, Module.rankAtStalk ((S ⊗[R₀] V₀) ⧸ (myModMap' V₀ R₀ S M)) P = d := by
sorry

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

set_option synthInstance.maxHeartbeats 100000

instance foo (M : Submodule R (R ⊗[R₀] V₀)) : AddCommMonoid ((R ⊗[R₀] V₀)⧸M) := by exact
  SubtractionCommMonoid.toAddCommMonoid

def myModA (M : Submodule R (R ⊗[R₀] V₀)) :
  Submodule R (S ⊗[R] (R ⊗[R₀] V₀)) :=
  LinearMap.range ((Submodule.subtype M).lTensor S)

instance basechangequotProj (M : Submodule R (R ⊗[R₀] V₀)) [Module.Projective R ((R ⊗[R₀] V₀)⧸M)] :
  Module.Projective S (S ⊗[R₀] ((R ⊗[R₀] V₀)⧸M)) := by
  let _ : Module.Projective R₀ (R ⊗[↑R₀] V₀ ⧸ M) := by sorry -- **FALSE!**
  exact Module.Projective.tensorProduct
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
    Function.Surjective ((Submodule.mkQ M).lTensor S) :=
  LinearMap.lTensor_surjective (↑S.right) (Submodule.mkQ_surjective M )

-- missing from the library -- trick someone else into proving it?
lemma LinearMap.lTensor_exact (R S A B C : Type) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (h : Function.Exact f g) : Function.Exact (f.lTensor S) (g.lTensor S) := by
  sorry

variable (S) in
omit [Module.Projective (↑R₀) V₀] [IsScalarTower ↑R₀ ↑R.right ↑S.right] in
lemma mapexact (M : Submodule R (R ⊗[R₀] V₀)) :
    Function.Exact ((Submodule.subtype M).lTensor S) ((Submodule.mkQ M).lTensor S) := by
  have foo : Function.Exact (Submodule.subtype M) (Submodule.mkQ M) := LinearMap.exact_subtype_mkQ M
  exact
    LinearMap.lTensor_exact (↑R.right) (↑S.right) (↥M) (↑R.right ⊗[↑R₀] V₀) (↑R.right ⊗[↑R₀] V₀ ⧸ M)
      M.subtype M.mkQ foo

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
set_option maxHeartbeats 1000000
/-
lemma equiv1 (M : Submodule R (R ⊗[R₀] V₀)) [Module R S] : ((S ⊗[R] (R ⊗[R₀] V₀)) ⧸ (LinearMap.range ((Submodule.subtype M).lTensor S)))
    ≃ₗ[R] (S ⊗[R] ((R ⊗[R₀] V₀) ⧸ M)) :=
  Function.Exact.linearEquivOfSurjective (mapexact V₀ R₀ M) (mapsurj V₀ R₀ M)
-/
lemma projlem {R M N : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Projective R M] (f : M ≃ₗ[R] N) : Module.Projective R N := by sorry

lemma myModProj1 (M : Submodule R (R ⊗[R₀] V₀)) [Module.Projective R ((R ⊗[R₀] V₀)⧸M)] :
    Module.Projective S ((S ⊗[R₀] V₀) ⧸ (myModMap' V₀ R₀ S M)) := by
  refine projlem (?_ : S ⊗[R] ((R ⊗[R₀] V₀) ⧸ M) ≃ₗ[S] (S ⊗[R₀] V₀) ⧸ (myModMap' V₀ R₀ S M))
  /-
  mapexact (V₀ : Type) (R₀ : CommRingCat) [AddCommGroup V₀] [Module (↑R₀) V₀] [Module.Projective (↑R₀) V₀]
  {R S : Under R₀} (M : Submodule (↑R.right) (↑R.right ⊗[↑R₀] V₀)) [Module ↑R.right ↑S.right] :
  -/
  have h1 := (mapexact V₀ R₀ S M)
  let foo := (Function.Exact.linearEquivOfSurjective (M := ↑S.right ⊗[↑R.right] ↥M) (mapexact V₀ R₀ S M) (mapsurj V₀ R₀ S M)).symm
  -- want: S-module iso, have foo: R-module iso :-(
  -- `foo` not strong enough :-(
  -- refine foo ≪≫ₗ ?_
  --refine ?_ ∘ₗ foo.symm
  --refine ?_ ∘ₗ (Function.Exact.linearEquivOfSurjective (mapexact V₀ R₀ S M) (mapsurj V₀ R₀ S M))
  sorry
--  refine projlem ((LinearEquiv.symm
--    ((Submodule.Quotient.equiv ?_ ?_ ?_ ?_) ∘ₗ (Function.Exact.linearEquivOfSurjective (mapexact V₀ R₀ M) (mapsurj V₀ R₀ M)))))
  --need to insert a map from '(S ⊗[R] (R ⊗[R0] V0)) ⧸ myModmap'' to (S ⊗[R₀] V₀) ⧸ M
--projlem (basechangequotProj V₀ R₀ M) (LinearEquiv.symm ((Function.Exact.linearEquivOfSurjective (mapexact V₀ R₀ M) (mapsurj V₀ R₀ M))))
/-
lemma myModConstRank (M : Submodule R (R ⊗[R₀] V₀)) [Module.Projective R ((R ⊗[R₀] V₀)⧸M)]
    [∀ P : PrimeSpectrum R, Module.rankAtStalk ((R ⊗[R₀] V₀)⧸M) P = d] :
    ∀ P : PrimeSpectrum S, Module.rankAtStalk ((S ⊗[R₀] V₀) ⧸ (myModMap' V₀ R₀ M)) P = d := by sorry
-/

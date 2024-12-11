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

variable (d : ℕ) (V₀: Type) (R₀ : CommRingCat) [AddCommGroup V₀] [Module R₀ V₀]  --(x: Under R₀)
    [Module.Projective R₀ V₀]

def myFunctorish (R : Under R₀) : Type := {M : Submodule R (R ⊗[R₀] V₀) //
    Module.Projective R ((R ⊗[R₀] V₀)⧸M) ∧
    (∀ P : PrimeSpectrum R, Module.rankAtStalk ((R ⊗[R₀] V₀)⧸M) P = d)}

variable {R S : Under R₀} (f : R ⟶ S)



set_option synthInstance.maxHeartbeats 100000

instance foo (M : Submodule R (R ⊗[R₀] V₀)) : AddCommMonoid ((R ⊗[R₀] V₀)⧸M) := by exact
  SubtractionCommMonoid.toAddCommMonoid

def myModA (M : Submodule R (R ⊗[R₀] V₀)) [Module R S] : Submodule R (S ⊗[R] (R ⊗[R₀] V₀)) :=
  LinearMap.range ((Submodule.subtype M).lTensor S)

lemma basechangequotProj (M : Submodule R (R ⊗[R₀] V₀)) (h : Module.Projective R ((R ⊗[R₀] V₀)⧸M)) :
  Module.Projective S (S ⊗[R₀] ((R ⊗[R₀] V₀)⧸M)) := by
  let _ : Module.Projective R₀ (R ⊗[↑R₀] V₀ ⧸ M) := by sorry
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
def myModMap' (M : Submodule R (R ⊗[R₀] V₀)) : Submodule S (S ⊗[R₀] V₀) :=
  letI := f.right.toAlgebra --Turn S into an R-algebra
  -- Commutative triangle R0 -> R -> S commutes
  -- and we tell this to the typeclass system
  haveI : IsScalarTower R₀ R S := .of_algebraMap_eq' f.w
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

lemma mapsurj (M : Submodule R (R ⊗[R₀] V₀)) [Module R S] : Function.Surjective (((Submodule.mkQ M)).lTensor S) :=
  by sorry

lemma mapexact (M : Submodule R (R ⊗[R₀] V₀)) [Module R S] :
    Function.Exact ((Submodule.subtype M).lTensor S) ((Submodule.mkQ M).lTensor S) := by sorry

instance [Module R S] : Module R (S ⊗[R] (R ⊗[R₀] V₀)) := instModule

instance (M : Submodule R (R ⊗[R₀] V₀)) [Module R S] : Module R (LinearMap.range ((Submodule.subtype M).lTensor S)) :=
  (LinearMap.range (LinearMap.lTensor (↑S.right) M.subtype)).module'

instance (M : Submodule R (R ⊗[R₀] V₀)) [Module R S] : ((LinearMap.range ((Submodule.subtype M).lTensor S)) : Submodule R (S ⊗[R] (R ⊗[R₀] V₀))) := by sorry

instance (M : Submodule R (R ⊗[R₀] V₀)) [Module R S] :
    AddCommMonoid (↑S.right ⊗[↑R.right] ↑R.right ⊗[↑R₀] V₀ ⧸ LinearMap.range (LinearMap.lTensor (↑S.right) M.subtype)) := by sorry

instance (M : Submodule R (R ⊗[R₀] V₀)) [Module R S] :
    Module (↑R.right) (↑S.right ⊗[↑R.right] ↑R.right ⊗[↑R₀] V₀ ⧸ LinearMap.range (LinearMap.lTensor (↑S.right) M.subtype)) := by sorry
set_option maxHeartbeats 1000000
/-
lemma equiv1 (M : Submodule R (R ⊗[R₀] V₀)) [Module R S] : ((S ⊗[R] (R ⊗[R₀] V₀)) ⧸ (LinearMap.range ((Submodule.subtype M).lTensor S)))
    ≃ₗ[R] (S ⊗[R] ((R ⊗[R₀] V₀) ⧸ M)) :=
  Function.Exact.linearEquivOfSurjective (mapexact V₀ R₀ M) (mapsurj V₀ R₀ M)
-/
lemma projlem {R M N : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Projective R M] (f : M ≃ₗ[R] N) : Module.Projective R N := by sorry

lemma myModProj (M : Submodule R (R ⊗[R₀] V₀)) [Module.Projective R ((R ⊗[R₀] V₀)⧸M)] :
    Module.Projective S ((S ⊗[R₀] V₀) ⧸ (myModMap' V₀ R₀ f M)) := by
  exact projlem (Function.Exact.linearEquivOfSurjective (mapexact V₀ R₀ M) (mapsurj V₀ R₀ M))
  sorry

/-
lemma myModConstRank (M : Submodule R (R ⊗[R₀] V₀)) [Module.Projective R ((R ⊗[R₀] V₀)⧸M)]
    [∀ P : PrimeSpectrum R, Module.rankAtStalk ((R ⊗[R₀] V₀)⧸M) P = d] :
    ∀ P : PrimeSpectrum S, Module.rankAtStalk ((S ⊗[R₀] V₀) ⧸ (myModMap' V₀ R₀ M)) P = d := by sorry
-/

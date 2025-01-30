import Mathlib

suppress_compilation

open TensorProduct

section playground

variable (R : Type) [CommRing R] (A B : Type) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (M : Type) [AddCommGroup M] [Module R M]
    (N : Type) [AddCommGroup N] [Module R N]
/-
example (φ : A →ₐ[R] B) :
  letI : Algebra A B := RingHom.toAlgebra φ
  IsScalarTower R A B :=
    letI : Algebra A B := RingHom.toAlgebra φ
    SMul.comp.isScalarTower id
-/
variable (φ : M →ₗ[R] N)

example : A ⊗[R] M →ₗ[A] A ⊗[R] N := by exact LinearMap.baseChange A φ

variable (P Q : Type) [AddCommGroup P] [Module A P]
  [AddCommGroup Q] [Module A Q]

variable (T : Type) [AddCommGroup T] [Module A T]
variable (φ : P →ₗ[A] Q)
/-
noncomputable example (α : A →ₐ[R] B) (φ : A ⊗[R] M →ₗ[A] A) : B ⊗[R] M →ₗ[B] B :=
  letI : Algebra A B := RingHom.toAlgebra α
  ((Algebra.TensorProduct.rid A B B).toLinearMap.comp
    (LinearMap.baseChange B φ)).comp
    ((AlgebraTensorModule.cancelBaseChange R A B B M).symm).toLinearMap
-/
--  let ρ : B ⊗[R] M →ₗ[B] (B ⊗[A] A) ⊗[R] M := by exact?
  /-
    B ⊗[R] M = (B ⊗[A] A) ⊗[R] M
             = B ⊗[A] (A ⊗[R] M)
             Now apply 1 ⊗ φ to get to
               B ⊗[A] A
             = B
  -/

end playground

variable (R : CommRingCat.{0})

open CategoryTheory

variable (M : Type) [AddCommGroup M] [Module R M]

def F : Under R ⥤ Type where
  obj A := A ⊗[R] M →ₗ[A] A
  map {A B} f (φ : (A ⊗[R] M) →ₗ[A] A) :=
    letI : Algebra A B := RingHom.toAlgebra (CommRingCat.toAlgHom f)
    haveI : IsScalarTower R A.right B.right := SMul.comp.isScalarTower id
    (((Algebra.TensorProduct.rid A B B).toLinearMap.comp
      (LinearMap.baseChange B φ)).comp
      ((AlgebraTensorModule.cancelBaseChange R A B B M).symm).toLinearMap : (B ⊗[R] M) →ₗ[B] B)
  map_id X := by
    ext
    simp
  map_comp {X Y Z} f g := by
    ext a m
    algebraize [(CommRingCat.toAlgHom f).toRingHom, (CommRingCat.toAlgHom g).toRingHom, (CommRingCat.toAlgHom (f ≫ g)).toRingHom]
    have bar : a ((1 : X) ⊗ₜ[↑R] m) • (1 : Z) = (a ((1 : X) ⊗ₜ[↑R] m) • (1 : Y)) • (1 : Z) := by
      simp only [Algebra.smul_def, mul_one]; rfl
    simp only [CommRingCat.toAlgHom_comp, AlgebraTensorModule.curry_apply,
      LinearMap.restrictScalars_comp, curry_apply, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, Function.comp_apply,
      AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul,
      AlgEquiv.toLinearMap_apply, Algebra.TensorProduct.rid_tmul, bar, types_comp_apply]

-- assume M has a finite basis
def corepresentableOfBasis (ι : Type) [Finite ι] (b : Basis ι R M) :
  Functor.CorepresentableBy (F R M) <| CommRingCat.mkUnder R (MvPolynomial ι R) where
    homEquiv {A} := {
      toFun := sorry
      invFun := sorry
      left_inv := sorry
      right_inv := sorry
    } -- need to write down the bijection (an equiv)
    homEquiv_comp {A B} f α := sorry

import Mathlib
--set_option autoImplicit false

suppress_compilation

open TensorProduct

open CategoryTheory

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
section

variable (R : CommRingCat.{0})

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

@[simps]
def F' : Under R ⥤ Type where
  obj A := M →ₗ[R] A
  map {A _} f (φ : M →ₗ[R] A) := (LinearMap.comp (CommRingCat.toAlgHom f).toLinearMap φ)
  map_id _ := rfl
  map_comp {_ _ _} _ _ := rfl

end section

section

variable (R : CommRingCat.{0})
variable (M : Type) [AddCommGroup M] [Module R M] (ι : Type) [Finite ι] (b : Basis ι R M)
  (B : Under R)

@[simps!]
def foo1 : (ι → B) ≃ (M →ₗ[R] B) := by
 exact ((Basis.constr b R) : (ι → B) ≃ₗ[R] M →ₗ[R] B).toEquiv

@[simps]
def foo2 : ((MvPolynomial ι R) →ₐ[R] B) ≃ (ι → B) where
  toFun f i := f (MvPolynomial.X i)
  invFun g := MvPolynomial.aeval g
  left_inv := by
    intro f
    ext
    simp
  right_inv := by
    intro f
    ext
    simp


@[simps!]
def foo3 : ((MvPolynomial ι R) →ₐ[R] B) ≃ (M →ₗ[R] B) := by
  exact Equiv.trans (foo2 R ι B) (foo1 R M ι b B)

abbrev foo4 (A : Under R) (B : Type) [CommRing B] [Algebra R B] : (R.mkUnder B ⟶ A) ≃ (B →ₐ[R] A.right) where
  toFun f :=
    { __ :=CommRingCat.toAlgHom f, commutes' := by
        simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
          MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe]
        intro r
        exact AlgHom.commutes (CommRingCat.toAlgHom f) r
        }
  invFun g := AlgHom.toUnder g
  left_inv f := by
    ext x
    simp
    rfl
  right_inv g := by
    ext x
    simp
    rfl

/-
example : ((MvPolynomial ι R) →ₗ[R] B) ≃ (ι → B) where
  toFun f := by
    intro i
    exact f (MvPolynomial.X i)
  invFun g := by
    let b' := MvPolynomial.basisMonomials ι R

    sorry
  left_inv := _
  right_inv := _
-/
-- assume M has a finite basis
def corepresentableOfBasis (ι : Type) [Finite ι] (b : Basis ι R M) :
  Functor.CorepresentableBy (F' R M) <| CommRingCat.mkUnder R (MvPolynomial ι R) where
    homEquiv {A} := Equiv.trans (by exact foo4 R A (MvPolynomial ι ↑R)) (foo3 R M ι b A)
    homEquiv_comp {A B} f α := by
      apply b.ext
      intro i
      simp

end section

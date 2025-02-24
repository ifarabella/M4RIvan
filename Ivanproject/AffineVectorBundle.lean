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

-- assume M has a finite basis
def corepresentableOfBasis (ι : Type) [Finite ι] (b : Basis ι R M) :
  Functor.CorepresentableBy (F' R M) <| CommRingCat.mkUnder R (MvPolynomial ι R) where
    homEquiv {A} := Equiv.trans (foo4 R A (MvPolynomial ι ↑R)) ((Equiv.trans (foo2 R ι A) (((Basis.constr b R) : (ι → A) ≃ₗ[R] M →ₗ[R] A).toEquiv)))
    homEquiv_comp {A B} f _ := by
      apply b.ext
      intro i
      simp

end section

variable (R : CommRingCat.{0})

variable (M : Type) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
--!!
--THE FOLLOWING ARE 'BAD' VARIABLES: WANT TO GET THEM FROM Module.FinitePresentation.equiv_quotient
--!!
variable (L ι β : Type) (_ : AddCommGroup L) (_ : Module R L) (K : Submodule R L) (_ : M ≃ₗ[R] L ⧸ K)
      (_ : Finite ι) (_ : Finite β) (lb : Basis β R L ) (kb : Basis ι R K)
      (φ : (MvPolynomial ι R) →ₗ[R] (MvPolynomial β R))

def ignorevar (B : Under R)  : (MvPolynomial ι R) →ₐ[R] B where
  toFun := MvPolynomial.aeval (fun _ => 0)
  map_one' := map_one (MvPolynomial.aeval fun _ ↦ 0)
  map_mul' := fun x y ↦ map_mul (MvPolynomial.aeval fun _ ↦ 0) x y
  map_zero' := rfl
  map_add' := fun x y ↦ map_add (MvPolynomial.aeval fun _ ↦ 0) x y
  commutes' := fun r ↦ AlgHom.commutes (MvPolynomial.aeval fun _ ↦ 0) r

abbrev representor := ((MvPolynomial β R) ⧸ (Ideal.span {b : MvPolynomial β R | ∃ (i : ι), (φ (MvPolynomial.X i)) = b}))

abbrev foo5 (B : Under R) : (M →ₗ[R] B) ≃ {α : ((MvPolynomial β R) → B) // α ∘ φ = (ignorevar R ι B)} where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

abbrev subtype_equiv_rep (B : Under R) : ((representor R ι β φ) →ₐ[R] B) ≃ {α : ((MvPolynomial β R) → B) // α ∘ φ = (ignorevar R ι B)} where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

def corepresentableOfFinitePresentation  :
    Functor.CorepresentableBy (F' R M) (CommRingCat.mkUnder R ((MvPolynomial β R) ⧸ (Ideal.span {b : MvPolynomial β R | ∃ (i : ι), (φ (MvPolynomial.X i)) = b}))) where
      homEquiv {A} :=
        Equiv.trans (foo4 R A (MvPolynomial β ↑R ⧸ Ideal.span {b | ∃ i, φ (MvPolynomial.X i) = b}))
        (Equiv.trans (subtype_equiv_rep R ι β φ A) (foo5 R M ι β φ A).symm)
      homEquiv_comp {A B} f _ := by
        sorry


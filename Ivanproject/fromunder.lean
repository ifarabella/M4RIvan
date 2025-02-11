import Mathlib

section
variable (R : CommRingCat.{0})
/-
lemma foo (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    CommRingCat.toAlgHom (AlgHom.toUnder f) = f := by sorry
-/

def fromUnder {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : CommRingCat.mkUnder R A ⟶ CommRingCat.mkUnder R B) : A →ₐ[R] B := by
  let i1 : Algebra ↑R ↑(R.mkUnder A).right := inferInstance
  let g := CommRingCat.toAlgHom f
  have h : A = ↑(R.mkUnder A).right := rfl
  have h1 : B = ↑(R.mkUnder B).right := rfl
  convert_to ↑(R.mkUnder A).right →ₐ[↑R] ↑(R.mkUnder B).right
  · exact Algebra.algebra_ext _ i1 (congrFun rfl)
  · apply Algebra.algebra_ext
    intro r
    rfl
  · exact g
end section

open TensorProduct CategoryTheory Limits

variable (A : Under R) (B : Type) [CommRing B] [Algebra R B] in
example : (R.mkUnder B ⟶ A) ≃ (B →ₐ[R] A.right) where
  toFun f :=
    { __ :=CommRingCat.toAlgHom f, commutes' r := by
        simp
        sorry }
  invFun g := AlgHom.toUnder g
  left_inv f := by
    ext x
    simp
    rfl
  right_inv g := by
    ext x
    simp
    rfl

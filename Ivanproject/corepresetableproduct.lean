import Mathlib

open CategoryTheory
open TensorProduct

noncomputable section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {R : CommRingCat} {F : Under R ⥤ Type} {G : Under R ⥤ Type}
{A : Under R} {B : Under R}

#check CategoryTheory.Functor.prod

/--Application of the universal property of tensor product in the case that the codomain is
commutative-/
abbrev Product_AlgHom_ofTensorProduct (S : Under R) : ((A →ₐ[R] S) × (B →ₐ[R] S)) ≃ ((A ⊗[R] B) →ₐ[R] S) where
  toFun f := Algebra.TensorProduct.productLeftAlgHom f.fst f.snd
  invFun g := (g.comp Algebra.TensorProduct.includeLeft, (g.restrictScalars R).comp Algebra.TensorProduct.includeRight)
  left_inv fg := by ext <;> simp
  right_inv fg' := by ext <;> simp

/-
!!!!!!!!!!!!!
Stuck on getting the Lean correct, the above equiv is the maths part, does F ⨯ G work or
do I need F.prod' G ?
!!!!!!!!!
-/
variable (e : F.CorepresentableBy A) (e' : G.CorepresentableBy B)
def CorepresentableBy_of_product :
    (F ⨯ G).CorepresentableBy (A ⨯ B) where
      homEquiv {Y} := sorry
      homEquiv_comp := sorry

#check PiTensorProduct

def Corepresentable_of_PiTensorProduct :

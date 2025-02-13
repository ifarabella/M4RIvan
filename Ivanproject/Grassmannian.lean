import Mathlib
import Ivanproject.Basic

open TensorProduct
open CategoryTheory

variable (d : ℕ) (V₀: Type) (R₀ : CommRingCat.{0}) [AddCommGroup V₀] [Module R₀ V₀]  --(x: Under R₀)
    [Module.Projective R₀ V₀] [Module.Finite R₀ V₀]

--how can i make this definition without using tactic mode
/--given a map of R₀ -algebras, `typemap` is the induced map on the objects of the Grassmannian-/
noncomputable def typemap (R S : Under R₀) [Algebra R S] [IsScalarTower R₀ R S] :
    (myFunctorish d V₀ R₀ R → myFunctorish d V₀ R₀ S) := by
  intro M
  let h0 := M.property
  unfold myFunctorish at *
  let M' := myModMap' V₀ R₀ S (M : Submodule (↑R.right) (↑R.right ⊗[↑R₀] V₀))
  have _ : Module.Projective (↑R.right) (↑R.right ⊗[↑R₀] V₀ ⧸ M.val) := h0.left
  let h1 := @myModProj1 V₀ R₀ _ _ R S _ _ (M : Submodule (↑R.right) (↑R.right ⊗[↑R₀] V₀)) _
  let h2 := @myModConstRank d V₀ R₀ _ _ _ R S _ _ M.val _ M.property.right
  use myModMap' V₀ R₀ S (M : Submodule (↑R.right) (↑R.right ⊗[↑R₀] V₀))

def myModMapId (R : Under R₀) (M : Submodule R (R ⊗[R₀] V₀)) : myModMap' V₀ R₀ R M = M := by
  rw [← mymodeq V₀ R₀ M]
  
  sorry

noncomputable def Grass : Under R₀ ⥤ Type where
  obj R := myFunctorish d V₀ R₀ R
  map {R S} f (M : myFunctorish d V₀ R₀ R) := by --again, how to avoid using tactic mode?
    letI : Algebra R S := RingHom.toAlgebra (CommRingCat.toAlgHom f)
    haveI : IsScalarTower R₀ R S := SMul.comp.isScalarTower id
    exact (((typemap d V₀ R₀ R S) M ) : myFunctorish d V₀ R₀ S)
  map_id R:= by
    simp only [CommRingCat.toAlgHom_id, AlgHom.id_toRingHom]
    ext M
    simp only [types_id_apply]
    rw [typemap]
    simp only [id_eq]
    let h := myModMapId V₀ R₀ R M.val

    sorry
  map_comp := sorry

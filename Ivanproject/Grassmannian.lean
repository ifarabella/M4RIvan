import Mathlib
import Ivanproject.Basic

open TensorProduct
open CategoryTheory

variable (d : ℕ) (V₀: Type) (R₀ : CommRingCat.{0}) [AddCommGroup V₀] [Module R₀ V₀]  --(x: Under R₀)
    [Module.Projective R₀ V₀] [Module.Finite R₀ V₀]

--how can i make this definition without using tactic mode
/--given a map of R₀ -algebras, `typemap` is the induced map on the objects of the Grassmannian-/
noncomputable def typemap (R S : Under R₀) [Algebra R S] [IsScalarTower R₀ R S] (M : myFunctorish d V₀ R₀ R) :
    myFunctorish d V₀ R₀ S :=
  let h0 := M.property
  have _ : Module.Projective (↑R.right) (↑R.right ⊗[↑R₀] V₀ ⧸ M.val) := h0.left
  let h1 := @myModProj1 V₀ R₀ _ _ R S _ _ (M : Submodule (↑R.right) (↑R.right ⊗[↑R₀] V₀)) _
  let h2 := @myModConstRank d V₀ R₀ _ _ _ R S _ _ M.val _ M.property.right
  ⟨myModMap' V₀ R₀ S (M : Submodule (↑R.right) (↑R.right ⊗[↑R₀] V₀)), by simp_all⟩

omit [Module.Projective (↑R₀) V₀] in
@[simp]
lemma typemap_val (R S : Under R₀) [Algebra R S] [IsScalarTower R₀ R S]
    (M : myFunctorish d V₀ R₀ R) :
    (typemap d V₀ R₀ R S M).val =
      myModMap' V₀ R₀ S (M : Submodule (↑R.right) (↑R.right ⊗[↑R₀] V₀)) := rfl

-- missing?
-- if `a ∈ A ⊗[A] N` and `b` is the image of `a` under the obvious map `A ⊗[A] N = N`
-- then `a = 1 ⊗ b`
theorem foo38 (A : Type) [CommRing A] (N : Type) [AddCommGroup N] [Module A N] (an : A ⊗[A] N) :
  1 ⊗ₜ (TensorProduct.lid A N an) = an := by
  let g := @lid_symm_apply A _ _ _ _ (TensorProduct.lid A N an)
  simp only [LinearEquiv.symm_apply_apply] at g
  exact id (Eq.symm g)

--  cancelBaseChange : R ⊗[R] R ⊗[R₀] N ≃ₗ[R] R ⊗[R₀] N sends 1 ⊗ x to x
lemma foo37 (R : Under R₀) (N : Type) [AddCommGroup N] [Module R₀ N] (x : R ⊗[R₀] N) :
    (AlgebraTensorModule.cancelBaseChange (↑R₀) (↑R.right) (↑R.right) (↑R.right) N) (1 ⊗ₜ[↑R.right] x) = x := by
  let g := AlgebraTensorModule.cancelBaseChange_symm_tmul R₀ R R (1 : R) x
  dsimp only [AlgebraTensorModule.cancelBaseChange_symm_tmul] at g
  induction x
  · simp
  · simp
  · simp_all [tmul_add]



def myModMapId (R : Under R₀) (M : Submodule R (R ⊗[R₀] V₀)) : myModMap' V₀ R₀ R M = M := by
  rw [← mymodeq V₀ R₀ M]
  ext x
  simp only [Submodule.mem_map, LinearMap.mem_range, exists_exists_eq_and]
  refine ⟨?_, ?_⟩
  · rintro ⟨a, ha⟩
    rw [← foo38 _ _ a] at ha
    simp at ha
    rw [foo37] at ha
    rw [← ha]
    simp
  · intro hx
    use 1 ⊗ₜ ⟨x, hx⟩
    simp
    clear hx
    exact foo37 R₀ R V₀ x

noncomputable def Grass : Under R₀ ⥤ Type where
  obj R := myFunctorish d V₀ R₀ R
  map {R S} f (M : myFunctorish d V₀ R₀ R) := --again, how to avoid using tactic mode?
    letI : Algebra R S := RingHom.toAlgebra (CommRingCat.toAlgHom f)
    haveI : IsScalarTower R₀ R S := SMul.comp.isScalarTower id
    (((typemap d V₀ R₀ R S) M ) : myFunctorish d V₀ R₀ S)
  map_id R:= by
    simp only [CommRingCat.toAlgHom_id, AlgHom.id_toRingHom]
    ext M x
    simp only [types_id_apply]
    rw [typemap]
    simp only [id_eq]
    let h := myModMapId V₀ R₀ R M.val
    simp [h]
  map_comp := by
    intro X Y Z f g
    --ext y z
    simp only [CommRingCat.toAlgHom_comp, typemap_val, types_comp_apply]
    unfold typemap
    --have h :
    sorry
    --have h : typemap d V₀ R₀ X Z M = (typemap d V₀ R₀ X Y M typemap d V₀ R₀ Y Z M

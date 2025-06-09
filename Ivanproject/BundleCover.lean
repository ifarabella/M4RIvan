import Mathlib
open CategoryTheory
open TensorProduct
section
variable {R : CommRingCat} {M : Type} [AddCommGroup M] [Module R M] {n : ℕ} {x : Fin n → M}
/-Some code concerning the functor F_{x,V_0} from the report-/
noncomputable def induced (S : Under R) : (((Fin n) → S) →ₗ[S] (S ⊗[R] M)) := by sorry

noncomputable def induced' (S : Under R) (b : Basis (Fin n) S (Fin n → S)) : (((Fin n) → S) →ₗ[S] (S ⊗[R] M)) :=
  Basis.constr b S (fun i => (1 ⊗ₜ (x i) : S ⊗[R] M))

variable (S T : Under R) (ψ : S ⟶ T) (b : Basis (Fin n) S (Fin n → S)) (b' : Basis (Fin n) T (Fin n → T))
variable [Algebra S T] [IsScalarTower R S T]

set_option synthInstance.maxHeartbeats 200000

noncomputable abbrev foo := (AlgebraTensorModule.cancelBaseChange R S T T M).symm.toLinearMap

lemma commutes :
    LinearMap.comp (foo S T) (@induced' R M _ _ _ x T b') =
      LinearMap.comp (LinearMap.baseChange T (@induced' R M _ _ _ x S b)) (piScalarRight S T T (Fin n)).symm.toLinearMap := by sorry

#check Module.basisOfFiniteTypeTorsionFree'.proof_1
#check LinearMap.stdBasis
#check piScalarRight
#check Basis.constr_def
end section
section
variable {R : CommRingCat} {M : Type} [AddCommGroup M] [Module R M] {n : ℕ} {x : Fin n → M}
--induced here will probably break after defining induced
def Fₓ : Under R ⥤ Type where
  obj {S} := {φ : (S ⊗[R] M) →ₗ[S] (Fin n → S) // LinearMap.comp φ (induced S) = LinearMap.id }
  map {S T} ψ φ := by
    letI : Algebra S T := RingHom.toAlgebra (CommRingCat.toAlgHom ψ)
    haveI : IsScalarTower R S T := SMul.comp.isScalarTower id
    let f1 := (AlgebraTensorModule.cancelBaseChange R S T T M).symm.toLinearMap
    let f2 := LinearMap.baseChange T φ.val
    let f3 := (piScalarRight S T T (Fin n)).toLinearMap
    let f' := LinearMap.comp f2 f1
    let f := LinearMap.comp f3 f'
    let h1 := @LinearMap.baseChange_comp _ T (Fin n → S) _ _ _ _ _ _ _ _ _ _ _ (@induced R M _ _ _ S) φ.val
    simp only [φ.property, LinearMap.baseChange_id] at h1
    sorry
  map_id := sorry
  map_comp := sorry
end section

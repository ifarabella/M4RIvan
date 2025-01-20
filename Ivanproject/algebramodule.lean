import Mathlib
open TensorProduct

variable (R S R₀ M : Type) [CommRing R₀] [CommRing R] [CommRing S] [Algebra R₀ R] [Algebra R₀ S]
    [AddCommGroup M] [Module R₀ M] [Module.Projective R₀ M]

instance tensorCor : Module.Projective S (S ⊗[R₀] M) := Module.Projective.tensorProduct

variable (R S R₀ M V₀: Type) [CommRing R₀] [CommRing R] [CommRing S] [Algebra R₀ R] [Algebra R₀ S]
    [AddCommGroup M] [Module R M] [Module.Projective R M] (f : R → S) [AddCommGroup V₀] [Module R₀ V₀]
    [Module.Projective R₀ V₀]

instance algHom : Module R S := by sorry

instance foo : S ⊗[R] S := by sorry
variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M)

lemma foo' : Function.Surjective (Submodule.mkQ N) := by exact Submodule.mkQ_surjective N

lemma foo'' (N : Type) [AddCommGroup N] [Module R N] (g : M ≃ₗ[R] N) : Module.Projective R N := by
    sorry

variable (R S M : Type) [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [Module S M] [Algebra R S] (N : Submodule R M)

--example (P : PrimeSpectrum R) (h1 : Module.Projective R (M ⧸ N)) (h2 : Module.rankAtStalk (M ⧸ N) (Submodule.comap (algebraMap R S) P) = d) :
   --Module.rankAtStalk (S ⊗[R] (M ⧸ N)) P
section
variable {R : Type} [CommSemiring R] (S : Submonoid R) (P : PrimeSpectrum R)
variable (M N : Type) [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

open OreLocalization
open Monoid
namespace OreLocalization

lemma suffices1 (f : M →ₗ[R] N) [Module (Localization S) M] [Module (Localization S) N] [IsScalarTower R (Localization S) M]
    (r : R) (s : S) (x : M) :
    --(s • (f ((r /ₒ s) • x)) = r • f x)
    s • (f ((Localization.mk r s) • x)) = r • f x
    := by
  rcases s with ⟨s, hs⟩
  simp only [Submonoid.mk_smul]
  rw [← map_smul]
  rw [← smul_assoc]
  rw [Localization.smul_mk]
  have h' : Localization.mk (s • r) ⟨s, hs⟩ = Localization.mk r 1 := by
    rw [Localization.mk_eq_mk_iff]
    simp only [smul_eq_mul]
    rw [Localization.r_iff_exists]
    use 1
    simp only [OneMemClass.coe_one, one_mul]

  have h : Localization.mk (s • r) ⟨s, hs⟩ = algebraMap R (Localization S) r := by
    rw [h']
    rfl
  rw [h, ← map_smul]
  congr 1
  exact algebraMap_smul (Localization S) r x

lemma localsmul (f : M →ₗ[R] N) [Module (Localization S) M] [Module (Localization S) N] [IsScalarTower R (Localization S) M]
    (c : OreLocalization S R) (x : M) : f (c • x) = c • f x := by
  induction' c with r s
  rw [← Localization.mk]
  have h : (s • (f ((Localization.mk r s) • x)) = r • f x) := suffices1 S M N f r s x;-- suffices1 S M N f r s x
  have h1 : (s • (f ((Localization.mk r s) • x))) = f ((s • (Localization.mk r s)) • x) := by
    sorry
  have h2 : s • (Localization.mk r s) = Localization.mk r 1  := by sorry
  have h3 : f ((s • (Localization.mk r s)) • x) = f (r • x) := by sorry

  sorry
#check LinearMap.extendScalarsOfIsLocalization

example (f : M →ₗ[R] N) [Module (Localization S) M] [Module (Localization S) N] [IsScalarTower R (Localization S) M] :
    IsLinearMap (Localization S) f where
      map_add :=  LinearMap.map_add f
      map_smul c x := localsmul S M N f c x


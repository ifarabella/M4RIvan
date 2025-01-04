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

variable (R S M : Type) (d : ℕ) [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [Module S M] [Algebra R S] (N : Submodule R M)

--example (P : PrimeSpectrum R) (h1 : Module.Projective R (M ⧸ N)) (h2 : Module.rankAtStalk (M ⧸ N) (Submodule.comap (algebraMap R S) P) = d) :
    --Module.rankAtStalk (S ⊗[R] (M ⧸ N)) P

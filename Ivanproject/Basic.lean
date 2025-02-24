import Mathlib
universe u

/-
suppress_compilation

open MvPolynomial

variable (R : Type ) [CommRing R]

open GradedAlgebra

open AlgebraicGeometry
attribute [instance] gradedAlgebra

variable (n : ℕ)

noncomputable abbrev Pn := Proj (homogeneousSubmodule (Fin (n + 1)) ℤ)

open Scheme

#check Hom (Spec (.of R)) $ Pn 7
--want 2nd functor, made up of 'locally rank n direct summands of Tⁿ⁺¹, K'
--define this as Tⁿ⁺¹⧸K is an invertible module
-- an invertible T - module is a f.g. locally free T-module of rank 1.
--locally free
--class InvertibleModule (R M : Type) [CommRing R] [AddCommMonoid M] [Module R M] :
        --Prop where
    --out : ∃ (h1 : Module.Finite R M) (h2 : Module.Projective R M),
    --∀ (p : Ideal R) (h4 : p.IsPrime),
    --(Module.rank ( (Localization.AtPrime p) (Module.LocalizedModule M p)) = 1)
-/

open CategoryTheory
open TensorProduct


lemma free_of_finite_IsLocalRing (R : Type*) [CommRing R] [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M]
  (h : Module.Projective R M) [Module.Finite R M] : Module.Free R M := by
  let h := Module.finitePresentation_of_projective R M
  exact Module.free_of_flat_of_isLocalRing


noncomputable section
variable {R : Type} [CommSemiring R] (S : Submonoid R) (P : PrimeSpectrum R)
variable (M : Type) [AddCommMonoid M] [Module R M]

open TensorProduct

/--Given an `R`-module `M`, an `R`-submonoid `S`, `localLinEq` gives an `R`-linear equivalence
between the localization of `M` by `S` and `R[S⁻¹] ⊗[R] M` -/
noncomputable def localLinEq : LocalizedModule S M ≃ₗ[Localization S] (Localization S) ⊗[R] M :=
  (IsLocalizedModule.isBaseChange S _ <| LocalizedModule.mkLinearMap S M).equiv.symm
end section

noncomputable section

-- pull back prime of S to prime of R
variable (R S M : Type) [CommRing R] [CommRing S] [Algebra R S]
    (Q : PrimeSpectrum S) (P : PrimeSpectrum R) [AddCommGroup M] [Module R M]
    (h' : P.asIdeal = Ideal.comap (algebraMap R S) Q.asIdeal) (d : ℕ)

--map from R_P to S_Q if P := f^{-1}(Q), f : R → S
/-- `RingHom` from `Rₚ` to `S_Q` if `P = f⁻¹(Q)`-/
def mylocalmap : Localization.AtPrime P.asIdeal →+*
    Localization.AtPrime Q.asIdeal :=
  Localization.localRingHom P.asIdeal Q.asIdeal (algebraMap R S) h'

-- map R -> R_P
example : R →+* Localization.AtPrime P.asIdeal := algebraMap R (Localization.AtPrime P.asIdeal)

-- square R -> S -> S_Q and R -> R_P -> S_Q commutes
lemma localizedalgebraMapComm : ((algebraMap S (Localization.AtPrime Q.asIdeal)).comp (algebraMap R S) :
    R →+* Localization.AtPrime Q.asIdeal) =
    (Localization.localRingHom P.asIdeal Q.asIdeal (algebraMap R S) <| h').comp
      (algebraMap R (Localization.AtPrime P.asIdeal)) := by
  ext x
  symm
  apply Localization.localRingHom_to_map P.asIdeal Q.asIdeal
  exact h'

--just use the paper proof.
/--For a prime `P` of `R`, `localLinEqlocal` returns the `Rₚ`-linear equivalence
 `Mₚ ≃ₗ[Rₚ] Rₚ ⊗[R] M` coming from `localLinEq`-/
def localLinEqlocal : LocalizedModule P.asIdeal.primeCompl M ≃ₗ[Localization.AtPrime P.asIdeal] Localization P.asIdeal.primeCompl ⊗[R] M := by
  exact localLinEq P.asIdeal.primeCompl M

--saying that M ⊗[R] Rₚ is locally rank d if rankAtStalk M P = d
lemma rankalgebraMaprankAtStalk (h : Module.rankAtStalk M P = d) :
    Module.finrank (Localization.AtPrime P.asIdeal) (Localization.AtPrime P.asIdeal ⊗[R] M) = d := by
  rw [Module.rankAtStalk] at h
  let g' := localLinEqlocal R M P
  have h1 := LinearEquiv.finrank_eq g'
  rw [h1] at h
  rw [← h]

lemma rankalgebraMaprankAtStalksymm (h : Module.finrank (Localization.AtPrime P.asIdeal) (Localization.AtPrime P.asIdeal ⊗[R] M) = d) :
    Module.rankAtStalk M P = d := by
  rw [Module.rankAtStalk]
  let g := localLinEq (P.asIdeal.primeCompl) M
  let g' := localLinEqlocal R M P
  have h1 := LinearEquiv.finrank_eq g'
  rw [h1]
  exact h

/-- The rank of `Mₚ` as an `Rₚ`-module is equal to the rank of `Rₚ ⊗[R] M` as an `Rₚ`-module-/
lemma rankAtStalkEqfinrank_iff :
    Module.finrank (Localization.AtPrime P.asIdeal) (Localization.AtPrime P.asIdeal ⊗[R] M) = d ↔
    Module.rankAtStalk M P = d := by
  constructor
  ·exact fun a ↦ rankalgebraMaprankAtStalksymm R M P d a
  ·exact fun a ↦ rankalgebraMaprankAtStalk R M P d a

lemma rankalgebraMaprankAtStalksymm' : (Module.finrank (Localization.AtPrime P.asIdeal) (Localization.AtPrime P.asIdeal ⊗[R] M) = d) → (Module.rankAtStalk M P = d) := by
  intro h
  exact rankalgebraMaprankAtStalksymm R M P d h
--instance : Module (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q.asIdeal) := by sorry

/-
example : Module.rankAtStalk (S ⊗[R] M) Q =
    Module.finrank (Localization.AtPrime Q.asIdeal)
    (((M ⊗[R] (Localization.AtPrime P.asIdeal)) ⊗[Localization.AtPrime P.asIdeal] (Localization.AtPrime Q.asIdeal))) := by sorry
-/
/-
instance : Module (Localization.AtPrime P.asIdeal) (M ⊗[R] Localization.AtPrime P.asIdeal) := by
  let h := algebraMap R (Localization.AtPrime P.asIdeal)
  have : Module R ((M ⊗[R] Localization.AtPrime P.asIdeal)) := instModule
  sorry
-/

variable [h' : Fact (P.asIdeal = Ideal.comap (algebraMap R S) Q.asIdeal)]

instance : Module (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q.asIdeal) := (Localization.localRingHom P.asIdeal Q.asIdeal (algebraMap R S) h'.elim).toModule

--dont need
instance locinst1 : Module (Localization.AtPrime Q.asIdeal)
    (Localization.AtPrime Q.asIdeal ⊗[Localization.AtPrime P.asIdeal] Localization.AtPrime P.asIdeal ⊗[R] M) := leftModule

instance : Algebra (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q.asIdeal) := (Localization.localRingHom P.asIdeal Q.asIdeal (algebraMap R S) h'.elim).toAlgebra

open Module Localization

instance : IsScalarTower R (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q.asIdeal) where
      smul_assoc x y z := by
        simp only [Algebra.smul_def, map_mul, mul_assoc]
        congr 1
        exact Localization.localRingHom_to_map P.asIdeal Q.asIdeal _ h'.elim x


lemma rankalgebraMaprankAtStalkup [Module.Free (Localization.AtPrime P.asIdeal) (Localization.AtPrime P.asIdeal ⊗[R] M)]
  (h : Module.rankAtStalk M P = d) :
    Module.rankAtStalk (S ⊗[R] M) Q = d := by
  rw [← rankAtStalkEqfinrank_iff R M P d] at h
  --let h1 := rankalgebraMaprankAtStalk R M P d h
  let _ : Module (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q.asIdeal) := inferInstance
  let _ : Module (Localization.AtPrime Q.asIdeal)
    (Localization.AtPrime Q.asIdeal ⊗[Localization.AtPrime P.asIdeal] Localization.AtPrime P.asIdeal ⊗[R] M) := leftModule
  have h2 : Module.finrank (Localization.AtPrime Q.asIdeal) (Localization.AtPrime Q.asIdeal ⊗[Localization.AtPrime P.asIdeal] (Localization.AtPrime P.asIdeal ⊗[R] M)) = d := by
    let h3 := @Module.finrank_baseChange (Localization.AtPrime Q.asIdeal) (Localization.AtPrime P.asIdeal) (Localization.AtPrime P.asIdeal ⊗[R] M) _ _ _ _ _ _ _ _
    rw [h3]
    exact h
  have h3 : Module.finrank (Localization.AtPrime Q.asIdeal) (Localization.AtPrime Q.asIdeal ⊗[R] M) = d := by
    let h4 : IsScalarTower R (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q.asIdeal) := by infer_instance
    have := @AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q.asIdeal) (Localization.AtPrime Q.asIdeal) M _ _ _ _ _ _ _ _ _ h4 _ _ _ _ _ _
    rw [← h2]
    exact (LinearEquiv.finrank_eq this).symm
  have h4 : Module.finrank (Localization.AtPrime Q.asIdeal) (Localization.AtPrime Q.asIdeal ⊗[S] S ⊗[R] M) = d := by
    let g := AlgebraTensorModule.cancelBaseChange R S (Localization.AtPrime Q.asIdeal) (Localization.AtPrime Q.asIdeal) M
    let h5 := @LinearEquiv.finrank_eq (Localization.AtPrime Q.asIdeal) (Localization.AtPrime Q.asIdeal ⊗[S] S ⊗[R] M) _ _ _ _ _ _ g
    rw [h5]
    exact h3
  rw [← rankAtStalkEqfinrank_iff _ _ _ d]
  exact h4

end section

noncomputable section
--for grassmannian i think V₀ will be Rⁿ⁻¹ or something.
variable (d : ℕ) (V₀: Type) (R₀ : CommRingCat.{0}) [AddCommGroup V₀] [Module R₀ V₀]  --(x: Under R₀)
    [Module.Projective R₀ V₀] [Module.Finite R₀ V₀]

/--A Type denoting R-submodules of (R ⊗[R₀] V₀) such that (R ⊗[R₀] V₀) ⧸ M is projective and locally
free of rank d. -/
abbrev myFunctorish (R : Under R₀) : Type := {M : Submodule R (R ⊗[R₀] V₀) //
    Module.Projective R ((R ⊗[R₀] V₀) ⧸ M) ∧
    (∀ P : PrimeSpectrum R, Module.rankAtStalk ((R ⊗[R₀] V₀)⧸M) P = d)}

variable {R S : Under R₀} [Algebra R S] [IsScalarTower R₀ R S]

instance foo (M : Submodule R (R ⊗[R₀] V₀)) : AddCommMonoid ((R ⊗[R₀] V₀)⧸M) := by exact
  SubtractionCommMonoid.toAddCommMonoid

def myModA (M : Submodule R (R ⊗[R₀] V₀)) :
  Submodule R (S ⊗[R] (R ⊗[R₀] V₀)) :=
  LinearMap.range ((Submodule.subtype M).lTensor S)

-- let R and S be R_0-algebras and let f: R → S be an R_0-algebra hom
-- myModMap is a function which eats an R-submod of R ⨂ V_0 and returns an S-submod of S ⊗ V_0
variable (S) in
abbrev myModMap (M : Submodule R (R ⊗[R₀] V₀)) := ((AlgebraTensorModule.cancelBaseChange R₀ R S S V₀).toLinearMap ∘ₗ (M.subtype.baseChange (S)))

variable (S) in
/--Returns the image of a `R ⊗[R₀] V₀` submodule `M` under the map -/
def myModMap' (M : Submodule R (R ⊗[R₀] V₀)) : Submodule S (S ⊗[R₀] V₀) :=
  -- Commutative triangle R0 -> R -> S commutes
  -- and we tell this to the typeclass system
  -- `M` = R-submodule of `R ⊗[R0] V0`
  -- `M.subtype` = obvious injective R-linear map `M -> R ⊗[R0] V0`
  -- `M-subtype.baseChange S` = base-changed map `S ⊗[R] M -> S ⊗[R] (R ⊗[R0] V0)`
  -- We're going to compose this map with something else, which is the map
  -- `S ⊗[R] (R ⊗[R0] V0) ---(obvious)---> (S ⊗[R] R) ⊗[R0] V0 ---("mul_one")--> S ⊗[R0] V0`
  -- and we'll get a map `S ⊗[R] M -> S ⊗[R0] V0`
  -- Now take the image (LinearMap.range)
  LinearMap.range (myModMap V₀ R₀ S M)
  --M.map ((IsScalarTower.toAlgHom R₀ R S).toLinearMap.rTensor V₀)

--def myFunct (d : ℕ) : CommRingCat ⥤ Type _ where
  --obj R := {M : Submodule R ((Fin n) → R) // Module.Projective R ((Fin n → R)⧸M) ∧ (∀ P : PrimeSpectrum R, Module.rankAtStalk ((Fin n → R)⧸M) P = d) }
  --map {R S} f M := ⟨(M.subtype.lTensor S).range, _ ⟩ --LinearMap.lTensor
  --map_id := _
  --map_comp := _

variable (S) in
omit [Module.Projective (↑R₀) V₀] [IsScalarTower ↑R₀ ↑R.right ↑S.right] [Module.Finite (↑R₀) V₀] in
lemma mapsurj (M : Submodule R (R ⊗[R₀] V₀)) :
    Function.Surjective ((Submodule.mkQ M).baseChange S) :=
  LinearMap.lTensor_surjective (↑S.right) (Submodule.mkQ_surjective M )

variable (S) in
omit [Module.Projective (↑R₀) V₀] [IsScalarTower ↑R₀ ↑R.right ↑S.right] [Module.Finite (↑R₀) V₀] in
lemma mapexact (M : Submodule R (R ⊗[R₀] V₀)) :
    Function.Exact ((Submodule.subtype M).baseChange S) ((Submodule.mkQ M).baseChange S) := by
  have foo : Function.Exact (Submodule.subtype M) (Submodule.mkQ M) := LinearMap.exact_subtype_mkQ M
  have foo' : Function.Surjective (Submodule.mkQ M) := Submodule.mkQ_surjective M
  exact lTensor_exact S foo foo'

lemma projlem {R M N : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Projective R M] (f : M ≃ₗ[R] N) : Module.Projective R N := by
  exact Module.Projective.of_equiv f

omit [Module.Projective (↑R₀) V₀] [Module.Finite (↑R₀) V₀] in
lemma mymodeq (M : Submodule R (R ⊗[R₀] V₀)) : Submodule.map (AlgebraTensorModule.cancelBaseChange (↑R₀) (↑R.right) (↑S.right) (↑S.right) V₀)
    (LinearMap.range (LinearMap.baseChange (↑S.right) M.subtype)) =
  myModMap' V₀ R₀ S M := by
  rw [myModMap', myModMap, LinearMap.range_comp]
  rfl

omit [Module.Projective (↑R₀) V₀] [Module.Finite (↑R₀) V₀] in
/--`S ⊗[R] ((R ⊗[R₀] V₀) ⧸ M) ≃[S] (S ⊗[R] (R ⊗[R₀] V₀)) ⧸ Im (S ⊗[R] M)` where
where `Im (S ⊗[R] M)` is the image of `S ⊗[R] M` under the map
`S ⊗[R] M →ₗ[S] S ⊗[R] R ⊗[↑R₀] V₀`-/
def mymodMapequiv (M : Submodule R (R ⊗[R₀] V₀)) :=
  Submodule.Quotient.equiv
    (LinearMap.range (LinearMap.baseChange (↑S.right) M.subtype))
    (myModMap' V₀ R₀ S M)
    (AlgebraTensorModule.cancelBaseChange R₀ R S S V₀)
    (mymodeq V₀ R₀ M)
/-
lemma map_comm {T : Under R₀} [Algebra S T] [IsScalarTower R₀ S T] [Algebra R T] (M : Submodule R (R ⊗[R₀] V₀))
    [IsScalarTower R₀ R T] : (myModMap V₀ R₀ T M) = myModMap V₀ R₀ T (LinearMap.range (myModMap V₀ R₀ S M)) := by sorry
-/
lemma map'_comm {T : Under R₀} [Algebra S T] [IsScalarTower R₀ S T] [Algebra R T] (M : Submodule R (R ⊗[R₀] V₀))
    [IsScalarTower R₀ R T] [IsScalarTower R S T] : myModMap' V₀ R₀ T M = myModMap' V₀ R₀ T (myModMap' V₀ R₀ S M) := by
  rw [← mymodeq, ← mymodeq, ← mymodeq]
  ext tv
  constructor
  · intro ⟨trv, ⟨⟨tm, h12⟩, h2⟩⟩
    refine ⟨?_, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · use ((AlgebraTensorModule.cancelBaseChange (↑R₀) (↑S.right) (↑T.right) (↑T.right) V₀).symm tv)
    · let tim := (LinearMap.baseChange T (myModMap V₀ R₀ S M)) (((AlgebraTensorModule.cancelBaseChange R S T T M).symm) tm)
      rw [mymodeq, myModMap']
      sorry
    · rw [← h2]
      sorry
    · simp only [LinearEquiv.apply_symm_apply]
  · intro ⟨x, y⟩
    --simp only [Submodule.mem_map, LinearMap.mem_range, exists_exists_eq_and]
    refine ⟨?_, ?_ ⟩
    cases' y with y1 y2
    have hx : x ∈
      (LinearMap.range
        (LinearMap.baseChange (↑T.right)
          (Submodule.map (AlgebraTensorModule.cancelBaseChange (↑R₀) (↑R.right) (↑S.right) (↑S.right) V₀)
              (LinearMap.range (LinearMap.baseChange (↑S.right) M.subtype))).subtype)) := y1
    rw [LinearMap.mem_range] at hx
    · rw [mymodeq] at hx
      use (AlgebraTensorModule.cancelBaseChange R₀ R T T V₀).symm tv
    · simp only [SetLike.mem_coe, LinearMap.mem_range]
      constructor
      · 
        sorry
      · sorry

omit [Module.Projective (↑R₀) V₀] [Module.Finite (↑R₀) V₀] in
lemma myModProj1 (M : Submodule R (R ⊗[R₀] V₀)) [Module.Projective R ((R ⊗[R₀] V₀)⧸M)] :
    Module.Projective S ((S ⊗[R₀] V₀) ⧸ (myModMap' V₀ R₀ S M)) := by
  refine Module.Projective.of_equiv  (?_ : S ⊗[R] ((R ⊗[R₀] V₀) ⧸ M) ≃ₗ[S] (S ⊗[R₀] V₀) ⧸ (myModMap' V₀ R₀ S M))
  have h1 := (mapexact V₀ R₀ S M)
  let foo := (Function.Exact.linearEquivOfSurjective (M := S ⊗[R] ↥M) (mapexact V₀ R₀ S M) (mapsurj V₀ R₀ S M)).symm
  refine foo ≪≫ₗ ?_
  exact mymodMapequiv V₀ R₀ M

instance freelem (M : Submodule R (R ⊗[R₀] V₀)) (P : PrimeSpectrum R) (h : Module.Projective R ((R ⊗[R₀] V₀) ⧸ M)) :
    Module.Free (Localization.AtPrime P.asIdeal) (Localization.AtPrime P.asIdeal ⊗[R] (R ⊗[R₀] V₀ ⧸ M)) := by
  have h' : Module.Projective (Localization.AtPrime P.asIdeal)
    (Localization.AtPrime P.asIdeal ⊗[↑R.right] (↑R.right ⊗[↑R₀] V₀ ⧸ M)) := Module.Projective.tensorProduct
  exact free_of_finite_IsLocalRing (Localization.AtPrime P.asIdeal) (Localization.AtPrime P.asIdeal ⊗[R] (R ⊗[R₀] V₀ ⧸ M)) h'

def quotequal (M : Submodule R (R ⊗[R₀] V₀)) : Submodule.map (↑(AlgebraTensorModule.cancelBaseChange (↑R₀) (↑R.right) (↑S.right) (↑S.right) V₀))
    (LinearMap.range (LinearMap.baseChange (↑S.right) M.subtype)) =
  Submodule.map (AlgebraTensorModule.cancelBaseChange (↑R₀) (↑R.right) (↑S.right) (↑S.right) V₀)
    (LinearMap.range (LinearMap.baseChange (↑S.right) M.subtype)) := rfl

def modlineq (M : Submodule R (R ⊗[R₀] V₀)) :
    ((S ⊗[R₀] V₀) ⧸ (myModMap' V₀ R₀ S M)) ≃ₗ[S] S ⊗[R] ((R ⊗[R₀] V₀) ⧸ M) := by
  rw [← mymodeq]
  let g := TensorProduct.tensorQuotientEquiv S M
  --let g' := AlgebraTensorModule.cancelBaseChange R₀ R S S V₀
  let f := (Function.Exact.linearEquivOfSurjective (M := S ⊗[R] ↥M) (mapexact V₀ R₀ S M) (mapsurj V₀ R₀ S M))
  refine ?_ ≪≫ₗ f
  let h :=
        ((AlgebraTensorModule.cancelBaseChange (↑R₀) (↑R.right) (↑S.right) (↑S.right)
                V₀).ofSubmodules
            (LinearMap.range (LinearMap.baseChange (↑S.right) M.subtype))
            (Submodule.map
              (AlgebraTensorModule.cancelBaseChange (↑R₀) (↑R.right) (↑S.right) (↑S.right) V₀)
              (LinearMap.range (LinearMap.baseChange (↑S.right) M.subtype)))
          (quotequal _ _ M)).symm
  have h1 : Submodule.map (AlgebraTensorModule.cancelBaseChange (↑R₀) (↑R.right) (↑S.right) (↑S.right) V₀)
    (LinearMap.range (LinearMap.baseChange (↑S.right) M.subtype)) =
  Submodule.map (AlgebraTensorModule.cancelBaseChange (↑R₀) (↑R.right) (↑S.right) (↑S.right) V₀)
    (LinearMap.range (LinearMap.baseChange (↑S.right) M.subtype)) := by exact rfl
  exact
    (Submodule.Quotient.equiv (LinearMap.range (LinearMap.baseChange (↑S.right) M.subtype))
        (Submodule.map
          (AlgebraTensorModule.cancelBaseChange (↑R₀) (↑R.right) (↑S.right) (↑S.right) V₀)
          (LinearMap.range (LinearMap.baseChange (↑S.right) M.subtype)))
        (AlgebraTensorModule.cancelBaseChange (↑R₀) (↑R.right) (↑S.right) (↑S.right) V₀) h1).symm

--an S_Q equiv used in proof of myModConstRank for functorality
def myModLinEq (M : Submodule R (R ⊗[R₀] V₀)) (Q : PrimeSpectrum S) :
    (Localization.AtPrime Q.asIdeal ⊗[↑R.right] (↑R.right ⊗[↑R₀] V₀ ⧸ M)) ≃ₗ[Localization.AtPrime Q.asIdeal] ((Localization.AtPrime Q.asIdeal ⊗[↑S.right] (↑S.right ⊗[↑R₀] V₀ ⧸ myModMap' V₀ R₀ S M))) := by
  let f := LinearEquiv.baseChange (↑S.right) (Localization.AtPrime Q.asIdeal)
      (↑S.right ⊗[↑R₀] V₀ ⧸ myModMap' V₀ R₀ S M) (↑S.right ⊗[↑R.right] (↑R.right ⊗[↑R₀] V₀ ⧸ M))
      (@modlineq V₀ R₀ _ _ R S _ _ M)
  --let g := AlgebraTensorModule.cancelBaseChange (Localization.AtPrime Q.asIdeal)
  let g := AlgebraTensorModule.cancelBaseChange (↑R.right) (↑S.right) (Localization.AtPrime Q.asIdeal)
      (Localization.AtPrime Q.asIdeal) (↑R.right ⊗[↑R₀] V₀ ⧸ M)
  refine g.symm ≪≫ₗ ?_
  exact id f.symm

omit [Module.Projective R₀ V₀] in
lemma myModConstRank (M : Submodule R (R ⊗[R₀] V₀)) [Module.Projective R ((R ⊗[R₀] V₀)⧸M)]
    (h : ∀ P : PrimeSpectrum R, Module.rankAtStalk ((R ⊗[R₀] V₀)⧸M) P = d) :
    ∀ Q : PrimeSpectrum S, Module.rankAtStalk ((S ⊗[R₀] V₀) ⧸ (myModMap' V₀ R₀ S M)) Q = d := by
  intro Q
  let P := RingHom.specComap (algebraMap R S) Q
  have hP : P.asIdeal = Ideal.comap (algebraMap R S) Q.asIdeal := rfl
  let _ : Fact (P.asIdeal = Ideal.comap (algebraMap R S) Q.asIdeal) := { out := hP }
  have h1 : Module.Free (Localization.AtPrime P.asIdeal) (Localization.AtPrime P.asIdeal ⊗[↑R.right] (↑R.right ⊗[↑R₀] V₀ ⧸ M)) := by exact freelem _ _ M P inferInstance
  let h2 := rankalgebraMaprankAtStalkup R S ((R ⊗[R₀] V₀) ⧸ M) Q P d
  specialize h P
  apply h2 at h
  let h3 := rankalgebraMaprankAtStalk _ _ _ _ h
  let g := AlgebraTensorModule.cancelBaseChange R S (Localization.AtPrime Q.asIdeal) (Localization.AtPrime Q.asIdeal) ((R ⊗[R₀] V₀) ⧸ M)
  let h4 := @LinearEquiv.finrank_eq (Localization.AtPrime Q.asIdeal) (Localization.AtPrime Q.asIdeal ⊗[↑S.right]
    ↑S.right ⊗[↑R.right] (↑R.right ⊗[↑R₀] V₀ ⧸ M)) _ _ _ _ _ _ g
  rw [h3] at h4
  apply rankalgebraMaprankAtStalksymm'
  let g' := myModLinEq V₀ R₀ M Q
  let h5 := LinearEquiv.finrank_eq g'
  rw [← h5]
  exact id (Eq.symm h4)

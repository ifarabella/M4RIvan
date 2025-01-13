import Mathlib

open TensorProduct

variable {R : Type} [CommSemiring R] {R'' : Type} [Semiring R'']
  {M : Type } {N : Type} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Module R'' M]
  [SMulCommClass R R'' M]

noncomputable instance leftModule' : Module R'' (M ⊗[R] N) := TensorProduct.leftModule

noncomputable instance rightModule' : Module R'' (N ⊗[R] M) :=
  { add_smul := TensorProduct.add_smul
    zero_smul := TensorProduct.zero_smul }

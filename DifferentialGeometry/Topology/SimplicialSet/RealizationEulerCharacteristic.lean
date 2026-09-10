import DifferentialGeometry.Topology.SimplicialSet.FiniteRealizationHomology
import DifferentialGeometry.Topology.SimplicialSet.EulerCharacteristic
import DifferentialGeometry.Topology.Homology.EulerCharacteristic

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u

namespace Poincare.SSet

variable (k : Type u) [Field k] (X : _root_.SSet.{u}) [X.Finite]

theorem finiteHomologyType_realization :
    Poincare.Homology.finiteHomologyType k (_root_.SSet.toTop.obj X) := by
  constructor
  · intro n
    have := finiteDimensional_homology X (ModuleCat.of k k) n
    exact (realizationHomologyIso (ModuleCat.of k k) X n).toLinearEquiv.finiteDimensional
  · obtain ⟨d, hd⟩ := X.hasDimensionLT_of_finite
    exact ⟨d, fun n hn ↦
      (X.isZero_homology_of_hasDimensionLT (ModuleCat.of k k) n d hn.le).of_iso
        (realizationHomologyIso (ModuleCat.of k k) X n).symm⟩

theorem eulerChar_realization_eq_homologyEulerChar :
    Poincare.Homology.eulerChar k (_root_.SSet.toTop.obj X) =
      (X.chainComplex (ModuleCat.of k k)).homologyEulerChar := by
  apply finsum_congr
  intro n
  rw [(realizationHomologyIso (ModuleCat.of k k) X n).toLinearEquiv.finrank_eq]

theorem eulerChar_realization_eq_sum_card_nonDegenerate (d : ℕ) [X.HasDimensionLT d] :
    Poincare.Homology.eulerChar k (_root_.SSet.toTop.obj X) =
      ∑ n ∈ Finset.range d, (-1 : ℤ) ^ n * Nat.card (X.nonDegenerate n) := by
  rw [eulerChar_realization_eq_homologyEulerChar,
    homologyEulerChar_eq_sum_card_nonDegenerate (X := X) (k := k) d]

theorem eulerChar_realization_eq_finsum_card_nonDegenerate :
    Poincare.Homology.eulerChar k (_root_.SSet.toTop.obj X) =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Nat.card (X.nonDegenerate n) := by
  rw [eulerChar_realization_eq_homologyEulerChar,
    homologyEulerChar_eq_finsum_card_nonDegenerate]

theorem eulerChar_realization_eq_of_coefficients (K : Type u) [Field K] :
    Poincare.Homology.eulerChar k (_root_.SSet.toTop.obj X) =
      Poincare.Homology.eulerChar K (_root_.SSet.toTop.obj X) := by
  rw [eulerChar_realization_eq_finsum_card_nonDegenerate,
    eulerChar_realization_eq_finsum_card_nonDegenerate]

end Poincare.SSet

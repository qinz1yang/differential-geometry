import DifferentialGeometry.Topology.Double.EmptyBoundary
import DifferentialGeometry.Topology.Homology.EulerCharacteristic
import DifferentialGeometry.Topology.Manifold.ZeroDimensional

set_option autoImplicit false
noncomputable section
open Set Function Topology
open scoped Manifold
namespace Poincare.Homology
open Poincare.Topology

theorem finiteHomologyType_and_eulerChar_intrinsicDouble_of_subsingleton_model
    {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
    (I : ModelWithCorners ℝ E H) (K : Type) [Field K] :
    finiteHomologyType K (TopCat.of (Double (I.boundary M))) ∧
      eulerChar K (TopCat.of (Double (I.boundary M))) =
        2 * eulerChar K (TopCat.of M) - eulerChar K (TopCat.of (I.boundary M)) := by
  have hb := DifferentialGeometry.boundary_eq_empty_of_subsingleton_model (N := M) I
  rw [hb]
  let _ : DiscreteTopology M := DifferentialGeometry.discrete_topology_of_subsingleton_model I
  let _ : Finite M := DifferentialGeometry.finite_of_compact_subsingleton_model I
  let e : Double (∅ : Set M) ≃ₜ M ⊕ M := doubleEmptyHomeomorph
  have hf := finiteHomologyType_of_finite_totallyDisconnected K (X := TopCat.of (M ⊕ M))
  refine ⟨(finiteHomologyType_iff_of_homeomorph K (X := TopCat.of (Double (∅ : Set M))) (Y := TopCat.of (M ⊕ M)) e).mpr hf, ?_⟩
  rw [eulerChar_eq_of_homeomorph K (X := TopCat.of (Double (∅ : Set M))) (Y := TopCat.of (M ⊕ M)) e, eulerChar_of_finite_totallyDisconnected,
    eulerChar_of_finite_totallyDisconnected]
  simp [Nat.card_sum, two_mul]

end Poincare.Homology

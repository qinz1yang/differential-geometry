import DifferentialGeometry.Topology.StandardModel

noncomputable section
open scoped Manifold ContDiff

open private standardCharts standard_diffeo standard_mfld from DifferentialGeometry.Topology.StandardModel

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [I.Boundaryless]

theorem exists_standard_chartedSpace :
    ∃ c : ChartedSpace E Q,
      letI : ChartedSpace E Q := c
      IsManifold 𝓘(ℝ, E) ∞ Q ∧ Nonempty (Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ Q) := by
  refine ⟨standardCharts (I := I) (M := Q) (ContinuousLinearEquiv.refl ℝ E), ?_, ?_⟩
  · exact standard_mfld (I := I) (M := Q) (ContinuousLinearEquiv.refl ℝ E)
  · exact ⟨standard_diffeo (I := I) (M := Q) (ContinuousLinearEquiv.refl ℝ E)⟩

end DifferentialGeometry.Geometry.Topology

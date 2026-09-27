import Mathlib.Geometry.Manifold.Instances.Real

noncomputable section

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem extChartAt_opens_target (U : TopologicalSpace.Opens F) (α : U) :
    (extChartAt 𝓘(ℝ, F) α).target = (U : Set F) := by
  change Set.univ ∩ ((OpenPartialHomeomorph.refl F).subtypeRestr (s := U) ⟨α⟩).target = U
  rw [Set.univ_inter]
  rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_refl,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]

theorem interior_extChartAt_opens_target (U : TopologicalSpace.Opens F) (α : U) :
    interior (extChartAt 𝓘(ℝ, F) α).target = (U : Set F) := by
  rw [extChartAt_opens_target, U.isOpen.interior_eq]

end DifferentialGeometry

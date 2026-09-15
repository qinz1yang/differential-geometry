import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsPLHomeomorphOn.image_closure [FiniteDimensional ℝ E] {f : E → F} {P A : Set E} {Q : Set F}
    (hf : IsPLHomeomorphOn f P Q) (hP : IsCompact P) (hAP : A ⊆ P) :
    f '' closure A = closure (f '' A) := by
  have hcl : closure A ⊆ P := closure_minimal hAP hP.isClosed
  exact image_closure_of_isCompact (hP.of_isClosed_subset isClosed_closure hcl)
    (hf.isPiecewiseAffineOn.continuousOn.mono hcl)

end DifferentialGeometry.Topology.PiecewiseLinear

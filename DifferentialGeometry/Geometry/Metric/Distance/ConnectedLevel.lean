import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_riemannianEDistOf_eq_of_isPreconnected_of_closure
    (g : SmoothRiemannianMetric I M) (p : M) {U : Set M} (hU : IsPreconnected U)
    {a b : M} (ha : a ∈ closure U) (hb : b ∈ U) {R : ℝ}
    (hnear : riemannianEDistOf g p a < ENNReal.ofReal R)
    (hfar : ENNReal.ofReal R ≤ riemannianEDistOf g p b) :
    ∃ z ∈ U, riemannianEDistOf g p z = ENNReal.ofReal R := by
  have hcont : Continuous (fun z => riemannianEDistOf g p z) := continuous_riemannianEDist g p
  have hnhds : {z | riemannianEDistOf g p z < ENNReal.ofReal R} ∈ 𝓝 a :=
    (isOpen_lt hcont continuous_const).mem_nhds hnear
  obtain ⟨a', ha'near, ha'U⟩ := mem_closure_iff_nhds.mp ha _ hnhds
  exact hU.intermediate_value ha'U hb hcont.continuousOn ⟨ha'near.le, hfar⟩

end DifferentialGeometry.Geometry.Riemannian

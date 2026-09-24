import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Metric.Distance.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz


noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian

open Bundle Manifold
open scoped ContDiff ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [PseudoEMetricSpace N]

theorem locallyLipschitzOn_comp_extChartAt_symm_of_edist_le
    (g : SmoothRiemannianMetric I M) (α : M) {f : M → N} {L : ℝ≥0}
    (hf : ∀ x y, edist (f x) (f y) ≤ L * riemannianEDistOf g x y) :
    LocallyLipschitzOn (extChartAt I α).target (f ∘ (extChartAt I α).symm) := by
  let _ : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  intro y hy
  obtain ⟨C, s, hs, hC⟩ := chart_inv_edist_le (I := I) α hy
  refine ⟨L * C, s, hs, ?_⟩
  intro z hz w hw
  have hCzw : riemannianEDistOf g ((extChartAt I α).symm z)
      ((extChartAt I α).symm w) ≤ C * edist z w := by
    simpa only [riemannianEDistOf] using hC z hz w hw
  calc
    edist ((f ∘ (extChartAt I α).symm) z) ((f ∘ (extChartAt I α).symm) w) ≤
        L * riemannianEDistOf g ((extChartAt I α).symm z)
          ((extChartAt I α).symm w) := hf _ _
    _ ≤ L * (C * edist z w) := mul_right_mono hCzw
    _ = ((L * C : ℝ≥0) : ℝ≥0∞) * edist z w := by
      rw [ENNReal.coe_mul, mul_assoc]

end DifferentialGeometry.Geometry.Riemannian

end

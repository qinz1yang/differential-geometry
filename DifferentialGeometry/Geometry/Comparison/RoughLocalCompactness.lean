import DifferentialGeometry.Topology.MetricSpace.RoughDimensionCompactness
import DifferentialGeometry.Geometry.Comparison.LocalRoughDimension

set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem exists_compact_closedBall_of_local_rough_dimension
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    {Ω : Set X} (hΩ : IsOpen Ω) (hcomp : fourPointComparison 1 Ω)
    (hcomplete : ∀ z ∈ Ω, ∃ R : ℝ, 0 < R ∧ IsComplete (Metric.closedBall z R))
    {n : ℕ} (hdim : dimH Ω ≤ n) {p : X} (hp : p ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall p r ⊆ Ω ∧ IsCompact (Metric.closedBall p r) := by
  obtain ⟨h, hh, hB, m, _, hd, _⟩ :=
    exists_local_roughDim_le_of_fourPointComparison hcurves hΩ hcomp hcomplete hdim hp
  have hfinite : Metric.roughDim (Metric.ball p h) < ⊤ := hd.trans_lt (by simp)
  obtain ⟨r, hr, hsub, hcompact⟩ := Metric.exists_compact_closedBall_of_roughDim_lt_top
    (Metric.ball_mem_nhds p hh) hfinite (hcomplete p hp)
  exact ⟨r, hr, hsub.trans hB, hcompact⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov

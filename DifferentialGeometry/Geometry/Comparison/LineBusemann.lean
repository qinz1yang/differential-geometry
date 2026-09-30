import DifferentialGeometry.Geometry.Metric.ProductBusemann
import DifferentialGeometry.Geometry.Comparison.LineSplitting

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [ProperSpace X]
variable (hs : fourPointComparison 0 (univ : Set X)) {γ : ℝ → X} (hγ : Isometry γ)
variable (hsegments : ∀ a b : X, ∃ f : Icc (0 : ℝ) 1 → X,
  Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
  ∀ s t, dist (f s) (f t) = dist a b * dist s t)

include hs hγ hsegments

theorem tendsto_dist_line_sub_lineCoordinate (x : X) :
    Tendsto (fun T : ℝ => dist x (γ T) - T) atTop (𝓝 (-lineCoordinate γ x)) :=
  (lineSplitting hs hγ hsegments).tendsto_dist_aligned_line_sub
    (lineSplitting_apply_line hs hγ hsegments) x

theorem eventually_abs_dist_line_sub_lineCoordinate_lt (B : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ x : X, dist x (γ 0) ≤ B →
      |dist x (γ T) - T + lineCoordinate γ x| < η ∧
      |dist x (γ (-T)) - T - lineCoordinate γ x| < η :=
  (lineSplitting hs hγ hsegments).eventually_abs_dist_aligned_line_sub_lt
    (lineSplitting_apply_line hs hγ hsegments) B hη

end DifferentialGeometry.Geometry.Comparison.Toponogov

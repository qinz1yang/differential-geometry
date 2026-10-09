import DifferentialGeometry.Geometry.Comparison.FourPoint
import DifferentialGeometry.Geometry.Comparison.GermDistanceAsymptotic
import DifferentialGeometry.Geometry.Metric.Scaling.Rescale

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem eventually_fourPointComparison_rescale_of_local
    {X : Type*} [m : MetricSpace X] {Ω : Set X} {q : X} {κ : ℝ}
    (hκ : 0 ≤ κ) (hΩ : IsOpen Ω) (hcomp : fourPointComparison κ Ω) (hq : q ∈ Ω)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (hzero : Tendsto t atTop (𝓝 0))
    (B : ℝ) (hB : 0 < B) :
    ∀ᶠ n in atTop,
      @fourPointComparison X (m.rescale (t n)⁻¹ (inv_pos.mpr (ht n))) (κ * (t n) ^ 2)
        (@ball X (m.rescale (t n)⁻¹ (inv_pos.mpr (ht n))).toPseudoMetricSpace q B) := by
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp hΩ q hq
  filter_upwards [hzero.eventually (gt_mem_nhds (div_pos ha hB))] with n hn
  have hsmall : t n * B < a := (lt_div_iff₀ hB).mp hn
  have hmem (z : X)
      (hz : z ∈ @ball X (m.rescale (t n)⁻¹ (inv_pos.mpr (ht n))).toPseudoMetricSpace q B) :
      z ∈ Ω := by
    apply hball
    change dist z q < a
    change (t n)⁻¹ * dist z q < B at hz
    have hz' : dist z q / t n < B := by simpa only [div_eq_mul_inv, mul_comm] using hz
    have hd := (div_lt_iff₀ (ht n)).mp hz'
    exact hd.trans (by simpa only [mul_comm] using hsmall)
  have hangle (u v w : ℝ) :
      comparisonAngleNegCurvature (κ * (t n) ^ 2)
        ((t n)⁻¹ * u) ((t n)⁻¹ * v) ((t n)⁻¹ * w) =
      comparisonAngleNegCurvature κ u v w := by
    have h := comparisonAngleNegCurvature_mul_scale hκ (ht n) (u / t n) (v / t n) w
    rw [div_mul_cancel₀ _ (ht n).ne', div_mul_cancel₀ _ (ht n).ne'] at h
    simpa only [div_eq_mul_inv, mul_comm] using h.symm
  intro x hx u hu v hv w hw hux hvx hwx
  have h := hcomp x (hmem x hx) u (hmem u hu) v (hmem v hv) w (hmem w hw) hux hvx hwx
  simpa only [MetricSpace.rescale_dist, hangle] using h

end DifferentialGeometry.Geometry.Comparison.Toponogov

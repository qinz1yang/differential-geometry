import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MetricCompare_S107
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RicciNormDefect_S70
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterface
import DifferentialGeometry.Geometry.Curvature.Bounds.SectionalNorm
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls

set_option autoImplicit false

/-!
# CH12-S107 / G2b: pieces of the seed at the centre of the tracked ball

* `sectional_seed_S107` : the vector defect `≤ η ≤ 1` at `q` (time `s`, stage `j`) gives
  `SectionalBoundedBelowAt (s⁻¹ g) q (-(a²)⁻¹)` as soon as `189 a² ≤ 1`.
-/

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Collapse GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

theorem sectional_seed_S107 (K : ObservedHistory.{u}) (j : Fin (K.eventCount + 1)) {s η a : ℝ}
    (hs : 0 < s) (hη : η ≤ 1) (q : (K.stage j).Carrier)
    (hdef : ∀ V : TangentSpace ThreeModel q, DefectAt_S85 K j q V η s) (ha : 0 < a)
    (ha2 : 189 * a ^ 2 ≤ 1) :
    SectionalBoundedBelowAt (scaleMetric s⁻¹ (inv_pos.mpr hs) (K.stageMetric j s)) q
      (-(a ^ 2)⁻¹) := by
  rw [sectionalBoundedBelowAt_scaleMetric_iff (inv_pos.mpr hs)]
  have hrm := sqrt_normSq0S_rm_le_of_defect_S70 (K.stageMetric j s) q hs hη hdef
  have hC : 189 / s ≤ (a ^ 2)⁻¹ * s⁻¹ := by
    have ha2' : 189 ≤ (a ^ 2)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) (by positivity), ← one_div, le_div_iff₀ (by norm_num)]
      linarith
    calc 189 / s = 189 * s⁻¹ := div_eq_mul_inv _ _
      _ ≤ (a ^ 2)⁻¹ * s⁻¹ := mul_le_mul_of_nonneg_right ha2' (inv_nonneg.mpr hs.le)
  have := sectionalBoundedBelowAt_neg_of_sqrt_normSq0S_le (K.stageMetric j s) q (C := (a ^ 2)⁻¹ * s⁻¹)
    (hrm.trans hC)
  convert this using 1
  ring

end GC.LongTime.Ch12

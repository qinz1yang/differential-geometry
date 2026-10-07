import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitVolumeLimit_O5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.GronwallLog_S45

set_option autoImplicit false

/-!
# CH12-S45 / G1: from the LTF03 Ricci defect of a slice to the vector form used by the window

`slice_defect_quad_S45`: on a regular slice at time `s`, `|2 s Ric(V,V) + g(V,V)| ≤ D g(V,V)` for
every tangent vector `V`, where `D = NormalizedRicciDefect_S13 s q` (physical metric, no
normalization left).  Together with `metric_variation_S45` this is the hypothesis `hdef` of the
order-zero Grönwall step.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime Set
open scoped Manifold ContDiff
namespace GC.LongTime.Ch12
universe u

theorem slice_defect_quad_S45 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {T : ObservationTower P g} (s : RegularSlice T) (q : s.stage.Carrier)
    (V : TangentSpace ThreeModel q) :
    |2 * s.time * ricciTensor s.metric q V V + s.metric.inner q V V| ≤
      NormalizedRicciDefect_S13 s q * s.metric.inner q V V := by
  have hq := defect_quad_le_O5 s.normalizedMetric q V
  have hs : 0 < s.time := s.positive
  have hnorm : s.normalizedMetric.inner q V V = s.time⁻¹ * s.metric.inner q V V := by
    change (scaleMetric s.time⁻¹ (inv_pos.mpr s.positive) s.metric).inner q V V = _
    rw [scaleMetric_inner]
  have hric : ricciTensor s.normalizedMetric q V V = ricciTensor s.metric q V V := by
    change ricciTensor (scaleMetric s.time⁻¹ (inv_pos.mpr s.positive) s.metric) q V V = _
    rw [ricciTensor_scaleMetric]
  rw [hnorm, hric] at hq
  have hD : sSup (defectSet_O5 s.normalizedMetric q) = NormalizedRicciDefect_S13 s q := rfl
  rw [hD] at hq
  have h2 : 2 * s.time * ricciTensor s.metric q V V + s.metric.inner q V V =
      s.time * (2 * ricciTensor s.metric q V V + s.time⁻¹ * s.metric.inner q V V) := by
    field_simp
  rw [h2, abs_mul, abs_of_pos hs]
  calc s.time * |2 * ricciTensor s.metric q V V + s.time⁻¹ * s.metric.inner q V V|
      ≤ s.time * (NormalizedRicciDefect_S13 s q * (s.time⁻¹ * s.metric.inner q V V)) :=
        mul_le_mul_of_nonneg_left hq hs.le
    _ = NormalizedRicciDefect_S13 s q * s.metric.inner q V V := by field_simp

end GC.LongTime.Ch12

import DifferentialGeometry.Geometry.Metric.Scaling.Rescale
import Mathlib.Topology.UniformSpace.Equiv
import Mathlib.Topology.MetricSpace.HausdorffDimension

set_option autoImplicit false

open Set Metric

namespace MetricSpace

def rescaleUniformEquiv {X : Type*} (m : MetricSpace X) (c : ℝ) (hc : 0 < c) :
    @UniformEquiv X X m.toUniformSpace (m.rescale c hc).toUniformSpace :=
  @UniformEquiv.mk X X m.toUniformSpace (m.rescale c hc).toUniformSpace (Equiv.refl X)
  (@LipschitzWith.uniformContinuous X X
    m.toPseudoEMetricSpace (m.rescale c hc).toPseudoEMetricSpace ⟨c, hc.le⟩ id
    (m.lipschitzWith_rescale_id c hc))
  (@LipschitzWith.uniformContinuous X X
    (m.rescale c hc).toPseudoEMetricSpace m.toPseudoEMetricSpace
    ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ id (m.lipschitzWith_id_rescale c hc))

theorem rescale_completeSpace_iff {X : Type*} (m : MetricSpace X) (c : ℝ) (hc : 0 < c) :
    @CompleteSpace X (m.rescale c hc).toUniformSpace ↔ @CompleteSpace X m.toUniformSpace :=
  (@UniformEquiv.completeSpace_iff X X m.toUniformSpace (m.rescale c hc).toUniformSpace
    (m.rescaleUniformEquiv c hc)).symm

theorem rescale_dimH {X : Type*} (m : MetricSpace X) (c : ℝ) (hc : 0 < c) (s : Set X) :
    @dimH X (m.rescale c hc).toEMetricSpace s = @dimH X m.toEMetricSpace s := by
  apply le_antisymm
  · simpa only [image_id] using
      (@LipschitzWith.dimH_image_le X X m.toEMetricSpace (m.rescale c hc).toEMetricSpace
        ⟨c, hc.le⟩ id (m.lipschitzWith_rescale_id c hc) s)
  · simpa only [image_id] using
      (@LipschitzWith.dimH_image_le X X (m.rescale c hc).toEMetricSpace m.toEMetricSpace
        ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ id (m.lipschitzWith_id_rescale c hc) s)

theorem rescale_ball {X : Type*} (m : MetricSpace X) (c : ℝ) (hc : 0 < c) (o : X) (r : ℝ) :
    @ball X (m.rescale c hc).toPseudoMetricSpace o (c * r) =
      @ball X m.toPseudoMetricSpace o r := by
  ext x
  change c * @dist X m.toDist x o < c * r ↔ @dist X m.toDist x o < r
  exact mul_lt_mul_iff_right₀ hc

theorem rescale_closedBall {X : Type*} (m : MetricSpace X) (c : ℝ) (hc : 0 < c) (o : X) (r : ℝ) :
    @closedBall X (m.rescale c hc).toPseudoMetricSpace o (c * r) =
      @closedBall X m.toPseudoMetricSpace o r := by
  ext x
  change c * @dist X m.toDist x o ≤ c * r ↔ @dist X m.toDist x o ≤ r
  exact mul_le_mul_iff_right₀ hc

end MetricSpace

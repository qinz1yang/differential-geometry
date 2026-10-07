import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAgeObject_P6N
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

/-!
# CX-SPINE G5: weighted curvature control under history rescaling

For `c > 0`, replacing `g` by `c⁻¹ g` and `r` by `r / sqrt c` leaves
`r⁴ |Rm|²` unchanged. The first theorem derives this from the actual curvature
tensor and tensor-norm scaling identities. The terminal theorem transports the
same identity through `IncomingSlab.rescale_terminalRegularOpen` and
`TerminalLimitMetric.rescale_metric_heq_P6N`, with an explicit `HEq` of the points.
Thus it applies to the crossed-terminal clause of `BackwardPointTrace.isRmControlled`.
It does not assume any curvature identity or controlled-ball transport as an input.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

universe u

/-- The weighted `Rm` control is invariant under inverse metric scaling and
the corresponding radius scaling. The radius may be any real number. -/
theorem weighted_rm_sq_scale_inv_CXSP
    {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (g : SmoothRiemannianMetric ThreeModel X) (c : ℝ) (hc : 0 < c) (r : ℝ) (x : X) :
    (r / Real.sqrt c) ^ 4 * normSq0S (scaleMetric c⁻¹ (inv_pos.mpr hc) g) x 4
        (metricRm04At (scaleMetric c⁻¹ (inv_pos.mpr hc) g) x) =
      r ^ 4 * normSq0S g x 4 (metricRm04At g x) := by
  let : IsManifold ThreeModel 1 X := IsManifold.of_le (n := ∞) (by decide)
  have hnorm : normSq0S (scaleMetric c⁻¹ (inv_pos.mpr hc) g) x 4
      (metricRm04At (scaleMetric c⁻¹ (inv_pos.mpr hc) g) x) =
      c ^ 2 * normSq0S g x 4 (metricRm04At g x) := by
    simp only [← metricRm04_apply]
    rw [metricRm_scale, normSq0S_smul, normSq0S_scale, inv_inv]
    have hcancel : (c⁻¹) ^ 2 * c ^ 4 = c ^ 2 := by
      calc
        _ = (c⁻¹ * c) ^ 2 * c ^ 2 := by ring
        _ = _ := by rw [inv_mul_cancel₀ hc.ne', one_pow, one_mul]
    rw [← mul_assoc, hcancel]
  have hsqrt : (Real.sqrt c) ^ 4 = c ^ 2 := by
    calc
      _ = ((Real.sqrt c) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hc.le]
  rw [hnorm, div_pow, hsqrt, ← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 hc.ne')]

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.Geometry.Curvature

universe u

private theorem rm_sq_eq_of_open_heq_CXSP {P : OrientedThreeStage.{u}}
    {U V : TopologicalSpace.Opens P.Carrier} (hUV : U = V)
    (gU : SmoothRiemannianMetric ThreeModel U) (gV : SmoothRiemannianMetric ThreeModel V)
    (hg : HEq gU gV) (xU : U) (xV : V) (hx : HEq xU xV) :
    normSq0S gU xU 4 (metricRm04At gU xU) =
      normSq0S gV xV 4 (metricRm04At gV xV) := by
  subst hUV
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hx
  rfl

/-- The same weighted identity for the actual rescaled terminal limit metric.
The explicit point `HEq` identifies the two copies of the terminal regular open. -/
theorem TerminalLimitMetric.weighted_rm_sq_rescale_CXSP
    {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}
    (L : G.TerminalLimitMetric) (c : ℝ) (hc : 0 < c) (r : ℝ)
    (xScaled : (G.rescale c hc).terminalRegularOpen) (x : G.terminalRegularOpen)
    (hx : HEq xScaled x) :
    (r / Real.sqrt c) ^ 4 * normSq0S (L.rescale c hc).metric xScaled 4
        (metricRm04At (L.rescale c hc).metric xScaled) =
      r ^ 4 * normSq0S L.metric x 4 (metricRm04At L.metric x) := by
  have hnorm := rm_sq_eq_of_open_heq_CXSP (G.rescale_terminalRegularOpen c hc)
    (L.rescale c hc).metric (scaleMetric c⁻¹ (inv_pos.mpr hc) L.metric)
    (L.rescale_metric_heq_P6N c hc) xScaled x hx
  rw [hnorm]
  exact weighted_rm_sq_scale_inv_CXSP L.metric c hc r x

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

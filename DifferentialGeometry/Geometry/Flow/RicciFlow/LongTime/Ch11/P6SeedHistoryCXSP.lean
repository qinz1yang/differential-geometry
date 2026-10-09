import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedGeodesicCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedArithmeticCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedScaleP6A

set_option autoImplicit false

/-!
# CX-SPINE G1：history seed adapter

本文件单独承接 P6SeedScaleP6A 的宽 import；pure geodesic kernel 与它分离。
同一 history metric/seed/curve 的实例化，不生产 Claim 2。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 实际 seed consumer：小抛物曲率给起点界，固定 H 后同一 segment 交付 high tail。 -/
theorem exists_seed_scalar_tail_CXSP
    {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    {p : (H.stageAt t).Carrier} {r A Kb L : ℝ}
    (hsmall : hasSmallParabolicCurvature H t p r) (hA : 0 < A)
    (γ : ℝ → (H.stageAt t).Carrier) (hstart : γ 0 = p)
    (hγ : ContinuousOn γ (Icc 0 L)) (hL : 0 ≤ L) (hlen : L < A * r)
    (hdist : ∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
      riemannianEDistOf (H.stageMetric (H.activeStage t) t) (γ a) (γ b) =
        ENNReal.ofReal |a - b|)
    (hend : max 4 (2 * Kb) * (r ^ 2)⁻¹ <
      metricScalarAt (H.stageMetric (H.activeStage t) t) (γ L)) :
    ∃ s ∈ Ioo (0 : ℝ) L,
      metricScalarAt (H.stageMetric (H.activeStage t) t) (γ s) =
        max 4 (2 * Kb) * (r ^ 2)⁻¹ ∧
      (∀ v ∈ Icc (0 : ℝ) (L - s),
        γ (s + v) ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r) ∧
        (max 4 (2 * Kb) / 2) * (r ^ 2)⁻¹ <
          metricScalarAt (H.stageMetric (H.activeStage t) t) (γ (s + v))) ∧
      (∀ v ∈ Ioc (0 : ℝ) (L - s),
        max 4 (2 * Kb) * (r ^ 2)⁻¹ <
          metricScalarAt (H.stageMetric (H.activeStage t) t) (γ (s + v))) ∧
      riemannianEDistOf (H.stageMetric (H.activeStage t) t) (γ s) (γ L) =
        ENNReal.ofReal (L - s) ∧
      L - s < (2 * A * Real.sqrt (max 4 (2 * Kb))) /
        Real.sqrt (max 4 (2 * Kb) * (r ^ 2)⁻¹) ∧
      ∀ a ∈ Icc (0 : ℝ) (L - s), ∀ b ∈ Icc (0 : ℝ) (L - s),
        riemannianEDistOf (H.stageMetric (H.activeStage t) t) (γ (s + a)) (γ (s + b)) =
          ENNReal.ofReal |a - b| := by
  have hr : 0 < r := hsmall.1
  obtain ⟨_, h3, _, hhalf⟩ := seed_threshold_bounds_CXSP Kb hr
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hseed : metricScalarAt (H.stageMetric (H.activeStage t) t) (γ 0) <
      max 4 (2 * Kb) * (r ^ 2)⁻¹ := by
    rw [hstart]
    exact ((le_abs_self _).trans
      (hasSmallParabolicCurvature_scalar_abs_le_C11S hsmall hp)).trans_lt h3
  obtain ⟨s, hs, hQ, _, hclosed, hopen, hdistend, hshort, htaildist⟩ :=
    exists_scalar_high_tail_on_segment_CXSP (H.stageMetric (H.activeStage t) t)
      hγ hL hlen hdist hseed hend
  refine ⟨s, hs, hQ, ?_, hopen, hdistend, ?_, htaildist⟩
  · intro v hv
    have h := hclosed v hv
    refine ⟨?_, hhalf.trans_le h.2⟩
    simpa only [hstart] using h.1
  · exact seed_tail_length_lt_normalized_CXSP hA
      (seed_threshold_constants_CXSP Kb).1 hr hshort

end GC.LongTime.Ch11

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCurvHI_S20
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRicciShift

set_option autoImplicit false

/-!
# CH12-S37: sharp Hamilton–Ivey conversion on a regular slice

If the normalised sectional curvature fails to be `≥ -Λ` at `y` (some plane with
`sec < -Λ`, `2Λ ≥ e³`), the Hamilton–Ivey pinching forces the normalised scalar curvature to be
at least `2Λ (log (2Λ) - 3)`.  This is the logarithmic improvement of
`sec_lower_of_normScalar_le_S20`.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology
namespace GC.LongTime.Ch12
universe u

/-- **Sharp HI at a regular slice.** -/
theorem scalar_ge_of_not_sectionalBoundedBelow_S37 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (H : AnalyticSurgeryProfile F δ)
    (s : RegularSlice F.observation) (y : s.stage.Carrier) {Λ : ℝ}
    (hΛ : Real.exp 3 ≤ 2 * Λ)
    (hnot : ¬ SectionalBoundedBelowAt s.normalizedMetric y (-Λ)) :
    2 * Λ * (Real.log (2 * Λ) - 3) ≤ metricScalarAt s.normalizedMetric y := by
  have ht := s.positive
  have hdim : Module.finrank ℝ (TangentSpace ThreeModel y) = 3 := by
    change Module.finrank ℝ ThreeSpace = 3
    simp [ThreeSpace]
  obtain ⟨B, hB⟩ := exists_orthonormalBasisAt s.metric y hdim
  have hΛpos : 0 < 2 * Λ := lt_of_lt_of_le (Real.exp_pos 3) hΛ
  have hlog3 : 3 ≤ Real.log (2 * Λ) := (Real.le_log_iff_exp_le hΛpos).mpr hΛ
  -- the failure of the bound for the normalised metric, transported to `s.metric`
  have hnot' : ¬ SectionalBoundedBelowAt s.metric y (-(Λ / s.time)) := by
    intro hsec
    apply hnot
    have := hsec.scaleMetric s.time⁻¹ (inv_pos.mpr ht)
    have heq : -(Λ / s.time) / s.time⁻¹ = -Λ := by field_simp
    rw [heq] at this
    exact this
  -- least curvature operator eigenvalue
  have hlam : Λ / s.time < -leastCurvatureOperatorEigenvalueAt s.metric y
      (metricAlgebraicCurvatureTensorAt s.metric y) := by
    by_contra hle
    rw [not_lt] at hle
    apply hnot'
    rw [sectionalBoundedBelowAt_iff_curvatureOperatorLowerBoundAt hdim,
      curvatureOperatorLowerBoundAt_iff_neg_leastCurvatureOperatorEigenvalueAt_le B hB]
    exact hle
  set lam := leastCurvatureOperatorEigenvalueAt s.metric y
    (metricAlgebraicCurvatureTensorAt s.metric y) with hlamdef
  have hreg := (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion s.metric
    (H.pinchingShift + s.time) y).mp (slice_inFixedHamiltonIveyRegion_S20 H s y)
  rw [← hlamdef] at hreg
  have hXpos : 0 < -(2 * lam) := by
    have : 0 < Λ / s.time := div_pos (by linarith) ht
    linarith
  have hbar : fixedHamiltonIveyBarrier (H.pinchingShift + s.time) (-(2 * lam)) ≤
      metricScalarAt s.metric y := by
    rcases hreg with h | h
    · exact absurd h (not_le.mpr (by linarith))
    · exact h
  set X := -(2 * lam) with hX
  have hX1 : 2 * Λ / s.time < X := by
    have : 2 * (Λ / s.time) < X := by rw [hX]; linarith
    calc 2 * Λ / s.time = 2 * (Λ / s.time) := by ring
      _ < X := this
  have hX2 : 2 * Λ < s.time * X := by
    have := mul_lt_mul_of_pos_left hX1 ht
    calc 2 * Λ = s.time * (2 * Λ / s.time) := by field_simp
      _ < s.time * X := this
  have hsc : metricScalarAt s.normalizedMetric y = s.time * metricScalarAt s.metric y := by
    change metricScalarAt (scaleMetric s.time⁻¹ _ s.metric) y = _
    rw [metricScalarAt_scaleMetric, inv_inv]
  have hshift := H.pinchingShift_pos
  have haX : s.time * X ≤ (H.pinchingShift + s.time) * X := by
    nlinarith
  have hlogX : Real.log (2 * Λ) ≤ Real.log ((H.pinchingShift + s.time) * X) :=
    Real.log_le_log hΛpos (by linarith)
  have hbar' : X * (Real.log ((H.pinchingShift + s.time) * X) - 3) ≤
      metricScalarAt s.metric y := hbar
  rw [hsc]
  have hfac : 0 ≤ Real.log ((H.pinchingShift + s.time) * X) - 3 := by linarith
  calc 2 * Λ * (Real.log (2 * Λ) - 3)
      ≤ (s.time * X) * (Real.log ((H.pinchingShift + s.time) * X) - 3) := by
        apply mul_le_mul hX2.le (by linarith) (by linarith) (by positivity)
    _ = s.time * (X * (Real.log ((H.pinchingShift + s.time) * X) - 3)) := by ring
    _ ≤ s.time * metricScalarAt s.metric y := mul_le_mul_of_nonneg_left hbar' ht.le

end GC.LongTime.Ch12

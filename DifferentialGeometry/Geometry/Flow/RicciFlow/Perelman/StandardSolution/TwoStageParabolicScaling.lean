import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarLower
import Mathlib.Algebra.Order.Group.Pointwise.Interval

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

theorem parabolicTime_initialScalar {tau0 Q : ℝ} (htau0 : 0 < tau0) (hQ : 0 < Q)
    (t u : ℝ) :
    parabolicTime 0 tau0⁻¹ (parabolicTime (t / tau0) (tau0 * Q) u) =
      parabolicTime t Q u := by
  unfold parabolicTime
  field_simp [htau0.ne', hQ.ne']
  ring

theorem parabolicInterval_initialScalar
    (D : RealTimeInterval) (hzero : (0 : ℝ) ∈ D.carrier)
    {tau0 Q : ℝ} (htau0 : 0 < tau0) (hQ : 0 < Q)
    (t : ℝ) (ht : t ∈ D.carrier) :
    let D₁ := parabolicInterval D 0 tau0⁻¹ hzero
    let ht₁ : t / tau0 ∈ D₁.carrier := by
      change parabolicTime 0 tau0⁻¹ (t / tau0) ∈ D.carrier
      simpa [parabolicTime, div_inv_eq_mul, htau0.ne'] using ht
    let D₂ := parabolicInterval D₁ (t / tau0) (tau0 * Q) ht₁
    D₂.carrier = (parabolicInterval D t Q ht).carrier ∧
      D₂.regular = (parabolicInterval D t Q ht).regular := by
  dsimp only
  constructor
  · ext u
    change (parabolicTime 0 tau0⁻¹ (parabolicTime (t / tau0) (tau0 * Q) u) ∈ D.carrier) ↔
      parabolicTime t Q u ∈ D.carrier
    rw [parabolicTime_initialScalar htau0 hQ]
  · ext u
    change (parabolicTime 0 tau0⁻¹ (parabolicTime (t / tau0) (tau0 * Q) u) ∈ D.regular) ↔
      parabolicTime t Q u ∈ D.regular
    rw [parabolicTime_initialScalar htau0 hQ]

theorem parabolicTime_image_backwardWindow {Q : ℝ} (hQ : 0 < Q) (t L : ℝ) :
    parabolicTime t Q '' Icc (-L) 0 = Icc (t - L / Q) t := by
  change (fun u : ℝ => t + u / Q) '' Icc (-L) 0 = Icc (t - L / Q) t
  simpa only [div_eq_mul_inv, mul_comm, add_comm, mul_neg,
    mul_zero, zero_add, add_zero, sub_eq_add_neg] using
    (image_affine_Icc' (inv_pos.mpr hQ) t (-L) 0)

section MetricFamily

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem parabolicFamily_twoStage_metric
    (G : SolutionFamily (I := I) (M := M))
    {tau0 Q : ℝ} (htau0 : 0 < tau0) (hQ : 0 < Q) (t u : ℝ) :
    (parabolicFamily (parabolicFamily G 0 tau0⁻¹ (inv_pos.mpr htau0))
      (t / tau0) (tau0 * Q) (mul_pos htau0 hQ)).metric u =
        scaleMetric Q hQ (G.metric (t + u / Q)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [parabolicFamily, scaleMetric_inner]
  rw [parabolicTime_initialScalar htau0 hQ]
  change (tau0 * Q) * (tau0⁻¹ * (G.metric (t + u / Q)).inner x v w) =
    Q * (G.metric (t + u / Q)).inner x v w
  field_simp [htau0.ne']

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [BoundarylessManifold I M] in
theorem metricScalarAt_parabolicFamily_initial
    (G : SolutionFamily (I := I) (M := M))
    {tau0 : ℝ} (htau0 : 0 < tau0) (t : ℝ) (x : M) :
    metricScalarAt ((parabolicFamily G 0 tau0⁻¹ (inv_pos.mpr htau0)).metric (t / tau0)) x =
      tau0 * metricScalarAt (G.metric t) x := by
  have htime : parabolicTime 0 tau0⁻¹ (t / tau0) = t := by
    simp [parabolicTime, div_inv_eq_mul, htau0.ne']
  change metricScalarAt
    (scaleMetric tau0⁻¹ (inv_pos.mpr htau0) (G.metric (parabolicTime 0 tau0⁻¹ (t / tau0)))) x = _
  rw [htime, metricScalarAt_scaleMetric, inv_inv]

end MetricFamily

theorem PartialStandardSolution.twoStage_parabolic_normalization
    (S : PartialStandardSolution) {tau0 : ℝ} (htau0 : 0 < tau0)
    (t : ℝ) (ht : t ∈ S.domain) (htau0t : tau0 ≤ t)
    (x : EuclideanSpace ℝ (Fin 3)) :
    let Q := metricScalarAt (S.metric t) x
    let hQ : 0 < Q := lt_of_lt_of_le zero_lt_one (S.one_le_scalar t ht x)
    let G₁ := parabolicFamily S.toSolutionOn.base 0 tau0⁻¹ (inv_pos.mpr htau0)
    let G₂ := parabolicFamily G₁ (t / tau0) (tau0 * Q) (mul_pos htau0 hQ)
    1 ≤ t / tau0 ∧
      metricScalarAt (G₁.metric (t / tau0)) x = tau0 * Q ∧
      metricScalarAt (G₂.metric 0) x = 1 ∧
      ∀ u ∈ Icc (-(Q * t)) 0,
        u ∈ (parabolicInterval (lifetimeInterval S.lifetime S.lifetime_pos) t Q ht).carrier ∧
          G₂.metric u = scaleMetric Q hQ (S.metric (t + u / Q)) := by
  let Q := metricScalarAt (S.metric t) x
  have hQ : 0 < Q := lt_of_lt_of_le zero_lt_one (S.one_le_scalar t ht x)
  let G₁ := parabolicFamily S.toSolutionOn.base 0 tau0⁻¹ (inv_pos.mpr htau0)
  let G₂ := parabolicFamily G₁ (t / tau0) (tau0 * Q) (mul_pos htau0 hQ)
  have hmetric (u : ℝ) : G₂.metric u = scaleMetric Q hQ (S.metric (t + u / Q)) :=
    parabolicFamily_twoStage_metric S.toSolutionOn.base htau0 hQ t u
  refine ⟨(le_div_iff₀ htau0).mpr (by simpa using htau0t), ?_, ?_, ?_⟩
  · exact metricScalarAt_parabolicFamily_initial S.toSolutionOn.base htau0 t x
  · have hmetric0 : G₂.metric 0 = scaleMetric Q hQ (S.metric t) := by
      simpa only [zero_div, add_zero] using hmetric 0
    change metricScalarAt (G₂.metric 0) x = 1
    rw [hmetric0, metricScalarAt_scaleMetric]
    exact inv_mul_cancel₀ hQ.ne'
  · intro u hu
    have hwindow : parabolicTime t Q u ∈ Icc (t - (Q * t) / Q) t := by
      rw [← parabolicTime_image_backwardWindow hQ t (Q * t)]
      exact ⟨u, hu, rfl⟩
    have hleft : t - (Q * t) / Q = 0 := by
      field_simp [hQ.ne']
      ring
    rw [hleft] at hwindow
    have htime := (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht
    refine ⟨?_, hmetric u⟩
    change parabolicTime t Q u ∈ S.domain
    exact (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos _).mpr
      ⟨hwindow.1, (ENNReal.ofReal_le_ofReal hwindow.2).trans_lt htime.2⟩

end DifferentialGeometry.PDE.RicciFlow

end

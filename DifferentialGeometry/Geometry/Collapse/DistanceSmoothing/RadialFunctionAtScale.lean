import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.RadialFunction
import DifferentialGeometry.Geometry.Collapse.AnnularAdaptedCoordinates
import DifferentialGeometry.Geometry.Collapse.RiemannianConeScale

/-!
# LC30 at a prescribed scale `R`

`exists_radialFunction_of_kleinerLottApprox` (LC30) is stated at unit scale for the PC Riemannian
setting. This adapter applies it to the normalized manifold `(M, R⁻¹ d, R⁻² g)`: the metric space
`m.rescale R⁻¹`, the bundle metric `radialScaledBundle g R⁻¹` and its Riemannian-manifold instance
`radialScaledManifold` (the pattern of `selected_center_adapted_coordinate_of_original_buffer`). The
inputs are the ORIGINAL ones: a Kleiner–Lott map of `(M, R⁻¹ d, p)`, and the curvature buffer
`sec_g ≥ -(1/60)² R⁻²` on `B_g(p, 400 R)`; the conclusion is LC30's verbatim, for the normalized
data. It is the scale-`R` radial-function input of LC55 and LC57 (master207A, A:22905, A:23106).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Real
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [hM : CompleteSpace M]

/-- **LC30 at scale `R`.** From a Kleiner–Lott `δ`-map of `(M, R⁻¹ d, p)` to a radial cone and the
original buffer `sec_g ≥ -(1/60)² R⁻²` on `B_g(p, 400 R)`, the normalized manifold
`(M, R⁻¹ d, R⁻² g)` carries an LC30 radial function with all of LC30's clauses. -/
theorem exists_radialFunction_of_kleinerLottApprox_at_scale (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    {p : M} {R : ℝ} (hR : 0 < R) {C : Type*} [MetricSpace C] {o : C} {δ ε e : ℝ}
    (φ : @KleinerLottApprox M C (m.rescale R⁻¹ (inv_pos.mpr hR)) _ p o δ)
    (H : RadialConeData o)
    (hsec : ∀ y ∈ Metric.ball p (400 * R),
      SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * R⁻¹ ^ 2)))
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : δ < radialSmoothingConeError (ε / 4)) (he : 0 < e)
    (he1 : e < 1 / 40) :
    letI := m.rescale R⁻¹ (inv_pos.mpr hR)
    let gR := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
    ∃ F : M → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      (∃ O : Set M, IsOpen O ∧ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ⊆ O ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O) ∧
      (∀ x, |F x - Metric.infDist x {p}| < e) ∧
      (∀ x, x ∉ {x : M | 1 / 20 < dist x p ∧ dist x p < 20} → F x = Metric.infDist x {p}) ∧
      (∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤ ε * dist x y) ∧
      (∀ x, 0 ≤ F x) ∧ F p = 0 ∧
      (∀ q ∈ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
        1 - ε ≤ Real.sqrt (gR.inner q (gradFun gR F q) (gradFun gR F q)) ∧
          Real.sqrt (gR.inner q (gradFun gR F q) (gradFun gR F q)) ≤ 1 + ε) ∧
      (∀ x, F x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
      F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
      ∃ O' : Set M, IsOpen O' ∧ F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O' ∧ ∀ q ∈ O', gradFun gR F q ≠ 0 := by
  have hRinv : 0 < R⁻¹ := inv_pos.mpr hR
  have hMR : @CompleteSpace M (m.rescale R⁻¹ hRinv).toUniformSpace :=
    (m.rescale_completeSpace_iff R⁻¹ hRinv).mpr hM
  have hsecR : ∀ y ∈ @Metric.ball M (m.rescale R⁻¹ hRinv).toPseudoMetricSpace p 400,
      SectionalBoundedBelowAt (scaleMetric (R⁻¹ ^ 2) (pow_pos hRinv 2) g) y
        (-(1 / 60) ^ 2) := by
    intro y hy
    have hy' : R⁻¹ * dist y p < 400 := hy
    have hyR : y ∈ Metric.ball p (400 * R) := by
      rw [Metric.mem_ball]
      have := (inv_mul_lt_iff₀ hR).mp hy'
      linarith
    rw [sectionalBoundedBelowAt_scaleMetric_iff]
    simpa only [neg_mul] using hsec y hyR
  let := m.rescale R⁻¹ hRinv
  let := radialScaledBundle g R⁻¹ hRinv
  let := radialScaledContinuous g R⁻¹ hRinv
  let := radialScaledManifold (m := m) g hmetric R⁻¹ hRinv
  let gR := scaleMetric (R⁻¹ ^ 2) (pow_pos hRinv 2) g
  have hEnorm : IsMetricNorm gR := isMetricNorm_of_riemannianBundle gR
  exact exists_radialFunction_of_kleinerLottApprox gR hEnorm φ H hsecR hε hε1 hδ he he1

end DifferentialGeometry.Geometry.Collapse

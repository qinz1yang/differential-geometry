import DifferentialGeometry.Geometry.Comparison.FiniteMetric.FourPointApproximants
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.SigmaCompact
import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle

/-!
# Four-point comparison for a complete finite-regularity metric with `sec ≥ 0` (CM5.c)

Lane CM-A, package CM5.c of the D-FOUND design (§C1, §D1). A pure distance statement, proved by
smooth approximation (CM5.a, `exists_smooth_approximants_sigmaCompact`) and the kernel
`fourPointComparison_zero_ball_of_approximants`; no geodesic theory of the finite metric is used.

The distance is the ambient complete distance, which is the length distance of the Riemannian
bundle (`IsRiemannianManifold`) whose norm is the `g`-norm (`hnorm`).

* `fourPointComparison_zero_ball_finite` (local form, for the finite LC21 rows LFR55–59): if
  `sec_g ≥ 0` on `ball o (32 R)`, the four-point comparison at curvature `0` holds on `ball o R`.
* `metricComparisonAngle_sum_le_two_pi_finite` (the frozen CM5.c statement, with `2 ≤ n` in
  place of the frozen `4 ≤ n`; the verbatim form is kept as an `example`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.FiniteComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- **CM5.c, local form.** For a complete `C^n` metric `g` (`2 ≤ n`) whose length distance is the
ambient distance, `sec_g ≥ 0` on `ball o (32 R)` gives the four-point comparison at curvature `0`
on `ball o R`. -/
theorem fourPointComparison_zero_ball_finite [CompleteSpace M] {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (o : M) (R : ℝ)
    (hsec : ∀ y ∈ Metric.ball o (32 * R), ∀ v w : TangentSpace I y,
      0 ≤ g.sectionalCurvature y v w) :
    fourPointComparison 0 (Metric.ball o R) := by
  obtain ⟨gSeq, hbil, hcurv⟩ :=
    DifferentialGeometry.Geometry.MetricSmoothing.exists_smooth_approximants_sigmaCompact g hn
  exact fourPointComparison_zero_ball_of_approximants g hnorm gSeq hbil hcurv o R hsec

/-- **CM5.c (frozen statement, strengthened to `2 ≤ n`).** For a complete `C^n` metric `g` with
nonnegative finite-order sectional curvature whose length distance is the ambient distance, the
three comparison angles at `p` of any three points distinct from `p` sum to at most `2π`. -/
theorem metricComparisonAngle_sum_le_two_pi_finite [CompleteSpace M] {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (p a b c : M) (ha : a ≠ p) (hb : b ≠ p) (hc : c ≠ p) :
    metricComparisonAngle a p b + metricComparisonAngle b p c + metricComparisonAngle c p a ≤
      2 * Real.pi := by
  set R : ℝ := dist p a + dist p b + dist p c + 1 with hR
  have hcomp := fourPointComparison_zero_ball_finite g hn hnorm p R (fun y _ => hsec y)
  have hmem (z : M) (hz : dist p z ≤ dist p a + dist p b + dist p c) : z ∈ Metric.ball p R :=
    Metric.mem_ball'.mpr (by linarith)
  have h := hcomp p (Metric.mem_ball_self (by positivity)) a
    (hmem a (by linarith [dist_nonneg (x := p) (y := b), dist_nonneg (x := p) (y := c)])) b
    (hmem b (by linarith [dist_nonneg (x := p) (y := a), dist_nonneg (x := p) (y := c)])) c
    (hmem c (by linarith [dist_nonneg (x := p) (y := a), dist_nonneg (x := p) (y := b)]))
    ha hb hc
  simpa only [comparisonAngleNegCurvature_zero, metricComparisonAngle] using h

/-- The frozen D-FOUND signature of CM5.c (`4 ≤ n`), as a consumer of the strengthened form. -/
example [CompleteSpace M] {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (4 : ℕ∞ω) ≤ n)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (p a b c : M) (ha : a ≠ p) (hb : b ≠ p) (hc : c ≠ p) :
    metricComparisonAngle a p b + metricComparisonAngle b p c + metricComparisonAngle c p a ≤
      2 * Real.pi :=
  metricComparisonAngle_sum_le_two_pi_finite g (le_trans (by norm_num) hn) hnorm hsec p a b c
    ha hb hc

end DifferentialGeometry.Geometry.FiniteComparison

import DifferentialGeometry.Geometry.Comparison.RiemannianFourPoint
import DifferentialGeometry.Geometry.Comparison.EightChartCovering
import DifferentialGeometry.Geometry.Comparison.IntrinsicLocalComparison
import DifferentialGeometry.Geometry.Metric.AmbientSmoothChart
import DifferentialGeometry.Geometry.Metric.RiemannianShortCurves

set_option autoImplicit false
open Set Metric Manifold
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [CompleteSpace M]

theorem exists_closedBall_net_of_sectional_lower_bound
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (o : M) {κ R ε : ℝ} (hκ : κ ≤ 1) (hR : 0 < R) (hε : 0 < ε)
    (hsec : ∀ y ∈ ball o (8 * R), SectionalBoundedBelowAt g y (-κ)) :
    ∃ T : Finset M,
      T.card ≤ (1 + ⌈4 * (2 : ℝ) ^ 2 * Real.sqrt (Module.finrank ℝ E) *
        Real.sinh (2 * R) / ε⌉₊) ^ Module.finrank ℝ E ∧
      (T : Set M) ⊆ closedBall o R ∧ ∀ x ∈ closedBall o R, ∃ y ∈ T, dist x y < ε := by
  let hcurves := fun (a b : M) (ε : ℝ) (hε : 0 < ε) =>
    DifferentialGeometry.Geometry.Metric.exists_arbitrarily_short_riemannian_curve g hmetric a b hε
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  have : LocallyCompactSpace (ball o (8 * R)) := Metric.isOpen_ball.locallyCompactSpace
  have hlocal := exists_local_fourPointComparison_of_sectional_lower_bound
    g hmetric (Ω := ball o (8 * R)) Metric.isOpen_ball zero_le_one (by
      intro y hy
      exact (hsec y hy).mono (by linarith))
  obtain ⟨δ, hδ, φ, hφ0, _, hφlower, hφupper, _⟩ :=
    DifferentialGeometry.Geometry.Metric.exists_centered_ambient_two_bilipschitz_ball_chart
      g hmetric o
  refine exists_closedBall_net_of_intrinsic_8_comparison_and_chart hcurves o hR
    (fun z => ?_) (Metric.mem_ball_self (half_pos hR))
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))) (by norm_num) hδ hε φ
    hφ0 hφlower hφupper
  exact (exists_local_fourPointComparison_intrinsicBall_iff hcurves o
    (by positivity : 0 < 8 * R) z).mpr (hlocal z z.property)

end DifferentialGeometry.Geometry.Comparison.Toponogov

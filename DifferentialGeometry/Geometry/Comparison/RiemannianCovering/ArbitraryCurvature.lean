import DifferentialGeometry.Geometry.Comparison.EightChartCovering.Rescale
import DifferentialGeometry.Geometry.Comparison.RiemannianCovering

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

theorem exists_closedBall_net_of_arbitrary_sectional_lower_bound
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (o : M) {κ R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hsec : ∀ y ∈ ball o (8 * R), SectionalBoundedBelowAt g y (-κ)) :
    ∃ T : Finset M,
      T.card ≤ (1 + ⌈4 * (2 : ℝ) ^ 2 * Real.sqrt (Module.finrank ℝ E) *
        Real.sinh (2 * (Real.sqrt (max 1 κ) * R)) /
        (Real.sqrt (max 1 κ) * ε)⌉₊) ^ Module.finrank ℝ E ∧
      (T : Set M) ⊆ closedBall o R ∧ ∀ x ∈ closedBall o R, ∃ y ∈ T, dist x y < ε := by
  have hκ : 0 < max 1 κ := zero_lt_one.trans_le (le_max_left _ _)
  let hcurves := fun (a b : M) (ε : ℝ) (hε : 0 < ε) =>
    DifferentialGeometry.Geometry.Metric.exists_arbitrarily_short_riemannian_curve g hmetric a b hε
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  have : LocallyCompactSpace (ball o (8 * R)) := Metric.isOpen_ball.locallyCompactSpace
  have hlocal := exists_local_fourPointComparison_of_sectional_lower_bound
    g hmetric (Ω := ball o (8 * R)) Metric.isOpen_ball hκ.le (by
      intro y hy
      exact (hsec y hy).mono (neg_le_neg (le_max_right _ _)))
  obtain ⟨δ, hδ, φ, hφ0, _, hφlower, hφupper, _⟩ :=
    DifferentialGeometry.Geometry.Metric.exists_centered_ambient_two_bilipschitz_ball_chart
      g hmetric o
  exact exists_closedBall_net_of_positive_curvature_scale_and_chart hcurves o hκ hR
    hlocal (Metric.mem_ball_self (half_pos hR))
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))) (by norm_num)
    hδ hε φ hφ0 hφlower hφupper

end DifferentialGeometry.Geometry.Comparison.Toponogov

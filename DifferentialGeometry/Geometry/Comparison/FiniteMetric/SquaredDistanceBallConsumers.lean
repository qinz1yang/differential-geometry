import DifferentialGeometry.Geometry.Comparison.FiniteMetric.SquaredDistanceBall

/-!
# Consumer of the ball forms of CM5.d

For a complete `C³` metric (`r = 2`) with `sec ≥ 0` on `ball o (32 R)`: along a minimizing radial
geodesic `t ↦ exp_o (t u)` of length `a < R`, `t ↦ t² - d(q, exp_o (t u))²` is convex on `[0, a]`
for every `q ∈ ball o R`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.FiniteComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- Ball-local LFR55 on a minimizing radial geodesic of a complete `C³` metric. -/
theorem convexOn_sq_sub_sq_dist_expMap_ball_C3
    (g : ContMDiffRiemannianMetric I 3 E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {o : M} {R : ℝ}
    (hsec : ∀ y ∈ Metric.ball o (32 * R), ∀ w₁ w₂ : TangentSpace I y,
      0 ≤ g.sectionalCurvature y w₁ w₂)
    {u : E} {a : ℝ} (haR : a < R) (hu : g.inner o u u = 1)
    (hmin : dist o (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) = a)
    {q : M} (hq : q ∈ Metric.ball o R) :
    ConvexOn ℝ (Icc 0 a)
      (fun t => t ^ 2 - dist q (g.expMap (⟨o, t • u⟩ : TangentBundle I M)) ^ 2) := by
  obtain ⟨hrad, hseg⟩ := g.dist_expMap_smul_eq_of_dist_eq (r := 2) (by norm_num) hnorm hu hmin
  refine convexOn_sq_sub_sq_dist_ball_finite (r := 2) g (by norm_num) hnorm hsec (convex_Icc 0 a)
    (σ := fun t => g.expMap (⟨o, t • u⟩ : TangentBundle I M)) hseg (fun t ht => ?_) hq
  rw [Metric.mem_ball, dist_comm]
  exact (hrad t ht).trans_lt (ht.2.trans_lt haR)

end DifferentialGeometry.Geometry.FiniteComparison

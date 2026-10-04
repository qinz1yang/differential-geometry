import DifferentialGeometry.Geometry.Comparison.FiniteMetric.SquaredDistanceGeodesic

/-!
# Consumer of LFR55 along all geodesics

For a complete `C³` metric (`r = 2`, the lowest covered order) with `sec ≥ 0`: along every
radial geodesic `t ↦ exp_o (t u)` on any interval `J`, `t ↦ g_o(u,u) t² - d(q, exp_o (t u))²` is
convex — the restriction of `convexOn_inner_mul_sq_sub_sq_dist_expMap_finite`.
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

/-- LFR55 for a complete `C³` metric with `sec ≥ 0`, on an arbitrary parameter interval. -/
theorem convexOn_inner_mul_sq_sub_sq_dist_expMap_C3
    (g : ContMDiffRiemannianMetric I 3 E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (o : M) (u : E) (q : M) {J : Set ℝ} (hJ : Convex ℝ J) :
    ConvexOn ℝ J (fun t => g.inner o u u * t ^ 2 -
      dist q (g.expMap (⟨o, t • u⟩ : TangentBundle I M)) ^ 2) :=
  (convexOn_inner_mul_sq_sub_sq_dist_expMap_finite (r := 2) g le_rfl hnorm hsec o u q).subset
    (subset_univ J) hJ

end DifferentialGeometry.Geometry.FiniteComparison

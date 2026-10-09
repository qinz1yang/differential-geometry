import DifferentialGeometry.Geometry.Comparison.FiniteMetric.SquaredDistance
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.FourPoint

/-!
# CM5.d on balls: squared-distance comparison with `sec ≥ 0` only on a ball

Ball-local forms of CM-A2's CM5.d (LFR55's conclusions) for a complete finite-regularity metric
with `sec_g ≥ 0` on `ball o (32 R)` only, through CM-A's four-point comparison on `ball o R`
(`fourPointComparison_zero_ball_finite`):

* `sq_dist_le_point_on_side_ball_finite`: the point-on-side inequality for points of `ball o R`;
* `convexOn_sq_sub_sq_dist_ball_finite`: `t ↦ t² - d(q, σ t)²` is convex along every isometric
  segment `σ` inside `ball o R`, for `q ∈ ball o R`;
* `comparisonAngle_expMap_antitone_ball_finite`: arm-wise monotonicity of the comparison angle of
  a minimizing hinge at `o` with arm lengths `a, b < R`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.FiniteComparison

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- `2 ≤ r + 1` in `ℕ∞ω` from `1 ≤ r`. -/
theorem two_le_coe_add_one_of_one_le (hr : 1 ≤ r) : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := by
  have h1 : ((1 : ℕ∞) : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr
  calc (2 : ℕ∞ω) = 1 + 1 := by norm_num
    _ ≤ (r : ℕ∞ω) + 1 := by gcongr; simpa using h1

/-- **Point-on-side comparison on a ball**: with `sec ≥ 0` on `ball o (32 R)`, for points of
`ball o R` with `z` dividing `[a, b]` in the ratio `t : 1 - t`,
`(1 - t) d(v,a)² + t d(v,b)² - t(1 - t) d(a,b)² ≤ d(v,z)²`. -/
theorem sq_dist_le_point_on_side_ball_finite
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {o : M} {R : ℝ}
    (hsec : ∀ y ∈ Metric.ball o (32 * R), ∀ w₁ w₂ : TangentSpace I y,
      0 ≤ g.sectionalCurvature y w₁ w₂)
    {a b z v : M} (ha : a ∈ Metric.ball o R) (hb : b ∈ Metric.ball o R)
    (hz : z ∈ Metric.ball o R) (hv : v ∈ Metric.ball o R) {t : ℝ} (ht : t ∈ Icc 0 1)
    (haz : dist a z = t * dist a b) (hzb : dist z b = (1 - t) * dist a b) :
    (1 - t) * dist v a ^ 2 + t * dist v b ^ 2 - t * (1 - t) * dist a b ^ 2 ≤ dist v z ^ 2 :=
  quadratic_side_comparison_of_fourPointComparison
    (fourPointComparison_zero_ball_finite g (two_le_coe_add_one_of_one_le hr) hnorm o R hsec)
    ha hb hz hv ht haz hzb

/-- **Convexity of `t² - d(q, σ t)²` on a ball**: with `sec ≥ 0` on `ball o (32 R)`, along every
isometric segment `σ` inside `ball o R` and for every `q ∈ ball o R`. -/
theorem convexOn_sq_sub_sq_dist_ball_finite
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {o : M} {R : ℝ}
    (hsec : ∀ y ∈ Metric.ball o (32 * R), ∀ w₁ w₂ : TangentSpace I y,
      0 ≤ g.sectionalCurvature y w₁ w₂)
    {J : Set ℝ} (hJ : Convex ℝ J) {σ : ℝ → M}
    (hσ : ∀ s ∈ J, ∀ t ∈ J, dist (σ s) (σ t) = |s - t|) (hmem : ∀ t ∈ J, σ t ∈ Metric.ball o R)
    {q : M} (hq : q ∈ Metric.ball o R) :
    ConvexOn ℝ J (fun t => t ^ 2 - dist q (σ t) ^ 2) :=
  convexOn_sq_sub_sq_dist_of_fourPointComparison
    (fourPointComparison_zero_ball_finite g (two_le_coe_add_one_of_one_le hr) hnorm o R hsec)
    hJ hσ hmem hq

/-- **Arm-wise monotonicity on a ball**: with `sec ≥ 0` on `ball o (32 R)`, the comparison angle
`θ(s, t)` of a minimizing hinge `(exp_o (s u), o, exp_o (t v))` with arm lengths `a, b < R` is
nonincreasing in each arm length on `(0, a] × (0, b]`. -/
theorem comparisonAngle_expMap_antitone_ball_finite
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {o : M} {R : ℝ}
    (hsec : ∀ y ∈ Metric.ball o (32 * R), ∀ w₁ w₂ : TangentSpace I y,
      0 ≤ g.sectionalCurvature y w₁ w₂)
    (u v : E) {a b : ℝ} (hR : 0 < R) (haR : a < R) (hbR : b < R)
    (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : dist o (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) = a)
    (hminB : dist o (g.expMap (⟨o, b • v⟩ : TangentBundle I M)) = b) :
    DifferentialGeometry.Toponogov.CoordinatewiseNonincreasingOn a b
      (fun s t => comparisonAngle s t (dist (g.expMap (⟨o, s • u⟩ : TangentBundle I M))
        (g.expMap (⟨o, t • v⟩ : TangentBundle I M)))) := by
  obtain ⟨hγrad, hγmin⟩ := g.dist_expMap_smul_eq_of_dist_eq hr hnorm hu hminA
  obtain ⟨hβrad, hβmin⟩ := g.dist_expMap_smul_eq_of_dist_eq hr hnorm hv hminB
  have h := comparisonAngleNegCurvature_antitone_on_segments le_rfl
    (fourPointComparison_zero_ball_finite g (two_le_coe_add_one_of_one_le hr) hnorm o R hsec)
    (Metric.mem_ball_self hR)
    (γ := fun s => g.expMap (⟨o, s • u⟩ : TangentBundle I M))
    (β := fun t => g.expMap (⟨o, t • v⟩ : TangentBundle I M))
    (fun s hs => hγrad s (Ioc_subset_Icc_self hs)) (fun t ht => hβrad t (Ioc_subset_Icc_self ht))
    (fun s hs t ht => hγmin s (Ioc_subset_Icc_self hs) t (Ioc_subset_Icc_self ht))
    (fun s hs t ht => hβmin s (Ioc_subset_Icc_self hs) t (Ioc_subset_Icc_self ht))
    (fun s hs => by
      rw [Metric.mem_ball, dist_comm, hγrad s (Ioc_subset_Icc_self hs)]
      exact hs.2.trans_lt haR)
    (fun t ht => by
      rw [Metric.mem_ball, dist_comm, hβrad t (Ioc_subset_Icc_self ht)]
      exact ht.2.trans_lt hbR)
  simpa only [comparisonAngleNegCurvature_zero] using h

end DifferentialGeometry.Geometry.FiniteComparison

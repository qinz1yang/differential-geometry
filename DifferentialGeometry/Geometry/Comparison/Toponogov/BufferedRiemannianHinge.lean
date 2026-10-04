import DifferentialGeometry.Geometry.Comparison.Toponogov.LowerCurvatureHinge
import DifferentialGeometry.Geometry.Comparison.FourPoint

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [CompleteSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem hyperbolicComparisonAngle_le_arccos_inner_of_sectional_lower_bound_on_eight_ball
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (o x A B : M) {k R : ℝ} (hk : 0 < k)
    (hx : x ∈ Metric.ball o R) (hA : A ∈ Metric.ball o R) (hB : B ∈ Metric.ball o R)
    (hAx : A ≠ x) (hBx : B ≠ x) (U V : TangentSpace I x)
    (hU : g.inner x U U = 1) (hV : g.inner x V V = 1)
    (hUA : intrinsicGeodesic g hEnorm x U (dist x A) = A)
    (hVB : intrinsicGeodesic g hEnorm x V (dist x B) = B)
    (hsec : ∀ y ∈ Metric.ball o (8 * R), SectionalBoundedBelowAt g y (-k ^ 2)) :
    hyperbolicComparisonAngle k (dist x A) (dist x B) (dist A B) ≤
      Real.arccos (g.inner x U V) := by
  have he (a b : M) : riemannianEDist I a b = ENNReal.ofReal (dist a b) := by
    rw [← IsRiemannianManifold.out, edist_dist]
  have hd (a b : M) : (riemannianEDist I a b).toReal = dist a b := by
    rw [he, ENNReal.toReal_ofReal dist_nonneg]
  have hpos (a : M) (hax : a ≠ x) : 0 < dist x a := dist_pos.mpr hax.symm
  change dist x o < R at hx
  have hR : 0 < R := dist_nonneg.trans_lt hx
  have hminA : (riemannianEDist I x
      (intrinsicGeodesic g hEnorm x U (dist x A))).toReal = dist x A := by rw [hUA, hd]
  have hminB : (riemannianEDist I x
      (intrinsicGeodesic g hEnorm x V (dist x B))).toReal = dist x B := by rw [hVB, hd]
  have hA2 : dist x A < 2 * R := by
    have h := dist_triangle x o A
    rw [dist_comm o A] at h
    linarith [Metric.mem_ball.mp hA]
  have hB2 : dist x B < 2 * R := by
    have h := dist_triangle x o B
    rw [dist_comm o B] at h
    linarith [Metric.mem_ball.mp hB]
  have hlens : ∀ s ∈ Icc (0 : ℝ) (dist x A), ∀ t ∈ Icc (0 : ℝ) (dist x B), ∀ y : M,
      riemannianEDist I (intrinsicGeodesic g hEnorm x U s) y +
        riemannianEDist I y (intrinsicGeodesic g hEnorm x V t) =
        riemannianEDist I (intrinsicGeodesic g hEnorm x U s)
          (intrinsicGeodesic g hEnorm x V t) →
      SectionalBoundedBelowAt g y (-k ^ 2) := by
    intro s hs t ht y hy
    let P := intrinsicGeodesic g hEnorm x U s
    let Q := intrinsicGeodesic g hEnorm x V t
    have hxs : dist x P = s := by
      have h := unit_intrinsic_subsegment_dist g hEnorm x U hU
        (dist x A) s (hpos A hAx) hs.1 hs.2 hminA
      rwa [hd] at h
    have hxt : dist x Q = t := by
      have h := unit_intrinsic_subsegment_dist g hEnorm x V hV
        (dist x B) t (hpos B hBx) ht.1 ht.2 hminB
      rwa [hd] at h
    have hyreal : dist P y + dist y Q = dist P Q := by
      rw [he, he, he, ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at hy
      simpa only [ENNReal.toReal_ofReal (add_nonneg dist_nonneg dist_nonneg),
        ENNReal.toReal_ofReal dist_nonneg] using congrArg ENNReal.toReal hy
    have hPQ : dist P Q ≤ s + t := by
      have h := dist_triangle P x Q
      rwa [dist_comm P x, hxs, hxt] at h
    have hxy : dist x y ≤ 2 * s + t := by
      have h := dist_triangle x P y
      rw [hxs] at h
      linarith [dist_nonneg (x := y) (y := Q)]
    apply hsec y
    change dist y o < 8 * R
    have h := dist_triangle y x o
    rw [dist_comm y x] at h
    linarith [hx, hs.2, ht.2]
  have h := hyperbolicComparisonAngle_le_arccos_inner_of_sectional_lower_bound_on_minimizing_lenses
    g hEnorm x U V hk (hpos A hAx) (hpos B hBx) hU hV hminA hminB hlens
  rw [hUA, hVB, hd] at h
  exact h

theorem inner_le_hyperbolicComparisonCosine_of_sectional_lower_bound_on_eight_ball
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (o x A B : M) {k R : ℝ} (hk : 0 < k)
    (hx : x ∈ Metric.ball o R) (hA : A ∈ Metric.ball o R) (hB : B ∈ Metric.ball o R)
    (hAx : A ≠ x) (hBx : B ≠ x) (U V : TangentSpace I x)
    (hU : g.inner x U U = 1) (hV : g.inner x V V = 1)
    (hUA : intrinsicGeodesic g hEnorm x U (dist x A) = A)
    (hVB : intrinsicGeodesic g hEnorm x V (dist x B) = B)
    (hsec : ∀ y ∈ Metric.ball o (8 * R), SectionalBoundedBelowAt g y (-k ^ 2)) :
    g.inner x U V ≤ hyperbolicComparisonCosine k (dist x A) (dist x B) (dist A B) := by
  have hangle :=
    hyperbolicComparisonAngle_le_arccos_inner_of_sectional_lower_bound_on_eight_ball
      g hEnorm o x A B hk hx hA hB hAx hBx U V hU hV hUA hVB hsec
  have hn (Z : TangentSpace I x) (hZ : g.inner x Z Z = 1) : ‖Z‖ = 1 := by
    rw [norm_eq_sqrt_real_inner, hEnorm.inner_eq, hZ, Real.sqrt_one]
  have hi : |g.inner x U V| ≤ 1 := by
    simpa only [hEnorm.inner_eq, hn U hU, hn V hV, one_mul] using
      abs_real_inner_le_norm U V
  have hmodel := cos_comparisonAngleNegCurvature_of_pos (sq_pos_of_pos hk)
    (dist_pos.mpr hAx.symm) (dist_pos.mpr hBx.symm)
    (by simpa only [dist_comm A x, dist_comm B x] using abs_dist_sub_le A B x)
    (show dist A B ≤ dist x A + dist x B by simpa only [dist_comm A x] using
      (dist_triangle A x B))
  simp only [comparisonAngleNegCurvature, ite_eq_right (pow_ne_zero 2 hk.ne'),
    Real.sqrt_sq hk.le] at hmodel
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _)
    (Real.arccos_le_pi _) hangle
  rw [Real.cos_arccos (abs_le.mp hi).1 (abs_le.mp hi).2] at hc
  exact hc.trans_eq hmodel

end DifferentialGeometry.Geometry.Comparison.Toponogov

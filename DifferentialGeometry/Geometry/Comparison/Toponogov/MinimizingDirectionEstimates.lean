import DifferentialGeometry.Geometry.Comparison.Toponogov.BufferedRiemannianHinge
import DifferentialGeometry.Analysis.InnerProductSpace.AlmostAntipodal
import DifferentialGeometry.Geometry.Comparison.Toponogov.EscapingRadialArms

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

theorem abs_inner_sub_le_of_minimizing_comparison_cosines
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (o x A B z : M) {k R t ε : ℝ} (hk : 0 < k)
    (hx : x ∈ Metric.ball o R) (hA : A ∈ Metric.ball o R)
    (hB : B ∈ Metric.ball o R) (hz : z ∈ Metric.ball o R)
    (hAx : A ≠ x) (hBx : B ≠ x) (hzx : z ≠ x)
    (hsec : ∀ y ∈ Metric.ball o (8 * R), SectionalBoundedBelowAt g y (-k ^ 2))
    (hopposite : hyperbolicComparisonCosine k (dist x A) (dist x B) (dist A B) ≤ -1 + ε)
    (hplus : hyperbolicComparisonCosine k (dist x A) (dist x z) (dist A z) ≤ t + ε)
    (hminus : hyperbolicComparisonCosine k (dist x B) (dist x z) (dist B z) ≤ -t + ε)
    (U W : TangentSpace I x) (hU : g.inner x U U = 1) (hW : g.inner x W W = 1)
    (hUA : intrinsicGeodesic g hEnorm x U (dist x A) = A)
    (hWz : intrinsicGeodesic g hEnorm x W (dist x z) = z) :
    |g.inner x U W - t| ≤ ε + Real.sqrt (2 * ε) := by
  have hd (a b : M) : (riemannianEDist I a b).toReal = dist a b := by
    rw [← IsRiemannianManifold.out, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  obtain ⟨V, hV, hVB⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm x B
    (by rw [hd]; exact dist_pos.mpr hBx.symm)
  rw [hd] at hVB
  have huv := (inner_le_hyperbolicComparisonCosine_of_sectional_lower_bound_on_eight_ball
    g hEnorm o x A B hk hx hA hB hAx hBx U V hU hV hUA hVB hsec).trans hopposite
  have huw := (inner_le_hyperbolicComparisonCosine_of_sectional_lower_bound_on_eight_ball
    g hEnorm o x A z hk hx hA hz hAx hzx U W hU hW hUA hWz hsec).trans hplus
  have hvw := (inner_le_hyperbolicComparisonCosine_of_sectional_lower_bound_on_eight_ball
    g hEnorm o x B z hk hx hB hz hBx hzx V W hV hW hVB hWz hsec).trans hminus
  have hn (Z : TangentSpace I x) (hZ : g.inner x Z Z = 1) : ‖Z‖ = 1 := by
    rw [norm_eq_sqrt_real_inner, hEnorm.inner_eq, hZ, Real.sqrt_one]
  simpa only [hEnorm.inner_eq] using
    InnerProductGeometry.abs_inner_sub_le_of_almost_antipodal
      (hn U hU) (hn V hV) (hn W hW) (by simpa only [hEnorm.inner_eq] using huv)
      (by simpa only [hEnorm.inner_eq] using huw) (by simpa only [hEnorm.inner_eq] using hvw)

theorem arccos_inner_le_of_minimizing_opposite_comparison_cosine
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (o x A B : M) {k R ε : ℝ} (hk : 0 < k)
    (hx : x ∈ Metric.ball o R) (hA : A ∈ Metric.ball o R) (hB : B ∈ Metric.ball o R)
    (hAx : A ≠ x) (hBx : B ≠ x)
    (hsec : ∀ y ∈ Metric.ball o (8 * R), SectionalBoundedBelowAt g y (-k ^ 2))
    (hopposite : hyperbolicComparisonCosine k (dist x A) (dist x B) (dist A B) ≤ -1 + ε)
    (U U' : TangentSpace I x) (hU : g.inner x U U = 1) (hU' : g.inner x U' U' = 1)
    (hUA : intrinsicGeodesic g hEnorm x U (dist x A) = A)
    (hUA' : intrinsicGeodesic g hEnorm x U' (dist x A) = A) :
    Real.arccos (g.inner x U U') ≤ Real.pi * Real.sqrt (2 * ε) := by
  have hd (a b : M) : (riemannianEDist I a b).toReal = dist a b := by
    rw [← IsRiemannianManifold.out, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  obtain ⟨V, hV, hVB⟩ := exists_unit_intrinsic_vector_of_pos_distance g hEnorm x B
    (by rw [hd]; exact dist_pos.mpr hBx.symm)
  rw [hd] at hVB
  have huv := (inner_le_hyperbolicComparisonCosine_of_sectional_lower_bound_on_eight_ball
    g hEnorm o x A B hk hx hA hB hAx hBx U V hU hV hUA hVB hsec).trans hopposite
  have huv' := (inner_le_hyperbolicComparisonCosine_of_sectional_lower_bound_on_eight_ball
    g hEnorm o x A B hk hx hA hB hAx hBx U' V hU' hV hUA' hVB hsec).trans hopposite
  have hn (Z : TangentSpace I x) (hZ : g.inner x Z Z = 1) : ‖Z‖ = 1 := by
    rw [norm_eq_sqrt_real_inner, hEnorm.inner_eq, hZ, Real.sqrt_one]
  have h := InnerProductGeometry.angle_le_of_common_almost_antipode
    (hn U hU) (hn U' hU') (hn V hV) (by simpa only [hEnorm.inner_eq] using huv)
    (by simpa only [hEnorm.inner_eq] using huv')
  simpa only [InnerProductGeometry.angle, hEnorm.inner_eq, hn U hU, hn U' hU',
    one_mul, div_one] using h

end DifferentialGeometry.Geometry.Comparison.Toponogov

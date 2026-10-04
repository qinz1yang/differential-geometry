import DifferentialGeometry.Geometry.Comparison.FiniteMetric.FourPoint
import DifferentialGeometry.Geometry.Collapse.CompleteRiemannianSegments
import DifferentialGeometry.Topology.MetricSpace.GeodesicMidpoint
import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation
import DifferentialGeometry.Geometry.Comparison.CompleteHingeComparison

/-!
# Segments, global four-point comparison and the germ-angle hinge for a finite metric

Lane CM-A (toward CM5.b). For a complete finite-regularity metric `g` (`2 ≤ n`) whose length
distance is the ambient distance:

* `approximate_midpoints_finite`, `exists_isometric_segment_finite`: the distance is geodesic
  (every two points are joined by an isometric segment). Midpoints of the smooth approximants'
  segments (`segments_of_riemannianEDistOf_eq`) are approximate midpoints, and the distance is
  proper (`properSpace_of_bilipschitz_smooth`). No geodesic theory of `g` is used.
* `fourPointComparison_zero_univ_finite`: with `sec_g ≥ 0` everywhere, the four-point comparison
  at curvature `0` holds on the whole space.
* `endpointHingeComparison_zero_finite`: with `sec_g ≥ 0` everywhere, the hinge comparison
  against the germ (Alexandrov) angle of two segments holds at every scale
  (`endpointHingeComparison_of_complete_local_comparison`). CM5.b follows from it once the germ
  angle of the arms `t ↦ exp (t u)`, `t ↦ exp (t v)` is bounded by `arccos (g u v)`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.FiniteComparison

section Step

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- Exact midpoints for the length distance of a complete smooth metric `h` on a manifold that
carries only its topology. -/
theorem exists_midpoint_riemannianEDistOf {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M] [SigmaCompactSpace M]
    (h : SmoothRiemannianMetric I M) (hfin : ∀ a b : M, riemannianEDistOf (I := I) h a b ≠ ⊤)
    (hcomplete : @CompleteSpace M (inducedEMetricSpace h).toPseudoEMetricSpace.toUniformSpace)
    (x y : M) :
    ∃ m : M, (riemannianEDistOf (I := I) h x m).toReal =
        (riemannianEDistOf (I := I) h x y).toReal / 2 ∧
      (riemannianEDistOf (I := I) h y m).toReal = (riemannianEDistOf (I := I) h x y).toReal / 2 := by
  let mS : MetricSpace M := @EMetricSpace.toMetricSpace M (inducedEMetricSpace h) hfin
  have : CompleteSpace M := hcomplete
  have hmetric : ∀ a b : M, riemannianEDistOf (I := I) h a b = ENNReal.ofReal (dist a b) :=
    fun a b => edist_dist a b
  obtain ⟨f, -, hf0, hf1, hfd⟩ :=
    DifferentialGeometry.Geometry.Collapse.segments_of_riemannianEDistOf_eq h hmetric x y
  have hd0 : dist (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1) ⟨1 / 2, by norm_num⟩ = 1 / 2 := by
    rw [Subtype.dist_eq, Real.dist_eq]
    norm_num
  have hd1 : dist (⟨1, by norm_num⟩ : Icc (0 : ℝ) 1) ⟨1 / 2, by norm_num⟩ = 1 / 2 := by
    rw [Subtype.dist_eq, Real.dist_eq]
    norm_num
  have h0 := hfd ⟨0, by norm_num⟩ ⟨1 / 2, by norm_num⟩
  have h1 := hfd ⟨1, by norm_num⟩ ⟨1 / 2, by norm_num⟩
  rw [hf0, hd0] at h0
  rw [hf1, hd1] at h1
  refine ⟨f ⟨1 / 2, by norm_num⟩, ?_, ?_⟩
  · change dist x (f ⟨1 / 2, by norm_num⟩) = dist x y / 2
    rw [h0]
    ring
  · change dist y (f ⟨1 / 2, by norm_num⟩) = dist x y / 2
    rw [h1]
    ring

end Step

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- **Approximate midpoints** for the length distance of a complete finite-regularity metric. -/
theorem approximate_midpoints_finite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (a b : M) (ε : ℝ) (hε : 0 < ε) :
    ∃ z : M, dist a z ≤ dist a b / 2 + ε ∧ dist b z ≤ dist a b / 2 + ε := by
  obtain ⟨gSeq, hbil, -⟩ :=
    DifferentialGeometry.Geometry.MetricSmoothing.exists_smooth_approximants_sigmaCompact g hn
  set D := dist a b with hD
  obtain ⟨k, hk⟩ := exists_nat_gt ((D + ε) / ε)
  set δ : ℝ := 1 / ((k : ℝ) + 2) with hδ
  have hδ0 : 0 < δ := (one_div_nat_add_two_mem k).1
  have hδ2 : δ ≤ 1 / 2 := (one_div_nat_add_two_mem k).2
  have hδε : δ * (D + ε) ≤ ε := by
    have hk2 : (D + ε) / ε < (k : ℝ) + 2 := by linarith
    rw [div_lt_iff₀ hε] at hk2
    rw [hδ, one_div, inv_mul_le_iff₀ (by positivity)]
    linarith
  have hpos₁ : 0 < 1 - δ := by linarith
  have hpos₂ : 0 < 1 + δ := by linarith
  obtain ⟨z, hz1, hz2⟩ := exists_midpoint_riemannianEDistOf (gSeq k)
    (riemannianEDistOf_ne_top_of_le g hnorm (gSeq k) hpos₂ fun x w => (hbil k x w).2)
    (completeSpace_inducedEMetricSpace_of_le g hnorm (gSeq k) hpos₁ fun x w => (hbil k x w).1)
    a b
  have hIcc := toReal_riemannianEDistOf_mem_Icc g hnorm (gSeq k) hδ0 (by linarith) (hbil k)
  have hab := (hIcc a b).2
  have haz := (hIcc a z).1
  have hbz := (hIcc b z).1
  have hD0 : 0 ≤ D := dist_nonneg
  refine ⟨z, ?_, ?_⟩
  · nlinarith [mul_nonneg hpos₁.le (dist_nonneg (x := a) (y := z))]
  · nlinarith [mul_nonneg hpos₁.le (dist_nonneg (x := b) (y := z))]

/-- **Isometric segments** for the length distance of a complete finite-regularity metric. -/
theorem exists_isometric_segment_finite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (x y : M) :
    ∃ σ : Icc (0 : ℝ) (dist x y) → M, Isometry σ ∧ σ ⟨0, le_rfl, dist_nonneg⟩ = x ∧
      σ ⟨dist x y, dist_nonneg, le_rfl⟩ = y := by
  obtain ⟨gSeq, hbil, -⟩ :=
    DifferentialGeometry.Geometry.MetricSmoothing.exists_smooth_approximants_sigmaCompact g hn
  have hδ := one_div_nat_add_two_mem 0
  have : ProperSpace M := properSpace_of_bilipschitz_smooth g hnorm (gSeq 0)
    (by linarith [hδ.2]) (by linarith [hδ.1]) (fun x w => (hbil 0 x w).1)
    (fun x w => (hbil 0 x w).2)
  obtain ⟨f, -, hf0, hf1, hfd⟩ := Metric.exists_metric_segment_of_approximate_midpoints
    (approximate_midpoints_finite g hn hnorm) x y
  exact Metric.exists_isometric_segment_of_dist_eq_mul hf0 hf1 hfd

/-- **Global four-point comparison** for a complete finite-regularity metric with `sec_g ≥ 0`. -/
theorem fourPointComparison_zero_univ_finite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) :
    fourPointComparison 0 (univ : Set M) := by
  intro x _ a _ b _ c _ hax hbx hcx
  have h := metricComparisonAngle_sum_le_two_pi_finite g hn hnorm hsec x a b c hax hbx hcx
  simpa only [comparisonAngleNegCurvature_zero, metricComparisonAngle] using h

/-- **Hinge comparison against the germ angle** for a complete finite-regularity metric with
`sec_g ≥ 0`, at every centre and scale. -/
theorem endpointHingeComparison_zero_finite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (p : M) (r : ℝ) : endpointHingeComparison 0 p r :=
  endpointHingeComparison_of_complete_local_comparison le_rfl
    (exists_isometric_segment_finite g hn hnorm)
    (fun z => ⟨univ, isOpen_univ, fourPointComparison_zero_univ_finite g hn hnorm hsec,
      mem_univ z⟩) p r

end DifferentialGeometry.Geometry.FiniteComparison

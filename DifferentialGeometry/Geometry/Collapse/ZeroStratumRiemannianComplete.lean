import DifferentialGeometry.Geometry.Collapse.ZeroStratumRiemannian
import DifferentialGeometry.Geometry.Collapse.CompleteRiemannianSegments
import DifferentialGeometry.Geometry.Collapse.OriginalRadialSplitting
import DifferentialGeometry.Geometry.Metric.Approximation.AnnularExactStrainerExplicit

/-!
# LC65 and LC76 on complete (possibly non-compact) Riemannian manifolds

The bindings `exists_annular_exact_scale_strainer_riemannian` (LC65) and
`exists_line_unit_ball_splitting_parameter_riemannian` (LC76) of `ZeroStratumRiemannian.lean` assume
a CLOSED manifold (`[CompactSpace M]`), while the rows (`master207A.tex`, LC65 at 23765, LC76 at
24480) are stated for a complete connected manifold. Here the same conclusions are proved with
exactly the rows' hypotheses: `g` complete (`RiemannianMetricComplete g`), `M` connected, and
`sec_g ≥ -(1/60)²` on the `g`-ball of radius `400` about `p`. Compactness was used in three places,
each replaced:

* segments: Hopf–Rinow for complete metrics (`inducedMetricSpace_segments_of_riemannianMetricComplete`,
  lane W4-F7d2);
* four-point comparison: the eight-ball theorem `fourPointComparison_of_sectional_lower_bound_on_eight_ball`
  directly, with completeness of `inducedMetricSpace g` from `riemannianMetricComplete_iff_inducedMetricSpace`;
* Hausdorff dimension: the σ-compact bound `dimH_univ_le_finrank_of_riemannian_distance` (Codex X82).

`annular_exact_scale_strainer_riemannian_explicit_of_complete` is LC65 with the blueprint's explicit
constants `δσ`, `Λσ` (for every blueprint angle `θ`), from `annular_exact_scale_strainer_explicit`.

As in the closed case, the metric kernels only consume four-point comparison on the ball of radius
`21` (LC65) or `7` (LC76), so the eight-ball theorem needs the curvature bound on radius `168`
(resp. `56`), inside the row's `400`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section Inputs

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]

/-- Four-point comparison at every curvature `-K`, `K ≥ κ`, on the `g`-ball of radius `R`, from
`sec ≥ -κ` on the `g`-ball of radius `8R`, for a complete metric `g` (no compactness). -/
theorem inducedMetricSpace_fourPointComparison_levels_of_complete
    {g : SmoothRiemannianMetric I M} (hg : RiemannianMetricComplete (I := I) g) (o : M)
    {κ R : ℝ} (hκ : 0 ≤ κ)
    (hsec : ∀ y ∈ riemannianBallOf g o (8 * R), SectionalBoundedBelowAt g y (-κ)) :
    letI := inducedMetricSpace g
    ∀ K : ℝ, κ ≤ K → fourPointComparison K (ball o R) := by
  let := inducedMetricSpace g
  have : CompleteSpace M := riemannianMetricComplete_iff_inducedMetricSpace.mp hg
  intro K hK
  apply fourPointComparison_of_sectional_lower_bound_on_eight_ball g
    (inducedMetricSpace_hmetric g) o (hκ.trans hK)
  intro y hy
  rw [inducedMetricSpace_ball g o (8 * R)] at hy
  exact (hsec y hy).mono (by linarith)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- The Hausdorff dimension of every subset of a connected σ-compact manifold, for the distance of
a smooth metric, is at most the dimension of the model (compact or not). -/
theorem dimH_le_finrank_inducedMetricSpace (g : SmoothRiemannianMetric I M) (s : Set M) :
    letI := inducedMetricSpace g
    dimH s ≤ Module.finrank ℝ E := by
  let := inducedMetricSpace g
  exact (dimH_mono (subset_univ s)).trans
    (dimH_univ_le_finrank_of_riemannian_distance g (inducedMetricSpace_hmetric g))

end Inputs

/-- **LC65 for a complete connected Riemannian manifold** (the row's setting; the closed case is
`exists_annular_exact_scale_strainer_riemannian`). Besides the metric strainer of the kernel, the
metric `λ² g` has sectional curvature at least `-σ` on its `σ⁻¹`-ball about `q`. -/
theorem exists_annular_exact_scale_strainer_riemannian_of_complete {σ : ℝ} (hσ : 0 < σ)
    (hσone : σ < 1) :
    ∃ θ δσ Λσ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 < δσ ∧ 0 < Λσ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
        [SigmaCompactSpace M] [ConnectedSpace M]
        (g : SmoothRiemannianMetric I M), RiemannianMetricComplete (I := I) g → ∀ p : M,
      (∀ y ∈ riemannianBallOf g p 400, SectionalBoundedBelowAt g y (-((1 / 60) ^ 2))) →
      letI := inducedMetricSpace g
      ∀ (C : Type v) [MetricSpace C] (o : C), RadialConeData o →
      ∀ {δ : ℝ}, KleinerLottApprox p o δ → δ < δσ →
      ∀ q : M, 1 / 10 ≤ dist p q → dist p q ≤ 10 → ∀ (lam : ℝ) (hlam : 0 < lam), Λσ ≤ lam →
      (∀ y ∈ riemannianBallOf (scaleMetric (lam ^ 2) (pow_pos hlam 2) g) q σ⁻¹,
        SectionalBoundedBelowAt (scaleMetric (lam ^ 2) (pow_pos hlam 2) g) y (-σ)) ∧
      ∃ a b z : M,
        dist q z = dist p q ∧ 2 * dist p q - dist p z < 15 * δ ∧
        Real.pi - θ <
          comparisonAngleNegCurvature ((1 / 60) ^ 2) (dist q p) (dist q z) (dist p z) ∧
        dist q a = σ⁻¹ / lam ∧ dist q b = σ⁻¹ / lam ∧
        dist q a + dist a p = dist q p ∧ dist q b + dist b z = dist q z ∧
        Real.pi - σ < comparisonAngleNegCurvature σ (lam * dist q a) (lam * dist q b)
          (lam * dist a b) := by
  obtain ⟨θ, δσ, Λσ, hθ, hθone, hδσ, hΛσ, hK⟩ := exists_annular_exact_scale_strainer.{u, v} hσ hσone
  refine ⟨θ, δσ, max Λσ σ⁻¹, hθ, hθone, hδσ, lt_max_of_lt_left hΛσ, ?_⟩
  intro M _ _ _ _ _ _ g hg p hsec
  let := inducedMetricSpace g
  intro C _ o H δ φ hδ q hq1 hq2 lam hlam hΛ
  refine ⟨?_, hK M C (inducedMetricSpace_segments_of_riemannianMetricComplete hg) p o H φ hδ ?_
    q hq1 hq2 lam ((le_max_left _ _).trans hΛ)⟩
  · intro y hy
    have hy' : y ∈ riemannianBallOf g q (σ⁻¹ / lam) := by
      have h := riemannianBallOf_scaleMetric (lam ^ 2) (pow_pos hlam 2) g q (σ⁻¹ / lam)
      rw [Real.sqrt_sq hlam.le, show lam * (σ⁻¹ / lam) = σ⁻¹ by field_simp] at h
      rwa [h] at hy
    have hs1 : σ⁻¹ / lam ≤ 1 := by
      rw [div_le_one hlam]
      exact (le_max_right _ _).trans hΛ
    have hyp : y ∈ riemannianBallOf g p 400 := by
      rw [← inducedMetricSpace_ball g] at hy' ⊢
      have h1 : dist y q < σ⁻¹ / lam := hy'
      change dist y p < 400
      linarith [dist_triangle y q p, dist_comm q p]
    have h := DifferentialGeometry.PDE.RicciFlow.sectionalBoundedBelowAt_scaleMetric
      ((hsec y hyp).mono (show -(σ * lam ^ 2) ≤ -((1 / 60) ^ 2) by
        have hσlam : 1 ≤ σ * lam := by
          have := mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hΛ) hσ.le
          rwa [mul_inv_cancel₀ hσ.ne'] at this
        nlinarith))
      (lam ^ 2) (pow_pos hlam 2)
    rwa [show -(σ * lam ^ 2) / lam ^ 2 = -σ by field_simp] at h
  · refine inducedMetricSpace_fourPointComparison_levels_of_complete hg p (by positivity) ?_ _ le_rfl
    intro y hy
    apply hsec y
    rw [← inducedMetricSpace_ball g] at hy ⊢
    exact ball_subset_ball (by norm_num) hy

/-- **LC76 for a complete connected Riemannian manifold of dimension `n`** (the row's setting; the
closed case is `exists_line_unit_ball_splitting_parameter_riemannian`). -/
theorem exists_line_unit_ball_splitting_parameter_riemannian_of_complete {β : ℝ} (hβ : 0 < β)
    (hβone : β < 1) :
    ∃ δℓ Λℓ : ℝ, 0 < δℓ ∧ 0 < Λℓ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
        [SigmaCompactSpace M] [ConnectedSpace M]
        (g : SmoothRiemannianMetric I M), RiemannianMetricComplete (I := I) g → ∀ p : M,
      (∀ y ∈ riemannianBallOf g p 400, SectionalBoundedBelowAt g y (-((1 / 60) ^ 2))) →
      letI m := inducedMetricSpace g
      ∀ {δ o : ℝ}, KleinerLottApprox p o δ → δ < δℓ →
      ∀ q ∈ ball p 1, ∀ (lam : ℝ) (hlam : 0 < lam), Λℓ ≤ lam →
        @HasEuclideanSplitting.{u, 0} M (m.rescale lam hlam) q 1 β := by
  obtain ⟨δℓ, Λℓ, hδℓ, hΛℓ, hK⟩ := exists_line_unit_ball_splitting_parameter.{u}
    (n := Module.finrank ℝ E) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)) hβ hβone
  refine ⟨δℓ, Λℓ, hδℓ, hΛℓ, ?_⟩
  intro M _ _ _ _ _ _ g hg p hsec
  let m := inducedMetricSpace g
  have : CompleteSpace M := riemannianMetricComplete_iff_inducedMetricSpace.mp hg
  have hsec' : ∀ y ∈ riemannianBallOf g p (8 * 7), SectionalBoundedBelowAt g y (-((1 / 60) ^ 2)) := by
    intro y hy
    apply hsec y
    have hsub : riemannianBallOf g p (8 * 7) ⊆ riemannianBallOf g p 400 := by
      rw [← inducedMetricSpace_ball g, ← inducedMetricSpace_ball g]
      exact ball_subset_ball (by norm_num)
    exact hsub hy
  intro δ o
  exact hK M (inducedMetricSpace_segments_of_riemannianMetricComplete hg)
    p (dimH_le_finrank_inducedMetricSpace g _)
    (inducedMetricSpace_fourPointComparison_levels_of_complete hg p (by positivity) hsec' _ le_rfl)

/-- **LC65 for a complete connected Riemannian manifold, with the blueprint's explicit constants.**
For `0 < σ < 1` and every angle `0 < θ < π/2` with `2 σ⁻¹ cos(θ/2) > c_σ`, the constants are
`δσ = min {a/60, 1/(4b+20), a(1 - cos θ)/60}` and `Λσ = max {2σ⁻¹/a, (1/60)/√σ, 2}`
(`a = 1/10`, `b = 10`), written literally. -/
theorem annular_exact_scale_strainer_riemannian_explicit_of_complete {σ θ : ℝ} (hσ : 0 < σ)
    (hσone : σ < 1) (hθ : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hθside : annularStrainerSide σ < 2 * σ⁻¹ * Real.cos (θ / 2))
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
    [SigmaCompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} (hg : RiemannianMetricComplete (I := I) g) (p : M)
    (hsec : ∀ y ∈ riemannianBallOf g p 400, SectionalBoundedBelowAt g y (-((1 / 60) ^ 2)))
    {C : Type*} [MetricSpace C] (o : C) (H : RadialConeData o) :
    letI := inducedMetricSpace g
    ∀ {δ : ℝ}, KleinerLottApprox p o δ →
      δ < min ((1 / 10) / 60) (min (1 / (4 * 10 + 20)) ((1 / 10) * (1 - Real.cos θ) / 60)) →
      ∀ q : M, 1 / 10 ≤ dist p q → dist p q ≤ 10 → ∀ (lam : ℝ) (hlam : 0 < lam),
      max (2 * σ⁻¹ / (1 / 10)) (max ((1 / 60) / Real.sqrt σ) 2) ≤ lam →
      (∀ y ∈ riemannianBallOf (scaleMetric (lam ^ 2) (pow_pos hlam 2) g) q σ⁻¹,
        SectionalBoundedBelowAt (scaleMetric (lam ^ 2) (pow_pos hlam 2) g) y (-σ)) ∧
      ∃ a b z : M,
        dist q z = dist p q ∧ 2 * dist p q - dist p z < 15 * δ ∧
        Real.pi - θ <
          comparisonAngleNegCurvature ((1 / 60) ^ 2) (dist q p) (dist q z) (dist p z) ∧
        dist q a = σ⁻¹ / lam ∧ dist q b = σ⁻¹ / lam ∧
        dist q a + dist a p = dist q p ∧ dist q b + dist b z = dist q z ∧
        Real.pi - σ < comparisonAngleNegCurvature σ (lam * dist q a) (lam * dist q b)
          (lam * dist a b) := by
  let := inducedMetricSpace g
  intro δ φ hδ q hq1 hq2 lam hlam hΛ
  have hσinv : σ⁻¹ ≤ lam := by
    have h := (le_max_left _ _).trans hΛ
    have hpos : 0 ≤ σ⁻¹ := (inv_pos.mpr hσ).le
    have he : 2 * σ⁻¹ / (1 / 10) = 20 * σ⁻¹ := by ring
    rw [he] at h
    linarith
  refine ⟨?_, annular_exact_scale_strainer_explicit hσ hσone hθ hθpi hθside
    (inducedMetricSpace_segments_of_riemannianMetricComplete hg) p o H φ hδ ?_ q hq1 hq2 lam hΛ⟩
  · intro y hy
    have hy' : y ∈ riemannianBallOf g q (σ⁻¹ / lam) := by
      have h := riemannianBallOf_scaleMetric (lam ^ 2) (pow_pos hlam 2) g q (σ⁻¹ / lam)
      rw [Real.sqrt_sq hlam.le, show lam * (σ⁻¹ / lam) = σ⁻¹ by field_simp] at h
      rwa [h] at hy
    have hs1 : σ⁻¹ / lam ≤ 1 := by
      rw [div_le_one hlam]
      exact hσinv
    have hyp : y ∈ riemannianBallOf g p 400 := by
      rw [← inducedMetricSpace_ball g] at hy' ⊢
      have h1 : dist y q < σ⁻¹ / lam := hy'
      change dist y p < 400
      linarith [dist_triangle y q p, dist_comm q p]
    have hσlam : 1 ≤ σ * lam := by
      have := mul_le_mul_of_nonneg_left hσinv hσ.le
      rwa [mul_inv_cancel₀ hσ.ne'] at this
    have h := DifferentialGeometry.PDE.RicciFlow.sectionalBoundedBelowAt_scaleMetric
      ((hsec y hyp).mono (show -(σ * lam ^ 2) ≤ -((1 / 60) ^ 2) by nlinarith))
      (lam ^ 2) (pow_pos hlam 2)
    rwa [show -(σ * lam ^ 2) / lam ^ 2 = -σ by field_simp] at h
  · refine inducedMetricSpace_fourPointComparison_levels_of_complete hg p (by positivity) ?_ _ le_rfl
    intro y hy
    apply hsec y
    rw [← inducedMetricSpace_ball g] at hy ⊢
    exact ball_subset_ball (by norm_num) hy

end DifferentialGeometry.Geometry.Collapse

import DifferentialGeometry.Geometry.Metric.Approximation.SelectedModelOneEnd
import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianHausdorffDimension
import DifferentialGeometry.Geometry.Comparison.RiemannianFourPointApplications
import DifferentialGeometry.Geometry.Metric.RiemannianShortCurves
import DifferentialGeometry.Topology.MetricSpace.GeodesicMidpoint
import DifferentialGeometry.Topology.MetricSpace.CurveMidpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LocalAllOrdersScaled

/-!
# Riemannian bindings of LC65, LC66, LC76 and LC77 on a closed manifold

The metric kernels of `Geometry/Metric/Approximation/{AnnularExactStrainer, LineUnitBallSplitting,
ZeroStratumSmallCoreCover, SelectedModelOneEnd}.lean` applied to the distance of a smooth metric
`g` on a compact connected manifold (`inducedMetricSpace g`). Their metric hypotheses are
discharged from the Riemannian ones:

* segments: Hopf–Rinow minimizing curves (`exists_arbitrarily_short_riemannian_curve`) and
  properness of the compact space (`exists_metric_segment_of_approximate_midpoints`);
* Hausdorff dimension: `dimH_univ_le_finrank_inducedMetricSpace` (A3's volume identity);
* four-point comparison at every curvature `-K` with `K` above the sectional bound, on a ball
  of radius `R`, from `sec ≥ -κ` on the ball of radius `8R`
  (`fourPointComparison_of_sectional_lower_bound_on_compact_induced_ball`, then
  `SectionalBoundedBelowAt.mono`).

The rescaled distances `ρ(q)⁻¹ d_g` and `r(i)⁻¹ d_g` are the metric-scaling identification of
the distances of `ρ(q)⁻² g` and `r(i)⁻² g` used in LC16. The constants depend only on `β₁`
(and `σ`) and on the model `(E, H, I)`, uniformly over all manifolds and metrics.
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

universe u v w

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section Inputs

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
  [SigmaCompactSpace M] [ConnectedSpace M] [CompactSpace M]

/-- Minimizing segments for the distance of `g` on a compact connected manifold. -/
theorem inducedMetricSpace_segments (g : SmoothRiemannianMetric I M) :
    letI := inducedMetricSpace g
    ∀ x y : M, ∃ f : Icc (0 : ℝ) 1 → M,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let := inducedMetricSpace g
  have : ProperSpace M := inducedMetricSpace_properSpace g
  have : CompleteSpace M := inducedMetricSpace_completeSpace g
  intro x y
  exact Metric.exists_metric_segment_of_approximate_midpoints
    (Metric.approximate_midpoints_of_arbitrarily_short_curves
      (fun a b η hη => DifferentialGeometry.Geometry.Metric.exists_arbitrarily_short_riemannian_curve
        g (inducedMetricSpace_hmetric g) a b hη)) x y

/-- Four-point comparison at every curvature `-K`, `K ≥ κ`, on the `g`-ball of radius `R`, from
`sec ≥ -κ` on the `g`-ball of radius `8R`. -/
theorem inducedMetricSpace_fourPointComparison_levels (g : SmoothRiemannianMetric I M) (o : M)
    {κ R : ℝ} (hκ : 0 ≤ κ)
    (hsec : ∀ y ∈ riemannianBallOf g o (8 * R), SectionalBoundedBelowAt g y (-κ)) :
    letI := inducedMetricSpace g
    ∀ K : ℝ, κ ≤ K → fourPointComparison K (ball o R) := by
  intro K hK
  rw [inducedMetricSpace_ball g o R]
  exact fourPointComparison_of_sectional_lower_bound_on_compact_induced_ball g o
    (hκ.trans hK) (fun y hy => (hsec y hy).mono (by linarith))

end Inputs

/-- **LC66 for a closed connected Riemannian three-manifold.** With `g_i = r(i)⁻² g`, the LC65
data at a selected center are `sec_{g_i} ≥ -(1/60)²` on `B_{g_i}(i, 400)`, i.e.
`sec_g ≥ -(1/60)² r(i)⁻²` on `B_g(i, 400 r(i))`, and an actual Kleiner–Lott map from
`(M, r(i)⁻¹ d_g, i)` to a cone with `RadialConeData`. -/
theorem exists_zero_stratum_small_core_cover_riemannian (hE : Module.finrank ℝ E = 3)
    {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) :
    ∃ δ' Λ' : ℝ, 0 < δ' ∧ 0 < Λ' ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
        [SigmaCompactSpace M] [ConnectedSpace M] [CompactSpace M]
        (g : SmoothRiemannianMetric I M),
      letI m := inducedMetricSpace g
      ∀ (r ρ : M → ℝ), Continuous ρ → ∀ (hρpos : ∀ p, 0 < ρ p) {T U : ℝ} (hT : 0 < T),
      20 * Λ' ≤ T → T ≤ U → ∀ (hlower : ∀ p, T * ρ p ≤ r p), (∀ p, r p ≤ U * ρ p) →
      ∃ J : Set M, J.Finite ∧
        (∀ i ∈ J, (ball i (r i) ∩
            {q | @splittingRank.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0}
          ).Nonempty ∧
          ∀ q, (ball q (r q) ∩ {q | @splittingRank.{u, 0} M
              (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0}).Nonempty →
            ball i (r i) ⊆ ball q (r q) → r q ≤ 2 * r i) ∧
        J.PairwiseDisjoint (fun i => ball i (r i)) ∧
        (∀ i ∈ J, ∀ q, dist i q ≤ 10 * r i → r q ≤ 20 * r i ∧ T / 20 ≤ r i / ρ q) ∧
        {q | @splittingRank.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0} ⊆
          ⋃ i ∈ J, ball i (5 * r i) ∧
        ((∀ i ∈ J, (∀ y ∈ riemannianBallOf g i (400 * r i),
              SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * (r i)⁻¹ ^ 2))) ∧
            ∃ (C : Type v) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧ ∃ δ : ℝ,
              δ < δ' ∧ Nonempty (@KleinerLottApprox M C
                (m.rescale (r i)⁻¹ (inv_pos.mpr ((mul_pos hT (hρpos i)).trans_le (hlower i))))
                mC i o δ)) →
          (∀ i ∈ J, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
            @HasEuclideanSplitting.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q 1 (β 1) ∧
            @splittingRank.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 ≠ 0) ∧
          {q | @splittingRank.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0} ⊆
            ⋃ i ∈ J, ball i (r i / 10)) := by
  obtain ⟨δ', Λ', hδ', hΛ', hK⟩ := exists_zero_stratum_small_core_cover.{u, v} hβ hβone
  refine ⟨δ', Λ', hδ', hΛ', ?_⟩
  intro M _ _ _ _ _ _ _ g
  let m := inducedMetricSpace g
  intro r ρ hρ hρpos T U hT hTΛ hTU hlower hupper
  have hdim : dimH (univ : Set M) ≤ 3 := by
    have h := DifferentialGeometry.Geometry.Metric.dimH_univ_le_finrank_inducedMetricSpace g
    rw [hE] at h
    exact_mod_cast h
  obtain ⟨J, hfin, hmax, hdisj, hloc, hcov, hcond⟩ :=
    hK M (inducedMetricSpace_segments g) hdim r ρ hρ hρpos hT hTΛ hTU hlower hupper
  refine ⟨J, hfin, hmax, hdisj, hloc, hcov, fun hdata => hcond fun i hi => ⟨?_, (hdata i hi).2⟩⟩
  have hri : 0 < r i := (mul_pos hT (hρpos i)).trans_le (hlower i)
  refine inducedMetricSpace_fourPointComparison_levels g i (by positivity) ?_ _ le_rfl
  intro y hy
  apply (hdata i hi).1 y
  have hsub : riemannianBallOf g i (8 * (21 * r i)) ⊆ riemannianBallOf g i (400 * r i) := by
    rw [← inducedMetricSpace_ball g, ← inducedMetricSpace_ball g]
    exact ball_subset_ball (by nlinarith)
  exact hsub hy

/-- **LC76 for a closed connected Riemannian manifold of dimension `n`.** -/
theorem exists_line_unit_ball_splitting_parameter_riemannian {β : ℝ} (hβ : 0 < β)
    (hβone : β < 1) :
    ∃ δℓ Λℓ : ℝ, 0 < δℓ ∧ 0 < Λℓ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
        [SigmaCompactSpace M] [ConnectedSpace M] [CompactSpace M]
        (g : SmoothRiemannianMetric I M) (p : M),
      (∀ y ∈ riemannianBallOf g p 400, SectionalBoundedBelowAt g y (-((1 / 60) ^ 2))) →
      letI m := inducedMetricSpace g
      ∀ {δ o : ℝ}, KleinerLottApprox p o δ → δ < δℓ →
      ∀ q ∈ ball p 1, ∀ (lam : ℝ) (hlam : 0 < lam), Λℓ ≤ lam →
        @HasEuclideanSplitting.{u, 0} M (m.rescale lam hlam) q 1 β := by
  obtain ⟨δℓ, Λℓ, hδℓ, hΛℓ, hK⟩ := exists_line_unit_ball_splitting_parameter.{u}
    (n := Module.finrank ℝ E) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)) hβ hβone
  refine ⟨δℓ, Λℓ, hδℓ, hΛℓ, ?_⟩
  intro M _ _ _ _ _ _ _ g p hsec
  let m := inducedMetricSpace g
  have : CompleteSpace M := inducedMetricSpace_completeSpace g
  have hsec' : ∀ y ∈ riemannianBallOf g p (8 * 7), SectionalBoundedBelowAt g y (-((1 / 60) ^ 2)) := by
    intro y hy
    apply hsec y
    have hsub : riemannianBallOf g p (8 * 7) ⊆ riemannianBallOf g p 400 := by
      rw [← inducedMetricSpace_ball g, ← inducedMetricSpace_ball g]
      exact ball_subset_ball (by norm_num)
    exact hsub hy
  intro δ o
  exact hK M (inducedMetricSpace_segments g)
    p ((dimH_mono (subset_univ _)).trans
      (DifferentialGeometry.Geometry.Metric.dimH_univ_le_finrank_inducedMetricSpace g))
    (inducedMetricSpace_fourPointComparison_levels g p (by positivity) hsec' _ le_rfl)

/-- **LC77 for a closed connected Riemannian three-manifold, one selected center.** The LC76
data at scale `r_i` are `sec_g ≥ -(1/60)² r_i⁻²` on `B_g(i, 400 r_i)`. -/
theorem exists_selected_model_one_end_parameter_riemannian (hE : Module.finrank ℝ E = 3)
    {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) :
    ∃ δℓ Λℓ : ℝ, 0 < δℓ ∧ 0 < Λℓ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
        [SigmaCompactSpace M] [ConnectedSpace M] [CompactSpace M]
        (g : SmoothRiemannianMetric I M),
      letI m := inducedMetricSpace g
      ∀ (ρ : M → ℝ) (hρpos : ∀ p, 0 < ρ p) (i : M) {ri : ℝ} (hri : 0 < ri),
      (∀ y ∈ riemannianBallOf g i (400 * ri),
        SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * ri⁻¹ ^ 2))) →
      (∀ q, dist i q < ri → Λℓ ≤ ri / ρ q) →
      (ball i ri ∩ {q | @splittingRank.{u, 0} M
          (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0}).Nonempty →
      ∀ (N : Type w) [mN : MetricSpace N] [ProperSpace N] (n₀ : N)
        (C : Type v) [MetricSpace C] [ProperSpace C] (o : C),
      fourPointComparison 0 (univ : Set N) →
      (∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N,
        Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (f s) (f t) = dist x y * dist s t) →
      (∀ δ : ℝ, 0 < δ → δ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ,
        R₀ ≤ R → ∀ hR : 0 < R, Nonempty (@KleinerLottApprox N C
          (mN.rescale R⁻¹ (inv_pos.mpr hR)) _ n₀ o δ)) →
      ∀ {δ : ℝ}, δ < δℓ →
      Nonempty (@KleinerLottApprox M C (m.rescale ri⁻¹ (inv_pos.mpr hri)) _ i o δ) →
      ∀ K : Set N, IsCompact K → ∀ a b : N,
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
        connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b := by
  obtain ⟨δℓ, Λℓ, hδℓ, hΛℓ, hK⟩ := exists_selected_model_one_end_parameter.{u, v, w} hβ hβone
  refine ⟨δℓ, Λℓ, hδℓ, hΛℓ, ?_⟩
  intro M _ _ _ _ _ _ _ g
  let m := inducedMetricSpace g
  have : CompleteSpace M := inducedMetricSpace_completeSpace g
  intro ρ hρpos i ri hri hsec
  have hdim : dimH (ball i (2 * ri)) ≤ 3 := by
    have h := DifferentialGeometry.Geometry.Metric.dimH_univ_le_finrank_inducedMetricSpace g
    rw [hE] at h
    exact (dimH_mono (subset_univ _)).trans (by exact_mod_cast h)
  refine hK M (inducedMetricSpace_segments g) ρ hρpos i hri hdim
    (inducedMetricSpace_fourPointComparison_levels g i (by positivity) ?_ _ le_rfl)
  intro y hy
  apply hsec y
  have hsub : riemannianBallOf g i (8 * (21 * ri)) ⊆ riemannianBallOf g i (400 * ri) := by
    rw [← inducedMetricSpace_ball g, ← inducedMetricSpace_ball g]
    exact ball_subset_ball (by nlinarith)
  exact hsub hy

/-- **LC65 for a closed connected Riemannian manifold.** Besides the metric strainer of the
kernel, the metric `λ² g` has sectional curvature at least `-σ` on its `σ⁻¹`-ball about `q`. -/
theorem exists_annular_exact_scale_strainer_riemannian {σ : ℝ} (hσ : 0 < σ) (hσone : σ < 1) :
    ∃ θ δσ Λσ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 < δσ ∧ 0 < Λσ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
        [SigmaCompactSpace M] [ConnectedSpace M] [CompactSpace M]
        (g : SmoothRiemannianMetric I M) (p : M),
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
  intro M _ _ _ _ _ _ _ g p hsec
  let := inducedMetricSpace g
  intro C _ o H δ φ hδ q hq1 hq2 lam hlam hΛ
  refine ⟨?_, hK M C (inducedMetricSpace_segments g) p o H φ hδ ?_ q hq1 hq2 lam
    ((le_max_left _ _).trans hΛ)⟩
  · intro y hy
    have hσlam : 1 ≤ σ * lam := by
      have := mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hΛ) hσ.le
      rwa [mul_inv_cancel₀ hσ.ne'] at this
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
      ((hsec y hyp).mono (show -(σ * lam ^ 2) ≤ -((1 / 60) ^ 2) by nlinarith))
      (lam ^ 2) (pow_pos hlam 2)
    rwa [show -(σ * lam ^ 2) / lam ^ 2 = -σ by field_simp] at h
  · rw [inducedMetricSpace_ball g p 21]
    apply fourPointComparison_of_sectional_lower_bound_on_compact_induced_ball g p (by positivity)
    intro y hy
    apply hsec y
    rw [← inducedMetricSpace_ball g] at hy ⊢
    exact ball_subset_ball (by norm_num) hy

end DifferentialGeometry.Geometry.Collapse

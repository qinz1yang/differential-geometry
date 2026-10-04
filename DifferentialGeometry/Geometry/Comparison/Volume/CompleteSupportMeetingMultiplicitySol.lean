import DifferentialGeometry.Geometry.Comparison.Volume.ScaledBallComparison
import DifferentialGeometry.Geometry.Metric.SupportComparisonLists
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.LocalToGlobal
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison.X81Sol

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [SigmaCompactSpace M] [CompleteSpace M]

open _root_.Metric DifferentialGeometry.Integral.Measure

theorem ncard_supports_meeting_ball_le_of_complete_ricci_bound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {ι : Type*} (J : Finset ι) (c : ι → M) (S : ι → Set M) {ρ : M → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {R C a q : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (ha : 0 < a) (hq : 0 ≤ q) (hbudget : Λ * max R C ≤ 1 / 4)
    (hS : ∀ j ∈ J, S j ⊆ closedBall (c j) (C * ρ (c j)))
    (hdisj : (J : Set ι).PairwiseDisjoint fun j => ball (c j) (a * ρ (c j))) (p : M)
    (hRic : ∀ j ∈ J, (S j ∩ ball p (R * ρ p)).Nonempty → ricciBoundedBelowOn (I := I) g
      (ball (c j) (4 * (R + 2 * C + a) * ρ (c j)))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((q / ρ (c j)) ^ 2)))) :
    ({j | j ∈ J ∧ (S j ∩ ball p (R * ρ p)).Nonempty}.ncard : ℝ) ≤
      modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (4 * (R + 2 * C + a)) /
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) a := by
  let : Nonempty M := ⟨p⟩
  let : ConnectedSpace M := DifferentialGeometry.Geometry.Collapse.connectedSpace_of_riemannian g hEnorm
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasureOnCompacts μ := riemannianVolumeMeasure_isFiniteMeasureOnCompacts g
  let : T3Space M := inferInstance
  have hc : @CompleteSpace M (EMetricSpace.ofRiemannianMetric I M).toUniformSpace := by
    have he : (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace =
        (inferInstance : PseudoEMetricSpace M) := by
      apply PseudoEMetricSpace.ext
      ext x y
      exact (IsRiemannianManifold.out (I := I) x y).symm
    rw [he]
    infer_instance
  have hm : HopfRinow.riemMetricSpace (I := I) (M := M) = (inferInstance : MetricSpace M) := by
    apply MetricSpace.ext
    ext x y
    rw [HopfRinow.riemMetric_dist_eq, ← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  have hproper := HopfRinow.properSpace_riemMetric (I := I) hc g hEnorm
  rw [hm] at hproper
  let : ProperSpace M := hproper
  have hfinite (x : M) (r : ℝ) : μ (ball x r) ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top (isCompact_closedBall x r).measure_lt_top.ne
      (measure_mono ball_subset_closedBall)
  let : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  let D := 4 * (R + 2 * C + a)
  have haD : a ≤ D := by dsimp only [D]; linarith
  have hn : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hm (t : ℝ) (ht : 0 < t) : 0 < modelVolume (-(q ^ 2)) (Module.finrank ℝ E) t :=
    modelVolume_pos hn ht ⟨ht.le, fun h => (not_lt_of_ge (neg_nonpos.mpr (sq_nonneg _)) h).elim⟩
  have hball (x : M) (r : ℝ) :
      {y : M | riemannianEDist I x y < ENNReal.ofReal r} = ball x r := by
    ext y
    rw [mem_ofPred_eq, ← IsRiemannianManifold.out (I := I), edist_lt_ofReal]
    exact dist_comm x y ▸ Iff.rfl
  apply GC.MetricGeometry.card_supports_meeting_ball_le μ J c S hρ hρpos hR hC ha.le
    (div_nonneg (hm D (ha.trans_le haD)).le (hm a ha).le) hbudget hS hdisj p
  · intro j _ _
    exact ENNReal.toReal_pos (measure_ball_pos μ (c j) (mul_pos ha (hρpos (c j)))).ne'
      (hfinite _ _)
  · intro j _ _
    exact hfinite _ _
  · intro j hj hmeet
    have hric := hRic j hj hmeet
    rw [← hball (c j) (D * ρ (c j))] at hric
    have hcmp := ballVolume_mul_scale_le_model_ratio g hEnorm (c j) hq (hρpos (c j)) ha haD hric
    have hv (r : ℝ) : ballVolume g (c j) r = μ (ball (c j) r) := by
      simp only [ballVolume, μ, hball]
    rw [hv, hv] at hcmp
    have hcmp' := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite _ _)) hcmp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (div_nonneg (hm D (ha.trans_le haD)).le (hm a ha).le)] at hcmp'
    simpa only [D, Measure.real] using hcmp'



theorem ncard_supports_meeting_ball_le_of_complete_scaled_ricci_bound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {ι : Type*} (J : Finset ι) (c : ι → M) (S : ι → Set M) {ρ : M → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {Δ R C a q : ℝ} (hΔ : 0 < Δ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (ha : 0 < a) (hq : 0 ≤ q)
    (hbudget : Λ * max (R * Δ) (C * Δ) ≤ 1 / 4)
    (hS : ∀ j ∈ J, S j ⊆ closedBall (c j) (C * Δ * ρ (c j)))
    (hdisj : (J : Set ι).PairwiseDisjoint fun j => ball (c j) (a * Δ * ρ (c j))) (p : M)
    (hRic : ∀ j ∈ J, (S j ∩ ball p (R * Δ * ρ p)).Nonempty → ricciBoundedBelowOn (I := I) g
      (ball (c j) (4 * (R + 2 * C + a) * Δ * ρ (c j)))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((q / (Δ * ρ (c j))) ^ 2)))) :
    ({j | j ∈ J ∧ (S j ∩ ball p (R * Δ * ρ p)).Nonempty}.ncard : ℝ) ≤
      modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (4 * (R + 2 * C + a)) /
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) a := by
  have hn : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have h := ncard_supports_meeting_ball_le_of_complete_ricci_bound g hEnorm J c S hρ hρpos
    (R := R * Δ) (C := C * Δ) (a := a * Δ) (q := q / Δ) (by positivity) (by positivity)
    (by positivity) (div_nonneg hq hΔ.le) hbudget hS hdisj p (by
      intro j hj hmeet
      have hr := hRic j hj hmeet
      have h1 : 4 * (R * Δ + 2 * (C * Δ) + a * Δ) * ρ (c j) =
          4 * (R + 2 * C + a) * Δ * ρ (c j) := by ring
      have h2 : q / Δ / ρ (c j) = q / (Δ * ρ (c j)) := by rw [div_div]
      rw [h1, h2]
      exact hr)
  have h1 : 4 * (R * Δ + 2 * (C * Δ) + a * Δ) = Δ * (4 * (R + 2 * C + a)) := by ring
  rw [h1, mul_comm a Δ, modelVolume_neg_sq_scale q Δ _ _ hq hΔ hn,
    modelVolume_neg_sq_scale q Δ _ _ hq hΔ hn,
    mul_div_mul_left _ _ (pow_ne_zero _ hΔ.ne')] at h
  exact h



theorem complete_edge_comparison_list_card_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {ιe ιs : Type*} (Je : Finset ιe) (Js : Finset ιs) (ce : ιe → M) (cs : ιs → M)
    (Se : ιe → Set M) (Ss : ιs → Set M) {ρ : M → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {Δ : ℝ} (hΔ : 1 ≤ Δ)
    (hΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hSe : ∀ j ∈ Je, Se j ⊆ closedBall (ce j) (15 * Δ * ρ (ce j)))
    (hSs : ∀ j ∈ Js, Ss j ⊆ closedBall (cs j) (901002 * Δ * ρ (cs j)))
    (hdisje : (Je : Set ιe).PairwiseDisjoint fun j => ball (ce j) (Δ * ρ (ce j) / 3))
    (hdisjs : (Js : Set ιs).PairwiseDisjoint fun j => ball (cs j) (Δ * ρ (cs j) / 3)) (p : M)
    (hRice : ∀ j ∈ Je, (Se j ∩ ball p (20 * Δ * ρ p)).Nonempty → ricciBoundedBelowOn (I := I) g
      (ball (ce j) (4 * (20 + 2 * 15 + 1 / 3) * Δ * ρ (ce j)))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((1 / (Δ * ρ (ce j))) ^ 2))))
    (hRics : ∀ j ∈ Js, (Ss j ∩ ball p (20 * Δ * ρ p)).Nonempty → ricciBoundedBelowOn (I := I) g
      (ball (cs j) (4 * (20 + 2 * 901002 + 1 / 3) * Δ * ρ (cs j)))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((1 / (Δ * ρ (cs j))) ^ 2)))) :
    ({j | j ∈ Je ∧ (Se j ∩ ball p (20 * Δ * ρ p)).Nonempty}.ncard : ℝ) +
        {j | j ∈ Js ∧ (Ss j ∩ ball p (20 * Δ * ρ p)).Nonempty}.ncard ≤
      modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (4 * (20 + 2 * 15 + 1 / 3)) /
          modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (1 / 3) +
        modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (4 * (20 + 2 * 901002 + 1 / 3)) /
          modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (1 / 3) := by
  have hΛ0 := NNReal.coe_nonneg Λ
  have hcore (x : M) : 1 / 3 * Δ * ρ x = Δ * ρ x / 3 := by ring
  have hbudget (C : ℝ) (hC0 : 0 ≤ C) (hC : C ≤ 901002) : (Λ : ℝ) * max (20 * Δ) (C * Δ) ≤ 1 / 4 := by
    apply (mul_le_mul_of_nonneg_left (max_le (show 20 * Δ ≤ 1000000 * Δ by nlinarith)
      (show C * Δ ≤ 1000000 * Δ by nlinarith)) hΛ0).trans
    nlinarith
  have he := ncard_supports_meeting_ball_le_of_complete_scaled_ricci_bound g hEnorm Je ce Se hρ hρpos
    (R := 20) (C := 15) (a := 1 / 3) (q := 1) (by linarith) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (hbudget 15 (by norm_num) (by norm_num)) hSe
    (by simpa only [hcore] using hdisje) p hRice
  have hs := ncard_supports_meeting_ball_le_of_complete_scaled_ricci_bound g hEnorm Js cs Ss hρ hρpos
    (R := 20) (C := 901002) (a := 1 / 3) (q := 1) (by linarith) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (hbudget 901002 (by norm_num) (by norm_num)) hSs
    (by simpa only [hcore] using hdisjs) p hRics
  exact add_le_add he hs


private theorem negative_modelVolume_mono_radius {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (n : ℕ) :
    modelVolume (-(1 ^ 2)) n r ≤ modelVolume (-(1 ^ 2)) n t := by
  unfold modelVolume
  apply intervalIntegral.integral_mono_interval le_rfl hr hrt
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    unfold modelArea
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (euclideanUnitBallVolume_pos n).le)
      (pow_nonneg (modelRadius_nonneg hx.1.le ⟨hx.1.le, by norm_num⟩) _)
  · exact (modelArea_continuous _ n).intervalIntegrable _ _

theorem complete_fixed_test_ball_scaled_card_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {ι : Type*} (J : Finset ι) (c : ι → M) (S : ι → Set M)
    {ρ : M → ℝ} {Λ : NNReal} (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x)
    {Δ C : ℝ} (hΔ : 1 ≤ Δ) (hC : 0 ≤ C)
    (hbudget : (Λ : ℝ) * max 10 (C * Δ) ≤ 1 / 4)
    (hS : ∀ j ∈ J, S j ⊆ closedBall (c j) (C * Δ * ρ (c j)))
    (hdisj : (J : Set ι).PairwiseDisjoint fun j => ball (c j) (Δ * ρ (c j) / 3)) (p : M)
    (hRic : ∀ j ∈ J, (S j ∩ ball p (10 * ρ p)).Nonempty → ricciBoundedBelowOn (I := I) g
      (ball (c j) (4 * (10 + 2 * (C * Δ) + Δ / 3) * ρ (c j)))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((1 / (Δ * ρ (c j))) ^ 2)))) :
    ({j | j ∈ J ∧ (S j ∩ ball p (10 * ρ p)).Nonempty}.ncard : ℝ) ≤
      modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (4 * (10 + 2 * C + 1 / 3)) /
        modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (1 / 3) := by
  have hΔpos : 0 < Δ := by linarith
  have hcancel : 10 / Δ * Δ = 10 := div_mul_cancel₀ _ hΔpos.ne'
  have hcore (x : M) : 1 / 3 * Δ * ρ x = Δ * ρ x / 3 := by ring
  have h := ncard_supports_meeting_ball_le_of_complete_scaled_ricci_bound g hEnorm J c S hρ hρpos
    (R := 10 / Δ) (C := C) (a := 1 / 3) (q := 1) hΔpos (by positivity) hC
    (by norm_num) (by norm_num) (by simpa only [hcancel] using hbudget) hS
    (by simpa only [hcore] using hdisj) p (by
      intro j hj hmeet
      have hH : 4 * (10 / Δ + 2 * C + 1 / 3) * Δ * ρ (c j) =
          4 * (10 + 2 * (C * Δ) + Δ / 3) * ρ (c j) := by
        field_simp
      rw [hH]
      exact hRic j hj (by simpa only [hcancel] using hmeet))
  simp only [hcancel] at h
  have hr : 0 ≤ 4 * (10 / Δ + 2 * C + 1 / 3) := by positivity
  have hrt : 4 * (10 / Δ + 2 * C + 1 / 3) ≤ 4 * (10 + 2 * C + 1 / 3) := by
    have hd : 10 / Δ ≤ (10 : ℝ) := (div_le_iff₀ hΔpos).mpr (by nlinarith)
    linarith
  have hn : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hden : 0 < modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (1 / 3) :=
    modelVolume_pos hn (by norm_num) ⟨by norm_num, by norm_num⟩
  exact h.trans (div_le_div_of_nonneg_right (negative_modelVolume_mono_radius hr hrt _) hden.le)

theorem complete_blueprint_comparison_list_card_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {ιe ιs : Type*} (Je : Finset ιe) (Js : Finset ιs) (ce : ιe → M) (cs : ιs → M)
    (Se : ιe → Set M) (Ss : ιs → Set M) {ρ : M → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {Δ : ℝ} (hΔ : 1 ≤ Δ)
    (hΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hSe : ∀ j ∈ Je, Se j ⊆ closedBall (ce j) (100 * Δ * ρ (ce j)))
    (hSs : ∀ j ∈ Js, Ss j ⊆ closedBall (cs j) (1000000 * Δ * ρ (cs j)))
    (hdisje : (Je : Set ιe).PairwiseDisjoint fun j => ball (ce j) (Δ * ρ (ce j) / 3))
    (hdisjs : (Js : Set ιs).PairwiseDisjoint fun j => ball (cs j) (Δ * ρ (cs j) / 3)) (p : M)
    (hRice : ∀ j ∈ Je, (Se j ∩ ball p (10 * ρ p)).Nonempty → ricciBoundedBelowOn (I := I) g
      (ball (ce j) (4 * (10 + 2 * (100 * Δ) + Δ / 3) * ρ (ce j)))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((1 / (Δ * ρ (ce j))) ^ 2))))
    (hRics : ∀ j ∈ Js, (Ss j ∩ ball p (10 * ρ p)).Nonempty → ricciBoundedBelowOn (I := I) g
      (ball (cs j) (4 * (10 + 2 * (1000000 * Δ) + Δ / 3) * ρ (cs j)))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((1 / (Δ * ρ (cs j))) ^ 2)))) :
    ({j | j ∈ Je ∧ (Se j ∩ ball p (10 * ρ p)).Nonempty}.ncard : ℝ) +
        {j | j ∈ Js ∧ (Ss j ∩ ball p (10 * ρ p)).Nonempty}.ncard ≤
      modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (4 * (10 + 2 * 100 + 1 / 3)) /
          modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (1 / 3) +
        modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (4 * (10 + 2 * 1000000 + 1 / 3)) /
          modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (1 / 3) := by
  have hΛ0 := NNReal.coe_nonneg Λ
  have hbudget (C : ℝ) (hC0 : 0 ≤ C) (hC : C ≤ 1000000) : (Λ : ℝ) * max 10 (C * Δ) ≤ 1 / 4 := by
    apply (mul_le_mul_of_nonneg_left (max_le (show 10 ≤ 1000000 * Δ by nlinarith)
      (show C * Δ ≤ 1000000 * Δ by nlinarith)) hΛ0).trans
    nlinarith
  have he := complete_fixed_test_ball_scaled_card_le g hEnorm Je ce Se hρ hρpos hΔ
    (by norm_num) (hbudget 100 (by norm_num) (by norm_num)) hSe hdisje p hRice
  have hs := complete_fixed_test_ball_scaled_card_le g hEnorm Js cs Ss hρ hρpos hΔ
    (by norm_num) (hbudget 1000000 (by norm_num) (by norm_num)) hSs hdisjs p hRics
  exact add_le_add he hs


end DifferentialGeometry.Geometry.Riemannian.VolumeComparison.X81Sol

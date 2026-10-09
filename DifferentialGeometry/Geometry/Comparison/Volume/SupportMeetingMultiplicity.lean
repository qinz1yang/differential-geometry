import DifferentialGeometry.Geometry.Comparison.Volume.ScaledBallComparison
import DifferentialGeometry.Geometry.Metric.SupportComparisonLists

/-!
# FC08 on a Riemannian manifold: supports meeting a ball (EGP02, TCP01, SGP01 counts)

Blueprint `master207B.tex`, FC08 (`lem:fibration-ball-packing`, lines 448–490) and its use in
EGP02 (4845–4895), TCP01 (5250–5309) and SGP01 (4353–4408). On a compact connected Riemannian
manifold with `ρ` `Λ`-Lipschitz, `Λ max(R, C) ≤ 1/4`, a family with pairwise disjoint cores
`ball (c j) (a ρ (c j))` and supports `S j ⊆ closedBall (c j) (C ρ (c j))`, and the Ricci bound
`Ric ≥ (n-1)(-(q/ρ(c j))²)` on the WHOLE enlarged ball `ball (c j) (4 (R + 2C + a) ρ (c j))` of every
index whose support meets `ball p (R ρ p)`, the number of such indices is at most
`V_q(4 (R + 2C + a)) / V_q(a)`. The scaled corollary (`R, C, a` proportional to `Δ`, curvature
`q/Δ`) has a bound independent of `Δ`, which is FC08's early multiplicity constant.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

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
  [ConnectedSpace M] [CompactSpace M]

open _root_.Metric DifferentialGeometry.Integral.Measure

/-- FC08 on a compact Riemannian manifold, meeting-ball form. -/
theorem ncard_supports_meeting_ball_le_of_ricci_bound
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
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
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
      (measure_ne_top μ _)
  · intro j _ _
    exact measure_ne_top μ _
  · intro j hj hmeet
    have hric := hRic j hj hmeet
    rw [← hball (c j) (D * ρ (c j))] at hric
    have hcmp := ballVolume_mul_scale_le_model_ratio g hEnorm (c j) hq (hρpos (c j)) ha haD hric
    have hv (r : ℝ) : ballVolume g (c j) r = μ (ball (c j) r) := by
      simp only [ballVolume, μ, hball]
    rw [hv, hv] at hcmp
    have hcmp' := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)) hcmp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (div_nonneg (hm D (ha.trans_le haD)).le (hm a ha).le)] at hcmp'
    simpa only [D, Measure.real] using hcmp'

/-- The scaled form used by the edge and slim lists: radii `R' Δ, C' Δ, a' Δ` and curvature
`Ric ≥ (n-1)(-(q/(Δ ρ))²)` give a bound independent of `Δ`. -/
theorem ncard_supports_meeting_ball_le_of_scaled_ricci_bound
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
  have h := ncard_supports_meeting_ball_le_of_ricci_bound g hEnorm J c S hρ hρpos
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

/-- EGP02's whole-list count: edge supports (radius `15 Δ`) and slim supports (radius `901002 Δ`)
meeting `D = ball p (20 Δ ρ p)`, with the selected disjoint `Δ ρ / 3` cores and FC08's curvature bound
`Ric ≥ (n-1)(-(Δ ρ(c j))⁻²)` on each WHOLE enlarged ball, number at most `N_†`, a constant independent of
`Δ`, the noncollapse and the total number of charts. -/
theorem edge_comparison_list_card_le
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
  have he := ncard_supports_meeting_ball_le_of_scaled_ricci_bound g hEnorm Je ce Se hρ hρpos
    (R := 20) (C := 15) (a := 1 / 3) (q := 1) (by linarith) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (hbudget 15 (by norm_num) (by norm_num)) hSe
    (by simpa only [hcore] using hdisje) p hRice
  have hs := ncard_supports_meeting_ball_le_of_scaled_ricci_bound g hEnorm Js cs Ss hρ hρpos
    (R := 20) (C := 901002) (a := 1 / 3) (q := 1) (by linarith) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (hbudget 901002 (by norm_num) (by norm_num)) hSs
    (by simpa only [hcore] using hdisjs) p hRics
  exact add_le_add he hs

omit [MetricSpace M] [ConnectedSpace M] [CompactSpace M] in
/-- Fewer indices meet a smaller set. -/
theorem ncard_meeting_le_of_ball_subset {κ : Type*} (J : Finset κ) (S : κ → Set M) {D D' : Set M}
    (hD : D ⊆ D') :
    ({j | j ∈ J ∧ (S j ∩ D).Nonempty}.ncard : ℝ) ≤ {j | j ∈ J ∧ (S j ∩ D').Nonempty}.ncard := by
  have hsub : {j | j ∈ J ∧ (S j ∩ D).Nonempty} ⊆ {j | j ∈ J ∧ (S j ∩ D').Nonempty} := by
    intro j hj
    exact ⟨hj.1, hj.2.mono (inter_subset_inter_right _ hD)⟩
  have hfin : {j | j ∈ J ∧ (S j ∩ D').Nonempty}.Finite :=
    J.finite_toSet.subset (fun j hj => hj.1)
  exact_mod_cast Set.ncard_le_ncard hsub hfin

/-- TCP01's whole-list count around `D = ball p (10 ρ p)`: circle supports (radius `10`, cores `ρ/3`,
`Ric ≥ (n-1)(-ρ(c j)⁻²)`), and edge/slim supports counted, as in the blueprint, on the larger ball
`ball p (10 Δ ρ p)` with the edge/slim data of FC08. The bound is independent of `Δ`. -/
theorem two_stratum_list_card_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {ι₂ ιe ιs : Type*} (J₂ : Finset ι₂) (Je : Finset ιe) (Js : Finset ιs)
    (c₂ : ι₂ → M) (ce : ιe → M) (cs : ιs → M)
    (S₂ : ι₂ → Set M) (Se : ιe → Set M) (Ss : ιs → Set M) {ρ : M → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {Δ : ℝ} (hΔ : 1 ≤ Δ)
    (hΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hS₂ : ∀ j ∈ J₂, S₂ j ⊆ closedBall (c₂ j) (10 * ρ (c₂ j)))
    (hSe : ∀ j ∈ Je, Se j ⊆ closedBall (ce j) (15 * Δ * ρ (ce j)))
    (hSs : ∀ j ∈ Js, Ss j ⊆ closedBall (cs j) (901002 * Δ * ρ (cs j)))
    (hdisj₂ : (J₂ : Set ι₂).PairwiseDisjoint fun j => ball (c₂ j) (ρ (c₂ j) / 3))
    (hdisje : (Je : Set ιe).PairwiseDisjoint fun j => ball (ce j) (Δ * ρ (ce j) / 3))
    (hdisjs : (Js : Set ιs).PairwiseDisjoint fun j => ball (cs j) (Δ * ρ (cs j) / 3)) (p : M)
    (hRic₂ : ∀ j ∈ J₂, (S₂ j ∩ ball p (10 * ρ p)).Nonempty → ricciBoundedBelowOn (I := I) g
      (ball (c₂ j) (4 * (10 + 2 * 10 + 1 / 3) * ρ (c₂ j)))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((1 / ρ (c₂ j)) ^ 2))))
    (hRice : ∀ j ∈ Je, (Se j ∩ ball p (10 * Δ * ρ p)).Nonempty → ricciBoundedBelowOn (I := I) g
      (ball (ce j) (4 * (10 + 2 * 15 + 1 / 3) * Δ * ρ (ce j)))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((1 / (Δ * ρ (ce j))) ^ 2))))
    (hRics : ∀ j ∈ Js, (Ss j ∩ ball p (10 * Δ * ρ p)).Nonempty → ricciBoundedBelowOn (I := I) g
      (ball (cs j) (4 * (10 + 2 * 901002 + 1 / 3) * Δ * ρ (cs j)))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((1 / (Δ * ρ (cs j))) ^ 2)))) :
    ({j | j ∈ J₂ ∧ (S₂ j ∩ ball p (10 * ρ p)).Nonempty}.ncard : ℝ) +
        {j | j ∈ Je ∧ (Se j ∩ ball p (10 * ρ p)).Nonempty}.ncard +
        {j | j ∈ Js ∧ (Ss j ∩ ball p (10 * ρ p)).Nonempty}.ncard ≤
      modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (4 * (10 + 2 * 10 + 1 / 3)) /
          modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (1 / 3) +
        modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (4 * (10 + 2 * 15 + 1 / 3)) /
          modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (1 / 3) +
        modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (4 * (10 + 2 * 901002 + 1 / 3)) /
          modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (1 / 3) := by
  have hΛ0 := NNReal.coe_nonneg Λ
  have hcore (x : M) : 1 / 3 * Δ * ρ x = Δ * ρ x / 3 := by ring
  have hbudget (C : ℝ) (hC0 : 0 ≤ C) (hC : C ≤ 901002) :
      (Λ : ℝ) * max (10 * Δ) (C * Δ) ≤ 1 / 4 := by
    apply (mul_le_mul_of_nonneg_left (max_le (show 10 * Δ ≤ 1000000 * Δ by nlinarith)
      (show C * Δ ≤ 1000000 * Δ by nlinarith)) hΛ0).trans
    nlinarith
  have hball : ball p (10 * ρ p) ⊆ ball p (10 * Δ * ρ p) :=
    ball_subset_ball (by nlinarith [hρpos p])
  have h₂ := ncard_supports_meeting_ball_le_of_ricci_bound g hEnorm J₂ c₂ S₂ hρ hρpos
    (R := 10) (C := 10) (a := 1 / 3) (q := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by simpa only [max_self] using (by nlinarith : (Λ : ℝ) * 10 ≤ 1 / 4))
    hS₂ (by simpa only [one_div_mul_eq_div] using hdisj₂) p hRic₂
  have he := ncard_supports_meeting_ball_le_of_scaled_ricci_bound g hEnorm Je ce Se hρ hρpos
    (R := 10) (C := 15) (a := 1 / 3) (q := 1) (by linarith) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (hbudget 15 (by norm_num) (by norm_num)) hSe
    (by simpa only [hcore] using hdisje) p hRice
  have hs := ncard_supports_meeting_ball_le_of_scaled_ricci_bound g hEnorm Js cs Ss hρ hρpos
    (R := 10) (C := 901002) (a := 1 / 3) (q := 1) (by linarith) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (hbudget 901002 (by norm_num) (by norm_num)) hSs
    (by simpa only [hcore] using hdisjs) p hRics
  linarith [ncard_meeting_le_of_ball_subset Je Se hball, ncard_meeting_le_of_ball_subset Js Ss hball]

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

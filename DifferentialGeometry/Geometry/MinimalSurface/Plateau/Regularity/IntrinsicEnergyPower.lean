import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.LocalDefect
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Nonconcentration
import DifferentialGeometry.Analysis.Asymptotics.LimsupDecay
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.IntrinsicBoundaryPower
import DifferentialGeometry.Analysis.Asymptotics.TruncatedBallPower

section

noncomputable section

open Set Filter MeasureTheory Metric Manifold
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

omit [FiniteDimensional ℝ E] [T3Space M] in
private theorem disk_energy_nonneg (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (u : C(closedDisk, M)) (z : ℂ) : 0 ≤ diskMapEnergyDensity g (diskExtension u) z :=
  div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
    (metric_inner_self_nonneg g _ _)) (by norm_num)

private theorem integral_disk_energy_le_total
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : u ∈ weaklyMonotoneDiskCompetitors g γ) {S : Set ℂ}
    (hS : S ⊆ closedBall (0 : ℂ) 1) :
    (∫ z in S, diskMapEnergyDensity g (diskExtension u) z) ≤ riemannianDiskEnergy g u :=
  setIntegral_mono_set (weaklyMonotoneDiskCompetitor_integrable_energy g hu)
    (Eventually.of_forall (disk_energy_nonneg g u)) (Eventually.of_forall hS)

private theorem limsup_disk_energy_mono
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (u : ℕ → C(closedDisk, M)) (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    {B : ℝ} (hB : ∀ n, riemannianDiskEnergy g (u n) ≤ B)
    {S T : Set ℂ} (hST : S ⊆ T) (hT : T ⊆ closedBall (0 : ℂ) 1) :
    limsup (fun n => ∫ z in S, diskMapEnergyDensity g (diskExtension (u n)) z) atTop ≤
      limsup (fun n => ∫ z in T, diskMapEnergyDensity g (diskExtension (u n)) z) atTop := by
  apply limsup_le_limsup
    (Eventually.of_forall fun n => setIntegral_mono_set
      ((weaklyMonotoneDiskCompetitor_integrable_energy g (hu n)).mono_set hT)
      (Eventually.of_forall (disk_energy_nonneg g (u n))) (Eventually.of_forall hST))
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n =>
      integral_nonneg (disk_energy_nonneg g (u n)))).isCoboundedUnder_le
    (isBoundedUnder_of_eventually_le (Eventually.of_forall fun n =>
      (integral_disk_energy_le_total g (hu n) hT).trans (hB n)))

private theorem dist_normalize_of_norm_le_one {x : ℂ} (hx : x ≠ 0) (hx1 : ‖x‖ ≤ 1) :
    dist x (NormedSpace.normalize x) = 1 - ‖x‖ := by
  have he : x - NormedSpace.normalize x = (‖x‖ - 1) • NormedSpace.normalize x := by
    rw [sub_smul, one_smul, NormedSpace.norm_smul_normalize]
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, NormedSpace.norm_normalize hx,
    mul_one, abs_of_nonpos (by linarith)]
  ring

theorem exists_uniform_small_limsup_disk_energy_of_boundary_power
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    {β Kb δb : ℝ} (hβ : 0 < β) (hδb : 0 < δb)
    (hboundary : ∀ c ∈ sphere (0 : ℂ) 1, ∀ s : ℝ, 0 < s → s ≤ δb →
      limsup (fun n => ∫ z in ball (0 : ℂ) 1 ∩ closedBall c s,
        diskMapEnergyDensity g (diskExtension (u n)) z) atTop ≤ Kb * s ^ β)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ ∀ x ∈ closedBall (0 : ℂ) 1,
      ∀ s : ℝ, 0 < s → s ≤ δ →
        limsup (fun n => ∫ z in ball (0 : ℂ) 1 ∩ closedBall x s,
          diskMapEnergyDensity g (diskExtension (u n)) z) atTop ≤ η := by
  obtain ⟨B, hB⟩ := hmin.bddAbove_range
  have htotal (n : ℕ) : riemannianDiskEnergy g (u n) ≤ B := hB (mem_range_self n)
  obtain ⟨N, _, hevent⟩ := exists_eventually_uniform_small_ball_energy_of_minimizing_sequence
    g hregular γ u hu hmin hη
  have hlim : Tendsto (fun t : ℝ => Kb * (3 * t) ^ β) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => Kb * (3 * t) ^ β) :=
      continuous_const.mul ((Real.continuous_rpow_const hβ.le).comp
        (continuous_const.mul continuous_id))
    simpa only [mul_zero, Real.zero_rpow hβ.ne'] using hc.tendsto 0
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (hlim (Iio_mem_nhds hη))
  let d₀ := min (r / 2) (min (δb / 3) (1 / 8))
  have hd₀ : 0 < d₀ := lt_min (half_pos hr) (lt_min (by positivity) (by norm_num))
  have hd₀r : d₀ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hd₀b : d₀ ≤ δb / 3 := (min_le_right _ _).trans (min_le_left _ _)
  have hd₀8 : d₀ ≤ 1 / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : Kb * (3 * d₀) ^ β < η := hrsub (by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hd₀] using hd₀r)
  let δ := d₀ / (2 : ℝ) ^ N
  have hδ : 0 < δ := div_pos hd₀ (by positivity)
  have hδd : δ ≤ d₀ := div_le_self hd₀.le (one_le_pow₀ (by norm_num))
  refine ⟨δ, hδ, hδd.trans hd₀8, ?_⟩
  intro x hx s hs hsδ
  have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  by_cases hnear : 1 - ‖x‖ ≤ 2 * d₀
  · have hx0 : x ≠ 0 := by
      intro heq
      rw [heq, norm_zero] at hnear
      linarith [hd₀8]
    let c := NormedSpace.normalize x
    have hc : c ∈ sphere (0 : ℂ) 1 :=
      mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hx0)
    have hxc : dist x c = 1 - ‖x‖ := dist_normalize_of_norm_le_one hx0 hx1
    have hcap : ball (0 : ℂ) 1 ∩ closedBall x s ⊆
        ball (0 : ℂ) 1 ∩ closedBall c (3 * d₀) := by
      intro z hz
      refine ⟨hz.1, ?_⟩
      have hdist := dist_triangle z x c
      rw [hxc] at hdist
      have hzx : dist z x ≤ s := hz.2
      change dist z c ≤ 3 * d₀
      linarith [hsδ.trans hδd]
    exact (limsup_disk_energy_mono g u hu htotal hcap
      (inter_subset_left.trans ball_subset_closedBall)).trans
        ((hboundary c hc (3 * d₀) (by positivity) (by linarith [hd₀b])).trans hsmall.le)
  · have hxR : ‖x‖ + d₀ < 1 := by linarith
    have hset : ball (0 : ℂ) 1 ∩ closedBall x s ⊆ closedBall x δ :=
      fun z hz => closedBall_subset_closedBall hsδ hz.2
    have hT : closedBall x δ ⊆ closedBall (0 : ℂ) 1 := by
      intro z hz
      have hnorm : ‖z‖ ≤ dist z x + ‖x‖ := by
        simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - x) x
      exact mem_closedBall_zero_iff.mpr (by linarith [mem_closedBall.mp hz])
    apply (limsup_disk_energy_mono g u hu htotal hset hT).trans
    apply limsup_le_of_le
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n =>
        integral_nonneg (disk_energy_nonneg g (u n)))).isCoboundedUnder_le
    filter_upwards [hevent] with n hn
    exact hn x d₀ hd₀ hxR

theorem exists_limsup_disk_energy_half_contraction_of_boundary_power
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    {β Kb δb : ℝ} (hβ : 0 < β) (hδb : 0 < δb)
    (hboundary : ∀ c ∈ sphere (0 : ℂ) 1, ∀ s : ℝ, 0 < s → s ≤ δb →
      limsup (fun n => ∫ z in ball (0 : ℂ) 1 ∩ closedBall c s,
        diskMapEnergyDensity g (diskExtension (u n)) z) atTop ≤ Kb * s ^ β) :
    ∃ ε δ θ : ℝ, 0 < ε ∧ 0 < δ ∧ δ ≤ 1 / 8 ∧ 0 < θ ∧ θ < 1 ∧
      (∀ x ∈ closedBall (0 : ℂ) 1, ∀ s : ℝ, 0 < s → s ≤ δ →
        limsup (fun n => ∫ z in ball (0 : ℂ) 1 ∩ closedBall x s,
          diskMapEnergyDensity g (diskExtension (u n)) z) atTop ≤ ε / 2) ∧
      ∀ (x : ℂ) (s : ℝ), 0 < s → s ≤ δ → ‖x‖ + s < 1 →
        (∀ᶠ n in atTop, (∫ z in closedBall x s,
          diskMapEnergyDensity g (diskExtension (u n)) z) < ε) ∧
        limsup (fun n => ∫ z in closedBall x (s / 2),
          diskMapEnergyDensity g (diskExtension (u n)) z) atTop ≤
          θ * limsup (fun n => ∫ z in closedBall x s,
            diskMapEnergyDensity g (diskExtension (u n)) z) atTop := by
  obtain ⟨ε, θ, hε, hθ, hθ1, hcontract⟩ :=
    exists_local_energy_contraction_with_minimizing_defect g hregular
  obtain ⟨δ, hδ, hδ8, hsmall⟩ := exists_uniform_small_limsup_disk_energy_of_boundary_power
    g hregular γ u hu hmin hβ hδb hboundary (half_pos hε)
  obtain ⟨B, hB⟩ := hmin.bddAbove_range
  have htotal (n : ℕ) : riemannianDiskEnergy g (u n) ≤ B := hB (mem_range_self n)
  refine ⟨ε, δ, θ, hε, hδ, hδ8, hθ, hθ1, hsmall, ?_⟩
  intro x s hs hsδ hxs
  have hx : x ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr (by linarith)
  have hsub : closedBall x s ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    have hn : ‖z‖ ≤ dist z x + ‖x‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - x) x
    exact mem_ball_zero_iff.mpr (by linarith [mem_closedBall.mp hz])
  let a (n : ℕ) := ∫ z in closedBall x s, diskMapEnergyDensity g (diskExtension (u n)) z
  let b (n : ℕ) := ∫ z in closedBall x (s / 2), diskMapEnergyDensity g (diskExtension (u n)) z
  have ha0 : ∀ᶠ n in atTop, 0 ≤ a n :=
    Eventually.of_forall fun n => integral_nonneg (disk_energy_nonneg g (u n))
  have hb0 : ∀ᶠ n in atTop, 0 ≤ b n :=
    Eventually.of_forall fun n => integral_nonneg (disk_energy_nonneg g (u n))
  have haB : IsBoundedUnder (· ≤ ·) atTop a :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n =>
      (integral_disk_energy_le_total g (hu n) (hsub.trans ball_subset_closedBall)).trans (htotal n))
  have halim : limsup a atTop ≤ ε / 2 := by
    have h := hsmall x hx s hs hsδ
    rwa [inter_eq_right.mpr hsub] at h
  have hevent : ∀ᶠ n in atTop, a n < ε :=
    eventually_lt_of_limsup_lt (halim.trans_lt (half_lt_self hε)) haB
  let defect (n : ℕ) := riemannianDiskEnergy g (u n) -
    sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
      weaklyMonotoneDiskCompetitors g γ)
  have hdefect : Tendsto defect atTop (𝓝 0) := by
    simpa only [defect, sub_self] using hmin.sub_const
      (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))
  have herr : Tendsto (fun n => (1 - θ) * defect n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hdefect.const_mul (1 - θ)
  refine ⟨hevent, ?_⟩
  apply limsup_le_mul_limsup_of_eventually_le_add_tendsto_zero hθ.le ha0 haB hb0 herr
  filter_upwards [hevent] with n hn
  exact hcontract γ (u n) (hu n) x s hs hxs hn

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Set Filter MeasureTheory Metric Manifold
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_uniform_intrinsic_truncated_ball_power_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (u : ℕ → C(closedDisk, M)) (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (ψ : ℕ → CircleDeg1Lift) (hψ : ∀ n, Continuous (ψ n))
    (htrace : ∀ n (t : ℝ), u n (diskBoundary (t : loopCircle)) =
      γ ((ψ n t : ℝ) : loopCircle))
    (hthird : ∀ n, ψ n (1 / 3 : ℝ) = ψ n 0 + 1 / 3)
    (htwothird : ∀ n, ψ n (2 / 3 : ℝ) = ψ n 0 + 2 / 3) :
    ∃ p δ C : ℝ, 0 < p ∧ p ≤ 2 ∧ 0 < δ ∧ δ ≤ 1 / 8 ∧ 0 ≤ C ∧
      ∀ x ∈ closedBall (0 : ℂ) 1, ∀ s : ℝ, 0 < s → s ≤ δ →
        limsup (fun n => ∫ z in ball (0 : ℂ) 1 ∩ closedBall x s,
          diskMapEnergyDensity g (diskExtension (u n)) z) atTop ≤ C * s ^ p := by
  obtain ⟨β, Kb, δb, hβ, _, hKb, hδb, hboundary⟩ :=
    exists_uniform_intrinsic_boundary_power_bound g γ hγ u hu hmin ψ hψ htrace hthird htwothird
  obtain ⟨_, δi, θ, _, hδi, _, hθ, hθ1, _, hhalf⟩ :=
    exists_limsup_disk_energy_half_contraction_of_boundary_power
      g hregular γ u hu hmin hβ hδb hboundary
  let e (n : ℕ) := diskMapEnergyDensity g (diskExtension (u n))
  let ν (S : Set ℂ) := limsup (fun n => ∫ z in S, e n z) atTop
  obtain ⟨B, hB⟩ := hmin.bddAbove_range
  have htotal (n : ℕ) : riemannianDiskEnergy g (u n) ≤ B := hB (mem_range_self n)
  have h0 (n : ℕ) (z : ℂ) : 0 ≤ e n z := by
    unfold e diskMapEnergyDensity
    exact div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
      (metric_inner_self_nonneg g _ _)) (by norm_num)
  have hi (n : ℕ) := weaklyMonotoneDiskCompetitor_integrable_energy g (hu n)
  have hsubsetBound {S : Set ℂ} (hS : S ⊆ closedBall (0 : ℂ) 1) (n : ℕ) :
      (∫ z in S, e n z) ≤ B :=
    (setIntegral_mono_set (hi n) (Eventually.of_forall (h0 n))
      (Eventually.of_forall hS)).trans (htotal n)
  have hmono : ∀ {S T : Set ℂ}, S ⊆ T → T ⊆ ball (0 : ℂ) 1 → ν S ≤ ν T := by
    intro S T hST hTD
    exact limsup_le_limsup (Eventually.of_forall fun n =>
      setIntegral_mono_set ((hi n).mono_set (hTD.trans ball_subset_closedBall))
        (Eventually.of_forall (h0 n)) (Eventually.of_forall hST))
      (isBoundedUnder_of_eventually_ge
        (Eventually.of_forall fun n => integral_nonneg (h0 n))).isCoboundedUnder_le
      (isBoundedUnder_of_eventually_le
        (Eventually.of_forall (hsubsetBound (hTD.trans ball_subset_closedBall))))
  have hν : 0 ≤ ν (ball (0 : ℂ) 1) :=
    le_limsup_of_frequently_le (Eventually.of_forall (fun n => integral_nonneg (h0 n))).frequently
      (isBoundedUnder_of_eventually_le (Eventually.of_forall (hsubsetBound ball_subset_closedBall)))
  obtain ⟨p, δ, C, hp, _, hp2, hδ, hδ8, hC, hpower⟩ :=
    exists_uniform_truncated_ball_power_bound_of_boundary_bound_of_half_contraction ν
      hmono hν hβ hKb hδb hδi hθ.le hθ1 hboundary
      (fun x s hs hsδ hxs => (hhalf x s hs hsδ hxs).2)
  exact ⟨p, δ, C, hp, hp2, hδ, hδ8, hC, hpower⟩

end DifferentialGeometry.Geometry

end

end

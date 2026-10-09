import DifferentialGeometry.Topology.LoopSpace.PeriodicExtension
import DifferentialGeometry.Analysis.Calculus.Periodic.Affine
import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

noncomputable section

open Set
open scoped NNReal

namespace CircleDeg1Lift

private def splineRamp (x : ℝ) : ℝ := min (max x 0) 1

private theorem splineRamp_lipschitz : LipschitzWith 1 splineRamp :=
  (LipschitzWith.id.max_const 0).min_const 1

private theorem splineRamp_monotone : Monotone splineRamp := fun _ _ hxy =>
  min_le_min (max_le_max hxy le_rfl) le_rfl

private theorem splineRamp_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : splineRamp x = 0 := by
  simp only [splineRamp, max_eq_right hx, min_eq_left zero_le_one]

private theorem splineRamp_one_of_one_le {x : ℝ} (hx : 1 ≤ x) : splineRamp x = 1 := by
  rw [splineRamp, max_eq_left (zero_le_one.trans hx), min_eq_right hx]

private theorem splineRamp_eq_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : splineRamp x = x := by
  rw [splineRamp, max_eq_left hx.1, min_eq_left hx.2]

private def splineProfile (ψ : CircleDeg1Lift) (N : ℕ) (t : ℝ) : ℝ :=
  ψ 0 + ∑ i ∈ Finset.range N,
    (ψ ((i + 1 : ℕ) / (N : ℝ)) - ψ (i / (N : ℝ))) * splineRamp ((N : ℝ) * t - i)

theorem uniform_partition_increment_nonneg (ψ : CircleDeg1Lift) (N i : ℕ) :
    0 ≤ ψ ((i + 1 : ℕ) / (N : ℝ)) - ψ (i / (N : ℝ)) := by
  apply sub_nonneg.mpr
  apply ψ.monotone
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ i) (Nat.cast_nonneg N)

theorem sum_uniform_partition_increment (ψ : CircleDeg1Lift) {N : ℕ} (hN : 0 < N) :
    (∑ i ∈ Finset.range N, (ψ ((i + 1 : ℕ) / (N : ℝ)) - ψ (i / (N : ℝ)))) = 1 := by
  rw [Finset.sum_range_sub (fun i : ℕ => ψ (i / (N : ℝ))) N]
  simp only [Nat.cast_zero, zero_div, div_self (by exact_mod_cast hN.ne' : (N : ℝ) ≠ 0)]
  have hp := ψ.map_add_one 0
  simp only [zero_add] at hp
  linarith

private theorem splineProfile_formula (ψ : CircleDeg1Lift) {N i : ℕ} (hN : 0 < N)
    (hi : i < N) {t : ℝ} (ht : t ∈ Icc (i / (N : ℝ)) ((i + 1 : ℕ) / (N : ℝ))) :
    splineProfile ψ N t = ψ (i / (N : ℝ)) +
      (ψ ((i + 1 : ℕ) / (N : ℝ)) - ψ (i / (N : ℝ))) * ((N : ℝ) * t - i) := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  have htlo : (i : ℝ) ≤ (N : ℝ) * t := by
    have h := (div_le_iff₀ hNp).mp ht.1
    nlinarith
  have hthi : (N : ℝ) * t ≤ (i : ℝ) + 1 := by
    have h := (le_div_iff₀ hNp).mp ht.2
    push_cast at h
    nlinarith
  let Δ := fun k : ℕ => ψ ((k + 1 : ℕ) / (N : ℝ)) - ψ (k / (N : ℝ))
  have hterm (k : ℕ) : Δ k * splineRamp ((N : ℝ) * t - k) =
      if k < i then Δ k else if k = i then Δ i * ((N : ℝ) * t - i) else 0 := by
    by_cases hk : k < i
    · rw [ite_eq_left hk, splineRamp_one_of_one_le, mul_one]
      have hki : (k : ℝ) + 1 ≤ i := by exact_mod_cast hk
      linarith
    · rw [ite_eq_right hk]
      by_cases hki : k = i
      · subst k
        rw [ite_eq_left rfl, splineRamp_eq_of_mem ⟨by linarith, by linarith⟩]
      · rw [ite_eq_right hki, splineRamp_zero_of_nonpos, mul_zero]
        have hki' : i + 1 ≤ k := by omega
        have hcast : (i : ℝ) + 1 ≤ k := by exact_mod_cast hki'
        linarith
  have hsplit : (∑ k ∈ Finset.range N, Δ k * splineRamp ((N : ℝ) * t - k)) =
      (∑ k ∈ Finset.range i, Δ k) + Δ i * ((N : ℝ) * t - i) := by
    simp_rw [hterm]
    have hfun (k : ℕ) : (if k < i then Δ k else if k = i then Δ i * ((N : ℝ) * t - i) else 0) =
        (if k < i then Δ k else 0) + (if k = i then Δ i * ((N : ℝ) * t - i) else 0) := by
      split_ifs <;> simp_all
    simp_rw [hfun]
    rw [Finset.sum_add_distrib]
    have hsum : (∑ k ∈ Finset.range N, if k < i then Δ k else 0) = ∑ k ∈ Finset.range i, Δ k := by
      rw [← Finset.sum_filter]
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hsum]
    simp only [Finset.sum_ite_eq', Finset.mem_range.mpr hi, ↓reduceIte]
  dsimp only [splineProfile]
  change ψ 0 + (∑ k ∈ Finset.range N, Δ k * splineRamp ((N : ℝ) * t - k)) = _
  rw [hsplit]
  have hsum : (∑ k ∈ Finset.range i, Δ k) = ψ (i / (N : ℝ)) - ψ 0 := by
    dsimp only [Δ]
    rw [Finset.sum_range_sub (fun k : ℕ => ψ (k / (N : ℝ))) i]
    simp
  rw [hsum]
  dsimp only [Δ]
  ring

private theorem splineProfile_zero (ψ : CircleDeg1Lift) (N : ℕ) : splineProfile ψ N 0 = ψ 0 := by
  unfold splineProfile
  have hzero (i : ℕ) : splineRamp (0 - (i : ℝ)) = 0 :=
    splineRamp_zero_of_nonpos (by simp)
  simp only [mul_zero, hzero, Finset.sum_const_zero, add_zero]

private theorem splineProfile_one (ψ : CircleDeg1Lift) {N : ℕ} (hN : 0 < N) :
    splineProfile ψ N 1 = ψ 0 + 1 := by
  unfold splineProfile
  have hone : ∀ i ∈ Finset.range N, splineRamp ((N : ℝ) * 1 - i) = 1 := by
    intro i hi
    apply splineRamp_one_of_one_le
    have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hi
    linarith
  rw [Finset.sum_congr rfl (fun i hi => by rw [hone i hi, mul_one]),
    sum_uniform_partition_increment ψ hN]

private theorem splineProfile_lipschitz (ψ : CircleDeg1Lift) {N : ℕ} (hN : 0 < N) :
    LipschitzWith (N : ℝ≥0) (splineProfile ψ N) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (ψ 0 + _) (ψ 0 + _) ≤ _
  rw [dist_add_left, Real.dist_eq, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range N,
        |(ψ ((i + 1 : ℕ) / (N : ℝ)) - ψ (i / (N : ℝ))) *
          (splineRamp ((N : ℝ) * x - i) - splineRamp ((N : ℝ) * y - i))| := by
      simpa only [← mul_sub] using Finset.abs_sum_le_sum_abs
        (s := Finset.range N) (f := fun i =>
          (ψ ((i + 1 : ℕ) / (N : ℝ)) - ψ (i / (N : ℝ))) * splineRamp ((N : ℝ) * x - i) -
          (ψ ((i + 1 : ℕ) / (N : ℝ)) - ψ (i / (N : ℝ))) * splineRamp ((N : ℝ) * y - i))
    _ ≤ ∑ i ∈ Finset.range N,
        (ψ ((i + 1 : ℕ) / (N : ℝ)) - ψ (i / (N : ℝ))) * ((N : ℝ) * dist x y) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (uniform_partition_increment_nonneg ψ N i)]
      apply mul_le_mul_of_nonneg_left _ (uniform_partition_increment_nonneg ψ N i)
      have h := splineRamp_lipschitz.dist_le_mul ((N : ℝ) * x - i) ((N : ℝ) * y - i)
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq, sub_sub_sub_cancel_right,
        ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)] using h
    _ = (N : ℝ≥0) * dist x y := by
      rw [← Finset.sum_mul, sum_uniform_partition_increment ψ hN, one_mul]
      rfl

private theorem splineProfile_monotone (ψ : CircleDeg1Lift) (N : ℕ) :
    Monotone (splineProfile ψ N) := by
  intro x y hxy
  unfold splineProfile
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (uniform_partition_increment_nonneg ψ N i)
  exact splineRamp_monotone (sub_le_sub_right
    (mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg N)) i)

theorem exists_uniform_piecewise_affine_lift (ψ : CircleDeg1Lift) {N : ℕ} (hN : 0 < N) :
    ∃ g : CircleDeg1Lift, LipschitzWith (N : ℝ≥0) g ∧
      (∀ i < N, ∀ t ∈ Icc (i / (N : ℝ)) ((i + 1 : ℕ) / (N : ℝ)),
        g t = ψ (i / (N : ℝ)) +
          (ψ ((i + 1 : ℕ) / (N : ℝ)) - ψ (i / (N : ℝ))) * ((N : ℝ) * t - i)) ∧
      (∀ i ≤ N, g (i / (N : ℝ)) = ψ (i / (N : ℝ))) := by
  have hLip := splineProfile_lipschitz ψ hN
  obtain ⟨G, hGc, hG⟩ := AddConstMap.exists_continuous_extension_Icc 0 hLip.continuous.continuousOn
    (by simpa only [zero_add, splineProfile_zero] using splineProfile_one ψ hN)
  have hGp (x : ℝ) : G (x + 1) = G x + 1 := G.map_add_const' x
  have hGm : Monotone G := (AddConstMapClass.monotone_iff_Icc (f := G)
    (by norm_num : (0 : ℝ) < 1) 0).mpr (by
      intro x hx y hy hxy
      rw [hG hx, hG hy]
      exact splineProfile_monotone ψ N hxy)
  let g : CircleDeg1Lift := ⟨⟨G, hGm⟩, hGp⟩
  let H : AddConstMap ℝ ℝ 1 ((N : ℝ) - 1) :=
    ⟨fun x => (N : ℝ) * x - G x, fun x => by rw [hGp]; ring⟩
  have hHm : Monotone H := (AddConstMapClass.monotone_iff_Icc (f := H)
    (by norm_num : (0 : ℝ) < 1) 0).mpr (by
      intro x hx y hy hxy
      change (N : ℝ) * x - G x ≤ (N : ℝ) * y - G y
      rw [hG hx, hG hy]
      have h := hLip.dist_le_mul y x
      rw [Real.dist_eq, Real.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr (splineProfile_monotone ψ N hxy)),
        abs_of_nonneg (sub_nonneg.mpr hxy)] at h
      norm_num only [NNReal.coe_natCast] at h
      linarith)
  have hgd {x y : ℝ} (hxy : x ≤ y) : g y - g x ≤ (N : ℝ) * (y - x) := by
    have h := hHm hxy
    change (N : ℝ) * x - G x ≤ (N : ℝ) * y - G y at h
    change G y - G x ≤ (N : ℝ) * (y - x)
    linarith
  have hgLip : LipschitzWith (N : ℝ≥0) g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rcases le_total x y with hxy | hyx
    · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy),
        abs_of_nonpos (sub_nonpos.mpr (g.monotone hxy)), neg_sub, NNReal.coe_natCast] using hgd hxy
    · simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx),
        abs_of_nonneg (sub_nonneg.mpr (g.monotone hyx)), NNReal.coe_natCast] using hgd hyx
  have hformula (i : ℕ) (hi : i < N) (t : ℝ)
      (ht : t ∈ Icc (i / (N : ℝ)) ((i + 1 : ℕ) / (N : ℝ))) :
      g t = ψ (i / (N : ℝ)) +
        (ψ ((i + 1 : ℕ) / (N : ℝ)) - ψ (i / (N : ℝ))) * ((N : ℝ) * t - i) := by
    change G t = _
    rw [hG (show t ∈ Icc (0 : ℝ) (0 + 1) from ⟨
      (div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg N)).trans ht.1,
      ht.2.trans (by
        rw [zero_add, div_le_one (by exact_mod_cast hN : 0 < (N : ℝ))]
        exact_mod_cast hi)⟩)]
    exact splineProfile_formula ψ hN hi ht
  refine ⟨g, hgLip, hformula, ?_⟩
  intro i hi
  rcases lt_or_eq_of_le hi with hi | heq
  · rw [hformula i hi _ ⟨le_rfl, div_le_div_of_nonneg_right
      (by exact_mod_cast Nat.le_succ i) (Nat.cast_nonneg N)⟩]
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [mul_div_cancel₀ _ hn, sub_self, mul_zero, add_zero]
  · subst i
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [div_self hn]
    change G 1 = ψ 1
    rw [hG (by norm_num : (1 : ℝ) ∈ Icc 0 (0 + 1)), splineProfile_one ψ hN]
    simpa only [zero_add] using (ψ.map_add_one 0).symm

end CircleDeg1Lift

end

noncomputable section

open Set Filter
open scoped Topology NNReal

namespace CircleDeg1Lift

private theorem exists_grid_cell {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    ∃ i < N, t ∈ Icc (i / (N : ℝ)) ((i + 1 : ℕ) / (N : ℝ)) := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  refine ⟨⌊(N : ℝ) * t⌋₊, ?_, ?_, ?_⟩
  · apply (Nat.floor_lt (mul_nonneg hNp.le ht.1)).mpr
    nlinarith [ht.2]
  · apply (div_le_iff₀ hNp).mpr
    simpa only [mul_comm] using Nat.floor_le (mul_nonneg hNp.le ht.1)
  · apply (le_div_iff₀ hNp).mpr
    have h := Nat.lt_floor_add_one ((N : ℝ) * t)
    push_cast
    nlinarith

theorem dist_le_increment_of_grid_knots (ψ g : CircleDeg1Lift) {N i : ℕ}
    (hi : i < N) (hknots : ∀ k ≤ N, g (k / (N : ℝ)) = ψ (k / (N : ℝ)))
    {t : ℝ} (ht : t ∈ Icc (i / (N : ℝ)) ((i + 1 : ℕ) / (N : ℝ))) :
    dist (g t) (ψ t) ≤ ψ ((i + 1 : ℕ) / (N : ℝ)) - ψ (i / (N : ℝ)) := by
  have hglo := g.monotone ht.1
  have hghi := g.monotone ht.2
  rw [hknots i hi.le] at hglo
  rw [hknots (i + 1) (by omega)] at hghi
  have hψlo := ψ.monotone ht.1
  have hψhi := ψ.monotone ht.2
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

private theorem eventually_uniform_partition_increment_lt
    (ψ : CircleDeg1Lift) (hψ : Continuous ψ) (N : ℕ → ℕ)
    (hN : ∀ n, 0 < N n) (hNlim : Tendsto N atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ i : ℕ,
      ψ ((i + 1 : ℕ) / (N n : ℝ)) - ψ (i / (N n : ℝ)) < ε := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (DifferentialGeometry.Analysis.uniformContinuous_affinePeriodic hψ ψ.map_add_one) ε hε
  have hmesh : Tendsto (fun n => 1 / (N n : ℝ)) atTop (𝓝 0) :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hNlim
  filter_upwards [(tendsto_order.mp hmesh).2 δ hδ] with n hn
  intro i
  have hNp : 0 < (N n : ℝ) := by exact_mod_cast hN n
  have hdist : dist ((i + 1 : ℕ) / (N n : ℝ)) (i / (N n : ℝ)) = 1 / (N n : ℝ) := by
    rw [Real.dist_eq]
    have heq : ((i + 1 : ℕ) : ℝ) / (N n : ℝ) - (i : ℝ) / (N n : ℝ) =
        1 / (N n : ℝ) := by push_cast; ring
    rw [heq, abs_of_pos (one_div_pos.mpr hNp)]
  have h := hmod (by rw [hdist]; exact hn)
  simpa only [Real.dist_eq, abs_of_nonneg (ψ.uniform_partition_increment_nonneg (N n) i)] using h

theorem tendsto_sum_uniform_partition_increment_sq
    (ψ : CircleDeg1Lift) (hψ : Continuous ψ) (N : ℕ → ℕ)
    (hN : ∀ n, 0 < N n) (hNlim : Tendsto N atTop atTop) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      (ψ ((i + 1 : ℕ) / (N n : ℝ)) - ψ (i / (N n : ℝ))) ^ 2) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_uniform_partition_increment_lt ψ hψ N hN hNlim (half_pos hε)] with n hn
  have hsum : (∑ i ∈ Finset.range (N n),
      (ψ ((i + 1 : ℕ) / (N n : ℝ)) - ψ (i / (N n : ℝ))) ^ 2) ≤ ε / 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range (N n), (ε / 2) *
          (ψ ((i + 1 : ℕ) / (N n : ℝ)) - ψ (i / (N n : ℝ))) := by
        apply Finset.sum_le_sum
        intro i hi
        have h := mul_le_mul_of_nonneg_right (hn i).le
          (ψ.uniform_partition_increment_nonneg (N n) i)
        simpa only [pow_two] using h
      _ = ε / 2 := by
        rw [← Finset.mul_sum, ψ.sum_uniform_partition_increment (hN n), mul_one]
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i hi => sq_nonneg _)]
  exact hsum.trans_lt (half_lt_self hε)

theorem tendstoUniformly_of_grid_knots
    (ψ : CircleDeg1Lift) (hψ : Continuous ψ) (g : ℕ → CircleDeg1Lift) (N : ℕ → ℕ)
    (hN : ∀ n, 0 < N n) (hNlim : Tendsto N atTop atTop)
    (hknots : ∀ n k, k ≤ N n → g n (k / (N n : ℝ)) = ψ (k / (N n : ℝ))) :
    TendstoUniformly (fun n t => g n t) ψ atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [eventually_uniform_partition_increment_lt ψ hψ N hN hNlim hε] with n hn
  intro t
  obtain ⟨k, hk, _⟩ := existsUnique_sub_zsmul_mem_Ico (by norm_num : (0 : ℝ) < 1) t 0
  have htk : t - (k : ℝ) ∈ Ico (0 : ℝ) 1 := by
    simpa only [zsmul_eq_mul, mul_one, zero_add] using hk
  obtain ⟨i, hi, hit⟩ := exists_grid_cell (hN n) htk
  have h := (dist_le_increment_of_grid_knots ψ (g n) hi (hknots n) hit).trans_lt (hn i)
  rw [(g n).map_sub_int, ψ.map_sub_int, dist_sub_right] at h
  simpa only [dist_comm] using h

theorem exists_uniform_piecewise_affine_sequence (ψ : CircleDeg1Lift) (hψ : Continuous ψ) :
    ∃ g : ℕ → CircleDeg1Lift,
      (∀ n : ℕ, LipschitzWith ((3 * (n + 1) : ℕ) : ℝ≥0) (g n)) ∧
      (∀ (n i : ℕ), i < 3 * (n + 1) → ∀ t ∈ Icc (i / ((3 * (n + 1) : ℕ) : ℝ))
        ((i + 1 : ℕ) / ((3 * (n + 1) : ℕ) : ℝ)),
        g n t = ψ (i / ((3 * (n + 1) : ℕ) : ℝ)) +
          (ψ ((i + 1 : ℕ) / ((3 * (n + 1) : ℕ) : ℝ)) - ψ (i / ((3 * (n + 1) : ℕ) : ℝ))) *
            (((3 * (n + 1) : ℕ) : ℝ) * t - i)) ∧
      (∀ (n i : ℕ), i ≤ 3 * (n + 1) → g n (i / ((3 * (n + 1) : ℕ) : ℝ)) =
        ψ (i / ((3 * (n + 1) : ℕ) : ℝ))) ∧
      (∀ n, g n 0 = ψ 0 ∧ g n (1 / 3) = ψ (1 / 3) ∧ g n (2 / 3) = ψ (2 / 3)) ∧
      TendstoUniformly (fun n t => g n t) ψ atTop ∧
      Tendsto (fun n => ∑ i ∈ Finset.range (3 * (n + 1)),
        (ψ ((i + 1 : ℕ) / ((3 * (n + 1) : ℕ) : ℝ)) - ψ (i / ((3 * (n + 1) : ℕ) : ℝ))) ^ 2)
        atTop (𝓝 0) := by
  classical
  let N : ℕ → ℕ := fun n : ℕ => 3 * (n + 1)
  have hN (n : ℕ) : 0 < N n := by dsimp only [N]; omega
  choose g hLip hcell hknots using fun n => ψ.exists_uniform_piecewise_affine_lift (hN n)
  have hNlim : Tendsto N atTop atTop := by
    apply tendsto_atTop_mono (fun n => show n ≤ N n by dsimp only [N]; omega) tendsto_id
  have hmarks (n : ℕ) : g n 0 = ψ 0 ∧ g n (1 / 3) = ψ (1 / 3) ∧ g n (2 / 3) = ψ (2 / 3) := by
    have h0 := hknots n 0 (Nat.zero_le _)
    have h1 := hknots n (n + 1) (by dsimp only [N]; omega)
    have h2 := hknots n (2 * (n + 1)) (by dsimp only [N]; omega)
    have hden : (n : ℝ) + 1 ≠ 0 := by positivity
    have he1 : ((n + 1 : ℕ) : ℝ) / (N n : ℝ) = 1 / 3 := by
      dsimp only [N]
      push_cast
      field_simp
    have he2 : ((2 * (n + 1) : ℕ) : ℝ) / (N n : ℝ) = 2 / 3 := by
      dsimp only [N]
      push_cast
      field_simp
    exact ⟨by simpa using h0, he1 ▸ h1, he2 ▸ h2⟩
  refine ⟨g, ?_, ?_, ?_, hmarks, tendstoUniformly_of_grid_knots ψ hψ g N hN hNlim hknots, ?_⟩
  · intro n
    simpa only [N, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hLip n
  · intro n i hi t ht
    simpa only [N, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      hcell n i hi t ht
  · intro n i hi
    simpa only [N, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hknots n i hi
  · simpa only [N, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      tendsto_sum_uniform_partition_increment_sq ψ hψ N hN hNlim

end CircleDeg1Lift

end

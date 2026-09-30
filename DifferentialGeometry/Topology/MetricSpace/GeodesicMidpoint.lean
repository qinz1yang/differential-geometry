import DifferentialGeometry.Topology.MetricSpace.GeodesicCompactness
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology NNReal

namespace Metric

variable {X : Type*} [MetricSpace X]

private theorem exists_dyadic_chain
    (hm : ∀ a b : X, ∃ m, dist a m = dist a b / 2 ∧ dist m b = dist a b / 2)
    (n : ℕ) (a b : X) :
    ∃ f : ℕ → X, f 0 = a ∧ f (2 ^ n) = b ∧
      ∀ k < 2 ^ n, dist (f k) (f (k + 1)) ≤ dist a b * (1 / 2 : ℝ) ^ n := by
  induction n generalizing a b with
  | zero =>
    refine ⟨fun k => if k = 0 then a else b, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro k hk
      have hk0 : k = 0 := by simpa using hk
      simp [hk0]
  | succ n ih =>
    obtain ⟨m, ham, hmb⟩ := hm a b
    obtain ⟨f, hf0, hfend, hf⟩ := ih a m
    obtain ⟨g, hg0, hgend, hg⟩ := ih m b
    let N := 2 ^ n
    have hN : 0 < N := by dsimp [N]; positivity
    let F : ℕ → X := fun k => if k < N then f k else g (k - N)
    have hleft (k : ℕ) (hk : k ≤ N) : F k = f k := by
      by_cases hlt : k < N
      · simp [F, hlt]
      · have heq : k = N := by omega
        subst k
        simp [F, hg0, N, hfend]
    have hright (k : ℕ) (hk : N ≤ k) : F k = g (k - N) := by
      simp [F, not_lt.mpr hk]
    have hpow : 2 ^ (n + 1) = N + N := by simp [N, pow_succ, Nat.mul_two]
    refine ⟨F, ?_, ?_, ?_⟩
    · rw [hleft 0 (by omega), hf0]
    · rw [hpow, hright (N + N) (by omega)]
      simpa only [Nat.add_sub_cancel_left, N] using hgend
    · intro k hk
      rw [hpow] at hk
      by_cases hkN : k < N
      · rw [hleft k (by omega), hleft (k + 1) (by omega)]
        have hh := hf k hkN
        rw [ham] at hh
        have he : dist a b / 2 * (1 / 2 : ℝ) ^ n =
            dist a b * (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
        exact hh.trans_eq he
      · rw [hright k (by omega), hright (k + 1) (by omega)]
        have hsub : k + 1 - N = (k - N) + 1 := by omega
        rw [hsub]
        have hh := hg (k - N) (by omega)
        rw [hmb] at hh
        have he : dist a b / 2 * (1 / 2 : ℝ) ^ n =
            dist a b * (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
        exact hh.trans_eq he

private theorem chain_dist_le (f : ℕ → X) {N : ℕ} {δ : ℝ}
    (h : ∀ k < N, dist (f k) (f (k + 1)) ≤ δ) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ N) : dist (f i) (f j) ≤ (j - i : ℕ) * δ := by
  calc
    dist (f i) (f j) ≤ ∑ k ∈ Finset.Ico i j, δ :=
      dist_le_Ico_sum_of_dist_le hij (fun hki hkj => h _ (lt_of_lt_of_le hkj hj))
    _ = (j - i : ℕ) * δ := by simp

theorem exists_metric_segment_of_midpoints [ProperSpace X]
    (hm : ∀ a b : X, ∃ m, dist a m = dist a b / 2 ∧ dist m b = dist a b / 2)
    (a b : X) :
    ∃ f : Icc (0 : ℝ) 1 → X, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  classical
  let D := dist a b
  let δ : ℕ → ℝ := fun n => D * (1 / 2 : ℝ) ^ n
  have hD : 0 ≤ D := dist_nonneg
  have hδ (n : ℕ) : 0 ≤ δ n := mul_nonneg hD (by positivity)
  have hprod (n : ℕ) : (2 ^ n : ℕ) * δ n = D := by
    dsimp only [δ]
    push_cast
    calc
      (2 : ℝ) ^ n * (D * (1 / 2 : ℝ) ^ n) =
          D * ((2 : ℝ) * (1 / 2)) ^ n := by rw [mul_pow]; ring
      _ = D := by norm_num
  choose c hc0 hcend hcstep using fun n => exists_dyadic_chain hm n a b
  let k (n : ℕ) (t : Icc (0 : ℝ) 1) : ℕ := ⌊(t : ℝ) * (2 ^ n : ℕ)⌋₊
  have hk (n : ℕ) (t : Icc (0 : ℝ) 1) : k n t ≤ 2 ^ n := by
    dsimp only [k]
    calc
      ⌊(t : ℝ) * (2 ^ n : ℕ)⌋₊ ≤ ⌊((2 ^ n : ℕ) : ℝ)⌋₊ :=
        Nat.floor_mono (by nlinarith [t.property.2, (show (0 : ℝ) ≤ (2 ^ n : ℕ) from Nat.cast_nonneg _)])
      _ = 2 ^ n := Nat.floor_natCast _
  let g (n : ℕ) (t : Icc (0 : ℝ) 1) := c n (k n t)
  have hball (n : ℕ) (t : Icc (0 : ℝ) 1) : g n t ∈ closedBall a D := by
    have hh := chain_dist_le (c n) (hcstep n) (Nat.zero_le (k n t)) (hk n t)
    rw [hc0 n] at hh
    have hh' : dist a (g n t) ≤ (k n t : ℝ) * δ n := by
      simpa only [g, δ, D, Nat.sub_zero] using hh
    change dist (g n t) a ≤ D
    rw [dist_comm]
    exact hh'.trans ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hk n t)) (hδ n)).trans_eq
      (hprod n))
  have hordered (n : ℕ) (s t : Icc (0 : ℝ) 1) (hst : (s : ℝ) ≤ t) :
      dist (g n s) (g n t) ≤ D * dist s t + δ n := by
    have hks : k n s ≤ k n t :=
      Nat.floor_mono (mul_le_mul_of_nonneg_right hst (Nat.cast_nonneg (2 ^ n)))
    have hslo := Nat.lt_floor_add_one ((s : ℝ) * (2 ^ n : ℕ))
    have hthi := Nat.floor_le (mul_nonneg t.property.1 (Nat.cast_nonneg (2 ^ n)))
    have hdiff : (k n t : ℝ) - (k n s : ℝ) ≤
        ((t : ℝ) - (s : ℝ)) * (2 ^ n : ℕ) + 1 := by
      dsimp only [k]
      nlinarith only [hslo, hthi]
    have hstDist : dist s t = (t : ℝ) - (s : ℝ) := by
      change |(s : ℝ) - (t : ℝ)| = (t : ℝ) - (s : ℝ)
      rw [abs_of_nonpos (sub_nonpos.mpr hst)]
      ring
    have hh := chain_dist_le (c n) (hcstep n) hks (hk n t)
    rw [Nat.cast_sub hks] at hh
    change dist (g n s) (g n t) ≤ _ at hh
    rw [hstDist]
    calc
      dist (g n s) (g n t) ≤ ((k n t : ℝ) - (k n s : ℝ)) * δ n := hh
      _ ≤ (((t : ℝ) - (s : ℝ)) * (2 ^ n : ℕ) + 1) * δ n :=
        mul_le_mul_of_nonneg_right hdiff (hδ n)
      _ = ((t : ℝ) - (s : ℝ)) * ((2 ^ n : ℕ) * δ n) + δ n := by ring
      _ = D * ((t : ℝ) - (s : ℝ)) + δ n := by rw [hprod]; ring
  have hdist (n : ℕ) (s t : Icc (0 : ℝ) 1) :
      dist (g n s) (g n t) ≤ D * dist s t + δ n := by
    rcases le_total (s : ℝ) (t : ℝ) with hst | hts
    · exact hordered n s t hst
    · rw [dist_comm (g n s) (g n t), dist_comm s t]
      exact hordered n t s hts
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hcompact (t : Icc (0 : ℝ) 1) : ∃ x ∈ closedBall a D,
      Tendsto (fun n => g n t) U (𝓝 x) := by
    apply (isCompact_closedBall a D).ultrafilter_le_nhds
      (Ultrafilter.map (fun n => g n t) U)
    apply le_principal_iff.mpr
    change ∀ᶠ n in (U : Filter ℕ), g n t ∈ closedBall a D
    exact Eventually.of_forall (fun n => hball n t)
  choose F hFball hconv using hcompact
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, mul_zero] using (tendsto_const_nhds (x := D)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  let L : ℝ≥0 := ⟨D, hD⟩
  have hLip : LipschitzWith L F := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have hh := le_of_tendsto_of_tendsto ((hconv s).dist (hconv t))
      (tendsto_const_nhds.add (hδlim.mono_left hU))
      (Eventually.of_forall (fun n => hdist n s t))
    change dist (F s) (F t) ≤ D * dist s t
    simpa only [add_zero] using hh
  have hzero : ∀ n, g n ⟨0, by norm_num⟩ = a := by
    intro n
    simpa only [g, k, zero_mul, Nat.floor_zero] using hc0 n
  have hone : ∀ n, g n ⟨1, by norm_num⟩ = b := by
    intro n
    simpa only [g, k, one_mul, Nat.floor_natCast] using hcend n
  have hFzero : F ⟨0, by norm_num⟩ = a :=
    tendsto_nhds_unique (hconv ⟨0, by norm_num⟩)
      (by simpa only [hzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) U (𝓝 a)))
  have hFone : F ⟨1, by norm_num⟩ = b :=
    tendsto_nhds_unique (hconv ⟨1, by norm_num⟩)
      (by simpa only [hone] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => b) U (𝓝 b)))
  refine ⟨F, hLip.continuous, hFzero, hFone, ?_⟩
  apply dist_eq_mul_of_lipschitz_interval F hLip
  rw [hFzero, hFone]
  rfl

theorem exists_midpoint_of_approximate_midpoints [ProperSpace X] (a b : X)
    (h : ∀ ε : ℝ, 0 < ε → ∃ z, dist a z ≤ dist a b / 2 + ε ∧
      dist b z ≤ dist a b / 2 + ε) :
    ∃ z, dist a z = dist a b / 2 ∧ dist z b = dist a b / 2 := by
  classical
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  choose z hza hzb using fun n => h (ε n) (hpos n)
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hevent : ∀ᶠ n in atTop, z n ∈ closedBall a (dist a b / 2 + 1) := by
    filter_upwards [hε.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hn
    change dist (z n) a ≤ dist a b / 2 + 1
    rw [dist_comm]
    exact (hza n).trans (by linarith)
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨m, _, hm⟩ := (isCompact_closedBall a (dist a b / 2 + 1)).ultrafilter_le_nhds
    (Ultrafilter.map z U) (le_principal_iff.mpr (hU hevent))
  change Tendsto z U (𝓝 m) at hm
  have ham : dist a m ≤ dist a b / 2 := by
    have hh := le_of_tendsto_of_tendsto (tendsto_const_nhds.dist hm)
      (tendsto_const_nhds.add (hε.mono_left hU)) (Eventually.of_forall hza)
    simpa only [add_zero] using hh
  have hbm : dist b m ≤ dist a b / 2 := by
    have hh := le_of_tendsto_of_tendsto (tendsto_const_nhds.dist hm)
      (tendsto_const_nhds.add (hε.mono_left hU)) (Eventually.of_forall hzb)
    simpa only [add_zero] using hh
  have htri := dist_triangle a m b
  rw [dist_comm b m] at hbm
  refine ⟨m, ?_, ?_⟩ <;> linarith

theorem exists_metric_segment_of_approximate_midpoints [ProperSpace X]
    (h : ∀ a b : X, ∀ ε : ℝ, 0 < ε → ∃ z, dist a z ≤ dist a b / 2 + ε ∧
      dist b z ≤ dist a b / 2 + ε) (a b : X) :
    ∃ f : Icc (0 : ℝ) 1 → X, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t :=
  exists_metric_segment_of_midpoints
    (fun x y => exists_midpoint_of_approximate_midpoints x y (h x y)) a b

end Metric

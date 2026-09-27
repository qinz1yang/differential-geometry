import DifferentialGeometry.Analysis.ODE.Gronwall.ClosedEdge
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Set Real Filter

open scoped Topology

namespace DifferentialGeometry.Analysis.ODE

theorem mul_sqrt_le_sq_div_four_add (s : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    s * Real.sqrt M ≤ s ^ 2 / 4 + M := by
  nlinarith [sq_nonneg (Real.sqrt M - s / 2), Real.sq_sqrt hM, Real.sqrt_nonneg M]

theorem energy_hierarchy_uniform_bound
    {T c C : ℝ} {M M' : ℕ → ℝ → ℝ} {s B0 : ℕ → ℝ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hMnonneg : ∀ k, ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ M k t)
    (hcont : ∀ k, ContinuousOn (M k) (Icc (0 : ℝ) T))
    (hderiv : ∀ k, ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt (M k) (M' k t) (Ici t) t)
    (hdiss : ∀ k, ∀ t ∈ Ico (0 : ℝ) T,
      M' k t ≤ -c * (M (k + 1) t) + C * (M k t) + s k * Real.sqrt (M k t))
    (hinit : ∀ k, M k 0 ≤ B0 k) :
    ∀ k, ∃ Bound : ℝ, ∀ t ∈ Icc (0 : ℝ) T, M k t ≤ Bound := by
  intro k
  set K : ℝ := C + 1 with hKdef
  set ε : ℝ := (s k) ^ 2 / 4 with hεdef
  refine ⟨gronwallBound (B0 k) K ε T, ?_⟩
  have hf' : ∀ t ∈ Ico (0 : ℝ) T, ∀ r, M' k t < r →
      ∃ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (M k z - M k t) < r := by
    intro t ht r hr
    have := (hderiv k t ht).liminf_right_slope_le hr
    refine this.mono ?_
    intro z hz
    rwa [slope_def_field, div_eq_inv_mul] at hz
  have hbound : ∀ t ∈ Ico (0 : ℝ) T, M' k t ≤ K * M k t + ε := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self ht
    have hMt : 0 ≤ M k t := hMnonneg k t htIcc
    have hMt1 : 0 ≤ M (k + 1) t := hMnonneg (k + 1) t htIcc
    have hneg : -c * (M (k + 1) t) ≤ 0 := by
      have : 0 ≤ c * (M (k + 1) t) := mul_nonneg hc.le hMt1
      linarith
    have hdiss' := hdiss k t ht
    have hyoung : s k * Real.sqrt (M k t) ≤ (s k) ^ 2 / 4 + M k t :=
      mul_sqrt_le_sq_div_four_add (s k) hMt
    rw [hKdef, hεdef]
    nlinarith [hneg, hdiss', hyoung]
  have ha : M k 0 ≤ B0 k := hinit k
  have hgron := le_gronwallBound_of_liminf_deriv_right_le (a := 0) (b := T)
    (hcont k) hf' (by simpa using ha) hbound
  intro t htIcc
  have hKnn : 0 ≤ K := by rw [hKdef]; linarith
  have hεnn : 0 ≤ ε := by rw [hεdef]; positivity
  have hB0nn : 0 ≤ B0 k := le_trans (hMnonneg k 0 (by
      refine ⟨le_refl 0, ?_⟩; exact htIcc.1.trans htIcc.2)) ha
  have hmono : gronwallBound (B0 k) K ε (t - 0) ≤ gronwallBound (B0 k) K ε T := by
    have := gronwallBound_mono (δ := B0 k) (K := K) (ε := ε) hB0nn hεnn hKnn
    have hle : (t - 0) ≤ T := by simpa using htIcc.2
    have := this hle
    simpa using this
  calc M k t ≤ gronwallBound (B0 k) K ε (t - 0) := hgron t htIcc
    _ ≤ gronwallBound (B0 k) K ε T := hmono

private theorem weighted_shift_sum (q : ℝ) (v : ℕ → ℝ) (N : ℕ) :
    q * (∑ n ∈ Finset.range (N + 1), q ^ n * v (n + 1)) =
      (∑ n ∈ Finset.range (N + 1), q ^ n * v n) - v 0 + q ^ (N + 1) * v (N + 1) := by
  induction N with
  | zero => simp
  | succ N h =>
    simp only [Finset.sum_range_succ] at h ⊢
    rw [mul_add, h, pow_succ]
    ring

private theorem hierarchy_zero_first
    {a b K C B R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    {u u' : ℕ → ℝ → ℝ}
    (hnonneg : ∀ n, ∀ t ∈ Icc a b, 0 ≤ u n t)
    (hcont : ∀ n, ContinuousOn (u n) (Icc a b))
    (hderiv : ∀ n, ∀ t ∈ Ioo a b, HasDerivAt (u n) (u' n t) t)
    (hsub : ∀ n, ∀ t ∈ Ioo a b, u' n t ≤ K * u n t + C * u (n + 1) t)
    (hbound : ∀ n, ∀ t ∈ Icc a b, u n t ≤ B * R ^ n)
    (hinit : ∀ n, u n a = 0) : ∀ t ∈ Icc a b, u 0 t = 0 := by
  let q : ℝ := (2 * R)⁻¹
  have hq : 0 < q := inv_pos.mpr (mul_pos (by norm_num) hR)
  have hqR : q * R = (1 / 2 : ℝ) := by dsimp [q]; field_simp
  let e (N : ℕ) (t : ℝ) := ∑ n ∈ Finset.range (N + 1), q ^ n * u n t
  let e' (N : ℕ) (t : ℝ) := ∑ n ∈ Finset.range (N + 1), q ^ n * u' n t
  have hecont (N : ℕ) : ContinuousOn (e N) (Icc a b) :=
    continuousOn_finsetSum _ (fun n _ => continuousOn_const.mul (hcont n))
  have hederiv (N : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (e N) (e' N t) t := by
    have hd := HasDerivAt.sum (u := Finset.range (N + 1))
      (fun n _ => (hderiv n t ht).const_mul (q ^ n))
    have hf : (∑ n ∈ Finset.range (N + 1), fun s => q ^ n * u n s) = e N := by
      funext s
      simp only [Finset.sum_apply, e]
    rw [hf] at hd
    exact hd
  have hezero (N : ℕ) : e N a = 0 := by simp only [e, hinit, mul_zero, Finset.sum_const_zero]
  have hesub (N : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) :
      e' N t ≤ (K + C / q) * e N t + C * B * R * (1 / 2 : ℝ) ^ N := by
    have hsum := Finset.sum_le_sum (s := Finset.range (N + 1))
      (fun n _ => mul_le_mul_of_nonneg_left (hsub n t ht) (pow_nonneg hq.le n))
    have hshift := weighted_shift_sum q (fun n => u n t) N
    have hterm := mul_le_mul_of_nonneg_left (hbound (N + 1) t (Ioo_subset_Icc_self ht))
      (mul_nonneg hC (pow_nonneg hq.le N))
    have hzero := hnonneg 0 t (Ioo_subset_Icc_self ht)
    have hsumEq : (∑ n ∈ Finset.range (N + 1), q ^ n * (K * u n t + C * u (n + 1) t)) =
        K * e N t + C * ∑ n ∈ Finset.range (N + 1), q ^ n * u (n + 1) t := by
      simp only [e, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n _
      ring
    rw [hsumEq] at hsum
    have hnext : C * ∑ n ∈ Finset.range (N + 1), q ^ n * u (n + 1) t ≤
        C / q * e N t + C * q ^ N * u (N + 1) t := by
      have hshift' : q * (∑ n ∈ Finset.range (N + 1), q ^ n * u (n + 1) t) =
          e N t - u 0 t + q ^ (N + 1) * u (N + 1) t := hshift
      rw [pow_succ] at hshift'
      have hCq : 0 ≤ C / q := div_nonneg hC hq.le
      have hm := congrArg (fun z : ℝ => C / q * z) hshift'
      have hcancel : C / q * q = C := div_mul_cancel₀ C hq.ne'
      have hCZ := mul_nonneg hCq hzero
      rw [← mul_assoc, hcancel] at hm
      have ht : C / q * (q ^ N * q * u (N + 1) t) = C * q ^ N * u (N + 1) t := by
        calc _ = (C / q * q) * (q ^ N * u (N + 1) t) := by ring
          _ = _ := by rw [hcancel]; ring
      rw [mul_add, mul_sub, ht] at hm
      linarith
    have hlast : C * q ^ N * (B * R ^ (N + 1)) = C * B * R * (1 / 2 : ℝ) ^ N := by
      rw [pow_succ, ← hqR, mul_pow]
      ring
    rw [mul_assoc, hlast] at hterm
    dsimp only [e']
    calc (∑ n ∈ Finset.range (N + 1), q ^ n * u' n t)
        ≤ K * e N t + C * ∑ n ∈ Finset.range (N + 1), q ^ n * u (n + 1) t := hsum
      _ ≤ K * e N t + (C / q * e N t + C * q ^ N * u (N + 1) t) := add_le_add_right hnext _
      _ ≤ (K + C / q) * e N t + C * B * R * (1 / 2 : ℝ) ^ N := by nlinarith
  intro t ht
  have hupper (N : ℕ) : u 0 t ≤
      gronwallBound 0 (K + C / q) (C * B * R * (1 / 2 : ℝ) ^ N) (t - a) := by
    have hgron := le_gronwallBound_of_hasDerivAt_on_Ioo (hecont N)
      (hederiv N) (le_of_eq (hezero N)) (hesub N) t ht
    have hle : u 0 t ≤ e N t := by
      have h := Finset.single_le_sum
        (fun n (_ : n ∈ Finset.range (N + 1)) => mul_nonneg (pow_nonneg hq.le n) (hnonneg n t ht))
        (show 0 ∈ Finset.range (N + 1) by simp)
      simpa only [pow_zero, one_mul, e] using h
    exact hle.trans hgron
  have hlim : Tendsto (fun N : ℕ => C * B * R * (1 / 2 : ℝ) ^ N) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (C * B * R)
  have hg := (gronwallBound_continuous_ε 0 (K + C / q) (t - a)).tendsto 0 |>.comp hlim
  rw [gronwallBound_ε0_δ0] at hg
  exact le_antisymm (ge_of_tendsto hg (Filter.Eventually.of_forall hupper)) (hnonneg 0 t ht)

theorem energy_hierarchy_eq_zero_of_exponential_bound
    {a b K C B R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    {u u' : ℕ → ℝ → ℝ}
    (hnonneg : ∀ n, ∀ t ∈ Icc a b, 0 ≤ u n t)
    (hcont : ∀ n, ContinuousOn (u n) (Icc a b))
    (hderiv : ∀ n, ∀ t ∈ Ioo a b, HasDerivAt (u n) (u' n t) t)
    (hsub : ∀ n, ∀ t ∈ Ioo a b, u' n t ≤ K * u n t + C * u (n + 1) t)
    (hbound : ∀ n, ∀ t ∈ Icc a b, u n t ≤ B * R ^ n)
    (hinit : ∀ n, u n a = 0) : ∀ n, ∀ t ∈ Icc a b, u n t = 0 := by
  intro n
  have h := hierarchy_zero_first (B := B * R ^ n) (u := fun k => u (k + n))
    (u' := fun k => u' (k + n)) hC hR (fun k => hnonneg (k + n))
    (fun k => hcont (k + n)) (fun k => hderiv (k + n))
    (fun k t ht => by simpa only [Nat.add_right_comm] using hsub (k + n) t ht)
    (fun k t ht => by
      have hb := hbound (k + n) t ht
      rw [pow_add] at hb
      nlinarith [hb]) (fun k => hinit (k + n))
  simpa only [Nat.zero_add] using h

end DifferentialGeometry.Analysis.ODE

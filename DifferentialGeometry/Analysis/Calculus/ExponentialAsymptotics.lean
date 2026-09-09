import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact

open Filter Set
open scoped Topology

namespace Real
theorem tendsto_rpow_mul_exp_neg_div_nhdsGT_zero (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => t ^ a * exp (-c / t)) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-a) c hc).comp
    tendsto_inv_nhdsGT_zero
  apply h.congr
  intro t
  simp only [Function.comp_apply, ← rpow_neg_eq_inv_rpow, neg_neg, div_eq_mul_inv]

theorem exists_rpow_mul_exp_neg_div_bound (a T : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ioc 0 T, t ^ a * exp (-c / t) ≤ C := by
  have hlim := tendsto_rpow_mul_exp_neg_div_nhdsGT_zero a hc
  obtain ⟨δ, hδ, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)))
  have hcont : ContinuousOn (fun t : ℝ => t ^ a * exp (-c / t)) (Icc δ T) := by
    intro t ht
    have ht0 : t ≠ 0 := (hδ.trans_le ht.1).ne'
    exact ((continuousAt_id.rpow_const (Or.inl ht0)).mul
      (continuous_exp.continuousAt.comp (continuousAt_const.div continuousAt_id ht0))).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hcont
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t ht
  by_cases htδ : t < δ
  · exact (hsmall ⟨ht.1, htδ⟩).le.trans (le_max_right _ _)
  · exact (hC (mem_image_of_mem _ ⟨le_of_not_gt htδ, ht.2⟩)).trans (le_max_left _ _)

theorem exists_rpow_mul_exp_neg_div_le_rpow (a b T : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ioc 0 T, ∀ r : ℝ, c ≤ r →
      t ^ a * exp (-r / t) ≤ C * t ^ b := by
  obtain ⟨C, hC, hbound⟩ := exists_rpow_mul_exp_neg_div_bound (a - b) T hc
  refine ⟨C, hC, ?_⟩
  intro t ht r hr
  have he : exp (-r / t) ≤ exp (-c / t) :=
    exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hr) ht.1.le)
  calc
    t ^ a * exp (-r / t) ≤ t ^ a * exp (-c / t) :=
      mul_le_mul_of_nonneg_left he (rpow_nonneg ht.1.le _)
    _ = (t ^ (a - b) * exp (-c / t)) * t ^ b := by
      rw [mul_right_comm, ← rpow_add ht.1]
      rw [sub_add_cancel]
    _ ≤ C * t ^ b := mul_le_mul_of_nonneg_right (hbound t ht) (rpow_nonneg ht.1.le _)

theorem exists_gaussian_commutator_le_rpow (n r T A : ℝ) {c : ℝ}
    (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc 0 T, ∀ e a b d l : ℝ,
      c ≤ e → |a| ≤ A → |b| ≤ A → |d| ≤ A → |l| ≤ A →
      |(4 * Real.pi * t) ^ (-n / 2) * exp (-e / (2 * t)) * a * l +
        2 * ((4 * Real.pi * t) ^ (-n / 2) * exp (-e / (2 * t)) *
          (b - a / (2 * t) * d))| ≤ C * t ^ r := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_rpow_mul_exp_neg_div_le_rpow (-n / 2) r T (half_pos hc)
  obtain ⟨C₁, hC₁, h₁⟩ := exists_rpow_mul_exp_neg_div_le_rpow (-n / 2 - 1) r T (half_pos hc)
  let S := (4 * Real.pi) ^ (-n / 2)
  have hS : 0 ≤ S := rpow_nonneg (by positivity) _
  refine ⟨S * C₀ * A * A + 2 * (S * C₀ * A + S * C₁ * A * A / 2), by positivity, ?_⟩
  intro t ht e a b d l he ha hb hd hl
  let G := (4 * Real.pi * t) ^ (-n / 2) * exp (-e / (2 * t))
  have hG : 0 ≤ G := mul_nonneg (rpow_nonneg (mul_nonneg (by positivity) ht.1.le) _) (exp_pos _).le
  have hG₀ : G ≤ S * C₀ * t ^ r := by
    have hbound := h₀ t ht (e / 2) (by linarith)
    dsimp only [G, S]
    rw [mul_rpow (by positivity) ht.1.le]
    rw [show -e / (2 * t) = -(e / 2) / t by ring]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound hS
  have hG₁ : G / t ≤ S * C₁ * t ^ r := by
    have hbound := h₁ t ht (e / 2) (by linarith)
    dsimp only [G, S]
    rw [mul_rpow (by positivity) ht.1.le]
    rw [show -e / (2 * t) = -(e / 2) / t by ring]
    have heq : ((4 * Real.pi) ^ (-n / 2) * t ^ (-n / 2) * exp (-(e / 2) / t)) / t =
        (4 * Real.pi) ^ (-n / 2) * (t ^ (-n / 2 - 1) * exp (-(e / 2) / t)) := by
      rw [rpow_sub_one ht.1.ne']
      ring
    rw [heq]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound hS
  have htr : 0 ≤ t ^ r := rpow_nonneg ht.1.le r
  change |G * a * l + 2 * (G * (b - a / (2 * t) * d))| ≤ _
  calc
    _ ≤ G * |a| * |l| + 2 * (G * |b| + G / t * |a| * |d| / 2) := by
      have htri := abs_add_le (G * a * l) (2 * (G * (b - a / (2 * t) * d)))
      have hin := abs_sub b (a / (2 * t) * d)
      simp only [abs_mul, abs_of_nonneg hG, abs_of_pos ht.1, abs_div, abs_two] at htri hin
      calc
        _ ≤ G * |a| * |l| + 2 * (G * (|b| + |a| / (2 * t) * |d|)) :=
          htri.trans (add_le_add_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hin hG) (show (0 : ℝ) ≤ 2 by norm_num)) _)
        _ = _ := by ring
    _ ≤ (S * C₀ * t ^ r) * A * A +
        2 * ((S * C₀ * t ^ r) * A + (S * C₁ * t ^ r) * A * A / 2) := by gcongr
    _ = _ := by ring

theorem exists_gaussian_cutoff_commutator_bound (n T A : ℝ) {c : ℝ}
    (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc 0 T, ∀ e a₀ a₁ b₀ b₁ d l : ℝ,
      c ≤ e → |a₀| ≤ A → |a₁| ≤ A → |b₀| ≤ A → |b₁| ≤ A → |d| ≤ A → |l| ≤ A →
      |(4 * Real.pi * t) ^ (-n / 2) * exp (-e / (2 * t)) *
          (a₀ + t * a₁) * l +
        2 * ((4 * Real.pi * t) ^ (-n / 2) * exp (-e / (2 * t)) *
          (b₀ + t * b₁ - (a₀ + t * a₁) / (2 * t) * d))| ≤ C := by
  let B := A + |T| * A
  have hAB : A ≤ B := le_add_of_nonneg_right (mul_nonneg (abs_nonneg T) hA)
  obtain ⟨C, hC, hbound⟩ := exists_gaussian_commutator_le_rpow n 0 T B hc (hA.trans hAB)
  refine ⟨C, hC, ?_⟩
  intro t ht e a₀ a₁ b₀ b₁ d l he ha₀ ha₁ hb₀ hb₁ hd hl
  have hat : |t| ≤ |T| := by rw [abs_of_pos ht.1]; exact ht.2.trans (le_abs_self T)
  have ha : |a₀ + t * a₁| ≤ B := by
    calc
      _ ≤ |a₀| + |t| * |a₁| := by simpa only [abs_mul] using abs_add_le a₀ (t * a₁)
      _ ≤ A + |T| * A := by gcongr
  have hb : |b₀ + t * b₁| ≤ B := by
    calc
      _ ≤ |b₀| + |t| * |b₁| := by simpa only [abs_mul] using abs_add_le b₀ (t * b₁)
      _ ≤ A + |T| * A := by gcongr
  simpa only [rpow_zero, mul_one] using
    hbound t ht e (a₀ + t * a₁) (b₀ + t * b₁) d l he ha hb (hd.trans hAB) (hl.trans hAB)

end Real

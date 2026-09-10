import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace Poincare.Analysis

private theorem exists_bound_deriv_smoothTransition :
    ∃ D : ℝ, 0 < D ∧ ∀ t, |deriv Real.smoothTransition t| ≤ D := by
  have hc : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hd : Continuous (deriv Real.smoothTransition) := hc.continuous_deriv (by simp)
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hd.continuousOn : ContinuousOn (deriv Real.smoothTransition) (Icc (0 : ℝ) 1))
  refine ⟨max D 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t
  by_cases hlo : t < 0
  · have heq : Real.smoothTransition =ᶠ[𝓝 t] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds hlo] with s hs
      exact Real.smoothTransition.zero_of_nonpos hs.le
    rw [heq.deriv_eq, deriv_const, abs_zero]
    exact (zero_le_one.trans (le_max_right _ _))
  by_cases hhi : 1 < t
  · have heq : Real.smoothTransition =ᶠ[𝓝 t] fun _ ↦ 1 := by
      filter_upwards [Ioi_mem_nhds hhi] with s hs
      exact Real.smoothTransition.one_of_one_le hs.le
    rw [heq.deriv_eq, deriv_const, abs_zero]
    exact (zero_le_one.trans (le_max_right _ _))
  exact (show |deriv Real.smoothTransition t| ≤ D from
    hD t ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩).trans (le_max_left _ _)

theorem exists_uniform_smooth_interval_step :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ), a < b →
      ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ Monotone β ∧
        (∀ t, 0 ≤ β t ∧ β t ≤ 1) ∧
        (∀ t, t ≤ a → β t = 0) ∧ (∀ t, b ≤ t → β t = 1) ∧
        ∀ t, |deriv β t| ≤ C / (b - a) := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_deriv_smoothTransition
  refine ⟨C, hC, ?_⟩
  intro a b hab
  have hwidth : 0 < b - a := sub_pos.mpr hab
  let β : ℝ → ℝ := fun t ↦ Real.smoothTransition ((t - a) / (b - a))
  have hs : ContDiff ℝ ∞ β := Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const (b - a))
  refine ⟨β, hs, ?_, fun t ↦ ⟨Real.smoothTransition.nonneg _,
    Real.smoothTransition.le_one _⟩, ?_, ?_, ?_⟩
  · intro s t hst
    exact Real.smoothTransition.monotone
      (div_le_div_of_nonneg_right (sub_le_sub_right hst a) hwidth.le)
  · intro t ht
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hwidth.le)
  · intro t ht
    exact Real.smoothTransition.one_of_one_le
      ((le_div_iff₀ hwidth).mpr (by linarith only [ht]))
  · intro t
    have hd := (((show ContDiff ℝ ∞ Real.smoothTransition from
      Real.smoothTransition.contDiff).differentiable (by simp) _).hasDerivAt).comp t
      (((hasDerivAt_id t).sub_const a).div_const (b - a))
    have heq : deriv β t =
        deriv Real.smoothTransition ((t - a) / (b - a)) * (1 / (b - a)) := hd.deriv
    rw [heq, abs_mul, abs_of_pos (one_div_pos.mpr hwidth)]
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      mul_le_mul_of_nonneg_right (hbound ((t - a) / (b - a))) (inv_nonneg.mpr hwidth.le)

theorem exists_uniform_smooth_interval_cutoff :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b η : ℝ), 0 < η →
      ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
        (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) ∧ tsupport χ ⊆ Icc a b ∧
        (∀ t ∈ Icc (a + η) (b - η), χ t = 1) ∧
        ∀ t, |deriv χ t| ≤ C / η := by
  obtain ⟨D, hD, hbound⟩ := exists_bound_deriv_smoothTransition
  refine ⟨2 * D, by positivity, ?_⟩
  intro a b η hη
  let l : ℝ → ℝ := fun t ↦ Real.smoothTransition ((t - a) / η)
  let r : ℝ → ℝ := fun t ↦ Real.smoothTransition ((b - t) / η)
  let χ : ℝ → ℝ := fun t ↦ l t * r t
  have hl : ContDiff ℝ ∞ l := Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const η)
  have hr : ContDiff ℝ ∞ r := Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub contDiff_id).div_const η)
  have hlb (t : ℝ) : 0 ≤ l t ∧ l t ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hrb (t : ℝ) : 0 ≤ r t ∧ r t ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  refine ⟨χ, hl.mul hr, fun t ↦ ⟨mul_nonneg (hlb t).1 (hrb t).1,
    mul_le_one₀ (hlb t).2 (hrb t).1 (hrb t).2⟩, ?_, ?_, ?_⟩
  · apply closure_minimal _ isClosed_Icc
    intro t ht
    by_contra hout
    have hz : χ t = 0 := by
      rcases not_and_or.mp hout with hlo | hhi
      · have he : l t = 0 := Real.smoothTransition.zero_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le)
        exact mul_eq_zero_of_left he _
      · have he : r t = 0 := Real.smoothTransition.zero_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le)
        exact mul_eq_zero_of_right _ he
    exact ht hz
  · intro t ht
    have he₁ : l t = 1 := Real.smoothTransition.one_of_one_le
      ((le_div_iff₀ hη).mpr (by linarith [ht.1]))
    have he₂ : r t = 1 := Real.smoothTransition.one_of_one_le
      ((le_div_iff₀ hη).mpr (by linarith [ht.2]))
    simp only [χ, he₁, he₂, one_mul]
  · intro t
    have hd (s : ℝ) : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition s) s :=
      ((show ContDiff ℝ ∞ Real.smoothTransition from
        Real.smoothTransition.contDiff).differentiable (by simp) s).hasDerivAt
    have hdl := (hd ((t - a) / η)).comp t (((hasDerivAt_id t).sub_const a).div_const η)
    have hdr := (hd ((b - t) / η)).comp t (((hasDerivAt_id t).const_sub b).div_const η)
    have he : HasDerivAt χ
        (deriv Real.smoothTransition ((t - a) / η) * (1 / η) * r t +
          l t * (deriv Real.smoothTransition ((b - t) / η) * (-1 / η))) t := hdl.mul hdr
    rw [he.deriv]
    have h₁ := hbound ((t - a) / η)
    have h₂ := hbound ((b - t) / η)
    calc
      _ ≤ |deriv Real.smoothTransition ((t - a) / η)| * (1 / η) * r t +
          l t * (|deriv Real.smoothTransition ((b - t) / η)| * (1 / η)) := by
        simpa only [abs_mul, abs_div, abs_one, abs_neg, abs_of_pos hη,
          abs_of_nonneg (hlb t).1, abs_of_nonneg (hrb t).1] using
          abs_add_le (deriv Real.smoothTransition ((t - a) / η) * (1 / η) * r t)
            (l t * (deriv Real.smoothTransition ((b - t) / η) * (-1 / η)))
      _ ≤ D * (1 / η) + D * (1 / η) := add_le_add
        ((mul_le_of_le_one_right (by positivity) (hrb t).2).trans
          (mul_le_mul_of_nonneg_right h₁ (by positivity)))
        ((mul_le_of_le_one_left (by positivity) (hlb t).2).trans
          (mul_le_mul_of_nonneg_right h₂ (by positivity)))
      _ = 2 * D / η := by ring

end Poincare.Analysis

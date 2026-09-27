/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.ConstMulAction

open Set Filter Topology

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def rescale (f : E ≃ₜ E) (t : ℝ) : E ≃ₜ E := by
  classical
  exact if ht : t = 0 then Homeomorph.refl E else
    ((Homeomorph.smulOfNeZero t ht).symm.trans f).trans (Homeomorph.smulOfNeZero t ht)

@[simp]
theorem rescale_zero (f : E ≃ₜ E) : f.rescale 0 = Homeomorph.refl E := by
  simp [rescale]

theorem rescale_apply_of_ne_zero (f : E ≃ₜ E) {t : ℝ} (ht : t ≠ 0) (x : E) :
    f.rescale t x = t • f (t⁻¹ • x) := by
  simp [rescale, ht, Homeomorph.smulOfNeZero_symm_apply]

@[simp]
theorem rescale_one (f : E ≃ₜ E) : f.rescale 1 = f := by
  ext x
  simp [rescale_apply_of_ne_zero f one_ne_zero]

@[simp]
theorem rescale_symm (f : E ≃ₜ E) (t : ℝ) : (f.rescale t).symm = f.symm.rescale t := by
  classical
  by_cases ht : t = 0
  · simp [ht]
  · ext x
    simp [rescale, ht, Homeomorph.smulOfNeZero_symm_apply]

theorem norm_rescale_sub_le (f : E ≃ₜ E) {C : ℝ}
    (hf : ∀ x, ‖f x - x‖ ≤ C) (t : ℝ) (x : E) :
    ‖f.rescale t x - x‖ ≤ |t| * C := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [rescale_apply_of_ne_zero f ht]
    have heq : t • f (t⁻¹ • x) - x = t • (f (t⁻¹ • x) - t⁻¹ • x) := by
      rw [smul_sub, smul_inv_smul₀ ht]
    rw [heq, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hf _) (abs_nonneg _)

theorem continuous_rescale (f : E ≃ₜ E) {C : ℝ} (hf : ∀ x, ‖f x - x‖ ≤ C) :
    Continuous (fun q : ℝ × E => f.rescale q.1 q.2) := by
  rw [continuous_iff_continuousAt]
  intro q
  by_cases hq : q.1 = 0
  · have hb : Tendsto (fun z : ℝ × E => |z.1| * C) (𝓝 q) (𝓝 0) := by
      simpa only [ContinuousAt, hq, abs_zero, zero_mul] using
        (continuous_fst.abs.mul_const C).continuousAt (x := q)
    have hz : Tendsto (fun z : ℝ × E => f.rescale z.1 z.2 - z.2) (𝓝 q) (𝓝 0) :=
      squeeze_zero_norm (fun z => f.norm_rescale_sub_le hf z.1 z.2) hb
    have hh := hz.add (continuous_snd.continuousAt (x := q))
    simpa only [ContinuousAt, sub_add_cancel, zero_add, hq, rescale_zero, refl_apply,
      id_eq] using hh
  · have hc : ContinuousAt (fun z : ℝ × E => z.1 • f (z.1⁻¹ • z.2)) q :=
      continuousAt_fst.smul
        (f.continuous.continuousAt.comp ((continuousAt_fst.inv₀ hq).smul continuousAt_snd))
    apply hc.congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.eventually_ne hq] with z hz
    exact f.rescale_apply_of_ne_zero hz z.2

theorem rescale_apply_zero (f : E ≃ₜ E) (hf : f 0 = 0) (t : ℝ) :
    f.rescale t 0 = 0 := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [rescale_apply_of_ne_zero f ht, smul_zero, hf, smul_zero]

theorem exists_isotopy_of_bounded_displacement (f : E ≃ₜ E) {C : ℝ}
    (hf : ∀ x, ‖f x - x‖ ≤ C) :
    ∃ H : ℝ → E ≃ₜ E,
      Continuous (fun q : ℝ × E => H q.1 q.2) ∧
      Continuous (fun q : ℝ × E => (H q.1).symm q.2) ∧
      H 0 = Homeomorph.refl E ∧ H 1 = f ∧
      (∀ t x, ‖H t x - x‖ ≤ |t| * C) ∧
      (∀ t x, ‖(H t).symm x - x‖ ≤ |t| * C) ∧
      (f 0 = 0 → ∀ t, H t 0 = 0) := by
  have hi (x : E) : ‖f.symm x - x‖ ≤ C := by
    have h := hf (f.symm x)
    rw [f.apply_symm_apply, norm_sub_rev] at h
    exact h
  refine ⟨f.rescale, f.continuous_rescale hf, ?_, f.rescale_zero, f.rescale_one,
    f.norm_rescale_sub_le hf, ?_, f.rescale_apply_zero⟩
  · simpa only [rescale_symm] using f.symm.continuous_rescale hi
  · intro t x
    rw [rescale_symm]
    exact f.symm.norm_rescale_sub_le hi t x

theorem rescale_eq_self_of_le_norm (f : E ≃ₜ E) {R : ℝ}
    (hf : ∀ x, R ≤ ‖x‖ → f x = x) (t : ℝ) {x : E} (hx : |t| * R ≤ ‖x‖) :
    f.rescale t x = x := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [rescale_apply_of_ne_zero f ht]
    have hnorm : |t| * ‖t⁻¹ • x‖ = ‖x‖ := by
      rw [← Real.norm_eq_abs, ← norm_smul, smul_inv_smul₀ ht]
    have hinner : R ≤ ‖t⁻¹ • x‖ := by
      nlinarith [abs_pos.mpr ht]
    rw [hf _ hinner, smul_inv_smul₀ ht]

theorem alexander_trick (f : E ≃ₜ E) {R : ℝ} (hR : 0 ≤ R)
    (hf : EqOn f id (Metric.ball 0 R)ᶜ) :
    ∃ H : ℝ → E ≃ₜ E,
      Continuous (fun q : ℝ × E => H q.1 q.2) ∧
      Continuous (fun q : ℝ × E => (H q.1).symm q.2) ∧
      H 0 = Homeomorph.refl E ∧ H 1 = f ∧
      (∀ t, EqOn (H t) id (Metric.ball 0 R)ᶜ ∧
        EqOn (H t).symm id (Metric.ball 0 R)ᶜ) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, EqOn (H t) id (Metric.ball 0 (t * R))ᶜ ∧
        EqOn (H t).symm id (Metric.ball 0 (t * R))ᶜ) ∧
      (f 0 = 0 → ∀ t, H t 0 = 0) := by
  have hfix (x : E) (hx : R ≤ ‖x‖) : f x = x :=
    hf (by simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hx)
  have hbound (x : E) : ‖f x - x‖ ≤ 2 * R := by
    by_cases hx : R ≤ ‖x‖
    · rw [hfix x hx, sub_self, norm_zero]
      positivity
    · have hfx : ‖f x‖ < R := by
        by_contra h
        have heq : f x = x := f.injective (hfix _ (le_of_not_gt h))
        exact hx (heq ▸ le_of_not_gt h)
      exact (norm_sub_le _ _).trans (by linarith [lt_of_not_ge hx])
  have hibound (x : E) : ‖f.symm x - x‖ ≤ 2 * R := by
    simpa only [f.apply_symm_apply, norm_sub_rev] using hbound (f.symm x)
  let s (t : ℝ) := max 0 (min t 1)
  have hs : Continuous s := continuous_const.max (continuous_id.min continuous_const)
  have hsnonneg (t : ℝ) : 0 ≤ s t := le_max_left _ _
  have hsle (t : ℝ) : s t ≤ 1 := max_le zero_le_one (min_le_right _ _)
  have hsI {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : s t = t := by
    simp only [s, min_eq_left ht.2, max_eq_right ht.1]
  let H (t : ℝ) := f.rescale (s t)
  have hH (t : ℝ) {x : E} (hx : s t * R ≤ ‖x‖) : H t x = x := by
    apply f.rescale_eq_self_of_le_norm hfix
    simpa only [abs_of_nonneg (hsnonneg t)] using hx
  have hHi (t : ℝ) {x : E} (hx : s t * R ≤ ‖x‖) : (H t).symm x = x :=
    (H t).injective (((H t).apply_symm_apply x).trans (hH t hx).symm)
  refine ⟨H, (f.continuous_rescale hbound).comp ((hs.comp continuous_fst).prodMk continuous_snd),
    ?_, ?_, ?_, ?_, ?_, fun h t => f.rescale_apply_zero h (s t)⟩
  · simpa only [H, rescale_symm, Function.comp_def] using (f.symm.continuous_rescale hibound).comp
      ((hs.comp continuous_fst).prodMk continuous_snd)
  · simp [H, s]
  · simp [H, s]
  · intro t
    have hle : s t * R ≤ R := mul_le_of_le_one_left hR (hsle t)
    exact ⟨fun x hx => hH t (hle.trans (by simpa only [mem_compl_iff,
      Metric.mem_ball, dist_zero_right, not_lt] using hx)),
      fun x hx => hHi t (hle.trans (by simpa only [mem_compl_iff,
        Metric.mem_ball, dist_zero_right, not_lt] using hx))⟩
  · intro t ht
    constructor
    · intro x hx
      apply hH t
      simpa only [hsI ht, mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hx
    · intro x hx
      apply hHi t
      simpa only [hsI ht, mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hx

end Homeomorph

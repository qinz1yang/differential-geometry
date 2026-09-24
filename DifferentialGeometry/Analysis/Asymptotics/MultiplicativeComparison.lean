import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem abs_sub_le_of_mul_add_bounds
    {x y A delta e f : ℝ} (hdelta : 0 ≤ delta) (hy : y ≤ A)
    (hxy : x ≤ (1 + delta) * y + e)
    (hyx : y ≤ (1 + delta) * x + f) :
    |x - y| ≤ delta * A + max e f := by
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have hmul := mul_le_mul_of_nonneg_left (h.trans hy) hdelta
    linarith [le_max_right e f]
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hmul := mul_le_mul_of_nonneg_left hy hdelta
    linarith [le_max_left e f]

theorem tendsto_sub_zero_of_mul_add_bounds
    {alpha : Type*} {l : Filter alpha} {f g : alpha → ℝ} {A : ℝ}
    (hbounded : ∀ᶠ i in l, g i ≤ A)
    (hfg : ∀ delta > 0, ∃ e : alpha → ℝ, Tendsto e l (𝓝 0) ∧
      ∀ᶠ i in l, f i ≤ (1 + delta) * g i + e i)
    (hgf : ∀ delta > 0, ∃ e : alpha → ℝ, Tendsto e l (𝓝 0) ∧
      ∀ᶠ i in l, g i ≤ (1 + delta) * f i + e i) :
    Tendsto (fun i => f i - g i) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  let B := max A 0 + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hAB : A ≤ B := by dsimp only [B]; linarith [le_max_left A 0]
  let delta := epsilon / (2 * B)
  have hdelta : 0 < delta := div_pos hepsilon (by positivity)
  have hdeltaB : delta * B = epsilon / 2 := by
    dsimp only [delta]
    field_simp [hB.ne']
  obtain ⟨e, he, hfe⟩ := hfg delta hdelta
  obtain ⟨k, hk, hgk⟩ := hgf delta hdelta
  have hevent : ∀ᶠ i in l, e i < epsilon / 2 :=
    he.eventually (gt_mem_nhds (show (0 : ℝ) < epsilon / 2 by positivity))
  have hkevent : ∀ᶠ i in l, k i < epsilon / 2 :=
    hk.eventually (gt_mem_nhds (show (0 : ℝ) < epsilon / 2 by positivity))
  filter_upwards [hbounded, hfe, hgk, hevent, hkevent] with i hgi hfi hki hei hkei
  have hbound := abs_sub_le_of_mul_add_bounds hdelta.le hgi hfi hki
  have hmul : delta * A ≤ epsilon / 2 := by
    calc
      delta * A ≤ delta * B := mul_le_mul_of_nonneg_left hAB hdelta.le
      _ = epsilon / 2 := hdeltaB
  have herr : max (e i) (k i) < epsilon / 2 := max_lt hei hkei
  have hlt : |f i - g i| < epsilon := by linarith
  simpa only [Real.dist_eq, sub_zero] using hlt

theorem tendsto_abs_sub_zero_of_mul_add_bounds
    {alpha : Type*} {l : Filter alpha} {f g : alpha → ℝ} {A : ℝ}
    (hbounded : ∀ᶠ i in l, g i ≤ A)
    (hfg : ∀ delta > 0, ∃ e : alpha → ℝ, Tendsto e l (𝓝 0) ∧
      ∀ᶠ i in l, f i ≤ (1 + delta) * g i + e i)
    (hgf : ∀ delta > 0, ∃ e : alpha → ℝ, Tendsto e l (𝓝 0) ∧
      ∀ᶠ i in l, g i ≤ (1 + delta) * f i + e i) :
    Tendsto (fun i => |f i - g i|) l (𝓝 0) := by
  simpa only [abs_zero] using
    (tendsto_sub_zero_of_mul_add_bounds hbounded hfg hgf).abs

theorem tendsto_sub_zero_of_mul_add_div_sqrt_bounds
    {alpha : Type*} {l : Filter alpha} {f g t : alpha → ℝ} {A : ℝ}
    (ht : Tendsto t l atTop) (hbounded : ∀ᶠ i in l, g i ≤ A)
    (hfg : ∀ delta > 0, ∃ C : ℝ,
      ∀ᶠ i in l, f i ≤ (1 + delta) * g i + C / Real.sqrt (t i))
    (hgf : ∀ delta > 0, ∃ C : ℝ,
      ∀ᶠ i in l, g i ≤ (1 + delta) * f i + C / Real.sqrt (t i)) :
    Tendsto (fun i => f i - g i) l (𝓝 0) := by
  have hdecay (C : ℝ) : Tendsto (fun i => C / Real.sqrt (t i)) l (𝓝 0) := by
    have hinv : Tendsto (fun i => (Real.sqrt (t i))⁻¹) l (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp ht)
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul C
  apply tendsto_sub_zero_of_mul_add_bounds hbounded
  · intro delta hdelta
    obtain ⟨C, hC⟩ := hfg delta hdelta
    exact ⟨fun i => C / Real.sqrt (t i), hdecay C, hC⟩
  · intro delta hdelta
    obtain ⟨C, hC⟩ := hgf delta hdelta
    exact ⟨fun i => C / Real.sqrt (t i), hdecay C, hC⟩

end DifferentialGeometry.Analysis

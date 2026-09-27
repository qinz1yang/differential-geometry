import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic


set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open scoped Topology


theorem eventually_uniform_on_compact_time_of_weighted_lipschitz
    {α : Type*} (F : ℕ → ℝ → α → ℝ) (F₀ : ℝ → α → ℝ) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) {J : Set ℝ} (hJ : IsCompact J) {B : ℝ} (hB : 0 ≤ B)
    (hLip : ∀ᶠ i in atTop, ∀ s ∈ J, ∀ t ∈ J, ∀ x,
      |F i t x - F i s x| ≤ B * w x * |t - s|)
    (hconv : ∀ t ∈ J, ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x,
      |F i t x - F₀ t x| ≤ ε * w x) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ t ∈ J, ∀ x,
      |F i t x - F₀ t x| ≤ ε * w x := by
  classical
  have hpoint (t : ℝ) (ht : t ∈ J) (x : α) :
      Tendsto (fun i => F i t x) atTop (𝓝 (F₀ t x)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hw1 : 0 < w x + 1 := by linarith [hw x]
    filter_upwards [hconv t ht (ε / (w x + 1)) (div_pos hε hw1)] with i hi
    rw [Real.dist_eq]
    apply (hi x).trans_lt
    rw [div_mul_eq_mul_div, div_lt_iff₀ hw1]
    nlinarith
  have hlimit (s : ℝ) (hs : s ∈ J) (t : ℝ) (ht : t ∈ J) (x : α) :
      |F₀ t x - F₀ s x| ≤ B * w x * |t - s| :=
    le_of_tendsto ((hpoint t ht x).sub (hpoint s hs x)).abs
      (hLip.mono fun i hi => hi s hs t ht x)
  intro ε hε
  let δ : ℝ := ε / (4 * (B + 1))
  have hden : 0 < 4 * (B + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hscale : B * δ ≤ ε / 4 := by
    dsimp only [δ]
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith
  obtain ⟨T, hTJ, hT, hcover⟩ := hJ.elim_finite_subcover_image
    (b := J) (c := fun t => Metric.ball t δ) (fun _ _ => Metric.isOpen_ball)
    (fun t ht => mem_iUnion₂.mpr ⟨t, ht, Metric.mem_ball_self hδ⟩)
  have hfinite : ∀ᶠ i in atTop, ∀ t ∈ T, ∀ x,
      |F i t x - F₀ t x| ≤ (ε / 2) * w x :=
    (Filter.eventually_all_finite hT).mpr fun t ht =>
      hconv t (hTJ ht) (ε / 2) (by positivity)
  filter_upwards [hLip, hfinite] with i hi hnear
  intro t ht x
  obtain ⟨s, hs, hts⟩ := mem_iUnion₂.mp (hcover ht)
  have hdist : |t - s| < δ := by simpa only [Metric.mem_ball, Real.dist_eq] using hts
  have hsmall : B * w x * |t - s| ≤ (ε / 4) * w x := by
    calc
      B * w x * |t - s| = (B * |t - s|) * w x := by ring
      _ ≤ (B * δ) * w x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdist.le hB) (hw x)
      _ ≤ _ := mul_le_mul_of_nonneg_right hscale (hw x)
  have hleft := (hi s (hTJ hs) t ht x).trans hsmall
  have hright : |F₀ s x - F₀ t x| ≤ (ε / 4) * w x := by
    rw [abs_sub_comm]
    exact (hlimit s (hTJ hs) t ht x).trans hsmall
  calc
    |F i t x - F₀ t x| =
        |(F i t x - F i s x) + (F i s x - F₀ s x) + (F₀ s x - F₀ t x)| := by
      congr 1
      ring
    _ ≤ |F i t x - F i s x| + |F i s x - F₀ s x| + |F₀ s x - F₀ t x| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (ε / 4) * w x + (ε / 2) * w x + (ε / 4) * w x :=
      add_le_add (add_le_add hleft (hnear s hs x)) hright
    _ = ε * w x := by ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

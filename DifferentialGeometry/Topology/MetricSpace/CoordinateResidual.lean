import DifferentialGeometry.Analysis.Normed.Lp.CoordinateCorrection
import DifferentialGeometry.Topology.MetricSpace.ResidualCorrection

set_option autoImplicit false

open Set Finset Metric
open scoped BigOperators

namespace Metric

variable {X ι : Type*} [MetricSpace X] [Fintype ι] [Nonempty ι]

theorem exists_residual_correction_of_coordinate_moves
    {f : X → PiLp 1 (fun _ : ι => ℝ)} {x : X} {w : PiLp 1 (fun _ : ι => ℝ)}
    {V : Set X} {t₀ α β : ℝ}
    (hμ : 0 ≤ α - (Fintype.card ι - 1 : ℝ) * β)
    (he : 0 < dist (f x) w)
    (hscale : ∀ i, dist (f x i) (w i) ≤ t₀)
    (hmove : ∀ i (t : ℝ), 0 < t → t ≤ t₀ →
      ∃ y ∈ V, dist x y = t ∧
        (if w i ≤ f x i then α * t ≤ f x i - f y i ∧ f x i - f y i ≤ t
         else α * t ≤ f y i - f x i ∧ f y i - f x i ≤ t) ∧
        ∀ j ≠ i, dist (f y j) (f x j) ≤ β * t) :
    ∃ y ∈ V, dist (f x) w / Fintype.card ι ≤ dist x y ∧
      dist x y ≤ dist (f x) w ∧
      dist (f y) w ≤ (1 - (α - (Fintype.card ι - 1 : ℝ) * β) / Fintype.card ι) *
        dist (f x) w ∧
      (α - (Fintype.card ι - 1 : ℝ) * β) * dist x y ≤ dist (f x) w - dist (f y) w := by
  classical
  obtain ⟨i, _, hi⟩ := exists_max_image univ (fun j => dist (f x j) (w j)) univ_nonempty
  have hmax (j : ι) : dist (f x j) (w j) ≤ dist (f x i) (w i) := hi j (mem_univ j)
  have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsum : dist (f x) w ≤ Fintype.card ι * dist (f x i) (w i) := by
    rw [PiLp.dist_eq_of_L1]
    simpa using sum_le_sum (s := univ) (fun j _ => hmax j)
  have ht : 0 < dist (f x i) (w i) := by nlinarith
  obtain ⟨y, hy, hxy, hselected, hrest⟩ := hmove i _ ht (hscale i)
  have hselected' := Real.dist_le_mul_of_directed_step hselected
  refine ⟨y, hy, ?_, ?_, ?_, ?_⟩
  · rw [hxy]
    exact (div_le_iff₀ hm).mpr (by nlinarith)
  · rw [hxy]
    exact PiLp.dist_apply_le (f x) w i
  · exact PiLp.dist_le_mul_of_largest_coordinate_correction i hμ hmax hselected' hrest
  · rw [hxy]
    linarith [PiLp.dist_le_sub_of_coordinate_correction i hselected' hrest]

theorem paired_correction_constants {m : ℕ} (hm : 1 ≤ m) {δ : ℝ}
    (hδ : 0 < δ) (hδm : δ ≤ 1 / (100 * m)) :
    9 / 10 ≤ 1 - 3 * δ ^ 2 - 6 * (m - 1 : ℝ) * δ ∧
      1 - 3 * δ ^ 2 - 6 * (m - 1 : ℝ) * δ < 1 ∧
      0 ≤ 1 - (1 - 3 * δ ^ 2 - 6 * (m - 1 : ℝ) * δ) / m ∧
      1 - (1 - 3 * δ ^ 2 - 6 * (m - 1 : ℝ) * δ) / m < 1 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hprod : δ * (100 * m) ≤ 1 := (le_div_iff₀ (by positivity)).mp hδm
  have hδ1 : δ ≤ 1 / 100 := by nlinarith
  have hsq : δ ^ 2 ≤ 1 / 10000 := by nlinarith
  have hcross0 : 0 ≤ 6 * (m - 1 : ℝ) * δ := by positivity
  have hcross : 6 * (m - 1 : ℝ) * δ ≤ 6 / 100 := by nlinarith
  have hμ : 9 / 10 ≤ 1 - 3 * δ ^ 2 - 6 * (m - 1 : ℝ) * δ := by linarith
  have hμ1 : 1 - 3 * δ ^ 2 - 6 * (m - 1 : ℝ) * δ < 1 := by nlinarith [sq_pos_of_pos hδ]
  refine ⟨hμ, hμ1, ?_, ?_⟩
  · have : (1 - 3 * δ ^ 2 - 6 * (m - 1 : ℝ) * δ) / m ≤ 1 :=
      (div_le_iff₀ hm0).mpr (by linarith)
    linarith
  · have : 0 < (1 - 3 * δ ^ 2 - 6 * (m - 1 : ℝ) * δ) / m :=
      div_pos (by linarith) hm0
    linarith

theorem exists_preimage_of_coordinate_moves
    {f : X → PiLp 1 (fun _ : ι => ℝ)} {q : X} {w : PiLp 1 (fun _ : ι => ℝ)}
    {r t₀ α β : ℝ} (hα : α ≤ 1) (hβ : 0 ≤ β)
    (hμ : 0 < α - (Fintype.card ι - 1 : ℝ) * β)
    (hcomplete : IsComplete (closedBall q r))
    (hf : ContinuousOn f (closedBall q r))
    (herror : dist (f q) w ≤ (α - (Fintype.card ι - 1 : ℝ) * β) * r)
    (hscale : dist (f q) w ≤ t₀)
    (hmove : ∀ x ∈ closedBall q r, ∀ i (t : ℝ),
      0 < t → t ≤ t₀ → t ≤ dist (f q) w →
      ∃ y : X, dist x y = t ∧
        (if w i ≤ f x i then α * t ≤ f x i - f y i ∧ f x i - f y i ≤ t
         else α * t ≤ f y i - f x i ∧ f y i - f x i ≤ t) ∧
        ∀ j ≠ i, dist (f y j) (f x j) ≤ β * t) :
    ∃ z ∈ closedBall q r, f z = w ∧
      dist q z ≤ dist (f q) w / (α - (Fintype.card ι - 1 : ℝ) * β) := by
  have hm1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hm0 : (0 : ℝ) < Fintype.card ι := by linarith
  have hμ1 : α - (Fintype.card ι - 1 : ℝ) * β ≤ 1 := by
    have := mul_nonneg (sub_nonneg.mpr hm1) hβ
    linarith
  have hρ0 : 0 ≤ 1 - (α - (Fintype.card ι - 1 : ℝ) * β) / Fintype.card ι := by
    have : (α - (Fintype.card ι - 1 : ℝ) * β) / Fintype.card ι ≤ 1 :=
      (div_le_iff₀ hm0).mpr (by linarith)
    linarith
  have hρ1 : 1 - (α - (Fintype.card ι - 1 : ℝ) * β) / Fintype.card ι < 1 := by
    have := div_pos hμ hm0
    linarith
  apply exists_preimage_of_local_residual_correction hμ hρ0 hρ1 hcomplete hf herror
  intro x hx he heq
  obtain ⟨y, _, _, _, hy, hb⟩ := exists_residual_correction_of_coordinate_moves
    (V := univ) hμ.le he
    (t₀ := min t₀ (dist (f q) w))
    (fun i => le_min ((PiLp.dist_apply_le (f x) w i).trans (heq.trans hscale))
      ((PiLp.dist_apply_le (f x) w i).trans heq))
    (fun i t ht hts => by
      obtain ⟨y, hdist, hdir, hrest⟩ := hmove x hx i t ht
        (hts.trans (min_le_left _ _)) (hts.trans (min_le_right _ _))
      exact ⟨y, mem_univ y, hdist, hdir, hrest⟩)
  exact ⟨y, hy, hb⟩

end Metric

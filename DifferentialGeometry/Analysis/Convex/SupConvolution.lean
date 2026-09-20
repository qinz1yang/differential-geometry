import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

noncomputable section

open Set Filter
open scoped NNReal Topology

namespace DifferentialGeometry.Analysis.Convex

variable {X : Type*} [PseudoMetricSpace X]

def supConvolutionOn (s : Set X) (u : X → ℝ) (ε : ℝ) (x : X) : ℝ :=
  sSup ((fun y => u y - dist x y ^ 2 / (2 * ε)) '' s)

private theorem quadratic_penalty_bound {u : X → ℝ} {s : Set X} {K : ℝ≥0}
    (hu : LipschitzOnWith K u s) {ε : ℝ} (hε : 0 < ε) {x : X} (hx : x ∈ s)
    {y : X} (hy : y ∈ s) :
    u y - dist x y ^ 2 / (2 * ε) ≤ u x + ε * (K : ℝ) ^ 2 / 2 := by
  have h := hu.dist_le_mul y hy x hx
  rw [Real.dist_eq, dist_comm y x] at h
  have hval := (le_abs_self (u y - u x)).trans h
  have hquad : (K : ℝ) * dist x y - ε * (K : ℝ) ^ 2 / 2 ≤ dist x y ^ 2 / (2 * ε) := by
    apply (le_div_iff₀ (show 0 < 2 * ε by positivity)).mpr
    nlinarith [sq_nonneg (dist x y - ε * K)]
  linarith

theorem supConvolutionOn_sub_mem_Icc_of_lipschitzOnWith
    {u : X → ℝ} {s : Set X} {K : ℝ≥0} (hu : LipschitzOnWith K u s)
    {ε : ℝ} (hε : 0 < ε) {x : X} (hx : x ∈ s) :
    supConvolutionOn s u ε x - u x ∈ Icc 0 (ε * (K : ℝ) ^ 2 / 2) := by
  have hb : BddAbove ((fun y => u y - dist x y ^ 2 / (2 * ε)) '' s) := by
    refine ⟨u x + ε * (K : ℝ) ^ 2 / 2, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact quadratic_penalty_bound hu hε hx hy
  have hlo : u x ≤ supConvolutionOn s u ε x := by
    have h := le_csSup hb (mem_image_of_mem (fun y => u y - dist x y ^ 2 / (2 * ε)) hx)
    simpa only [dist_self, sq, zero_mul, zero_div, sub_zero, supConvolutionOn] using h
  have hhi : supConvolutionOn s u ε x ≤ u x + ε * (K : ℝ) ^ 2 / 2 := by
    apply csSup_le (Nonempty.image _ ⟨x, hx⟩)
    rintro _ ⟨y, hy, rfl⟩
    exact quadratic_penalty_bound hu hε hx hy
  exact ⟨sub_nonneg.mpr hlo, by linarith⟩

theorem exists_supConvolutionOn_eq_of_isCompact
    {u : X → ℝ} {s : Set X} (hs : IsCompact s) (hne : s.Nonempty)
    (hu : UpperSemicontinuousOn u s) (ε : ℝ) (x : X) :
    ∃ y ∈ s, supConvolutionOn s u ε x = u y - dist x y ^ 2 / (2 * ε) := by
  have hc : Continuous (fun y => -(dist x y ^ 2 / (2 * ε))) := by fun_prop
  have hsc : UpperSemicontinuousOn (fun y => u y - dist x y ^ 2 / (2 * ε)) s := by
    simpa only [sub_eq_add_neg] using hu.add (hc.upperSemicontinuous.upperSemicontinuousOn s)
  obtain ⟨y, hy, hm⟩ := hsc.exists_isMaxOn hne hs
  refine ⟨y, hy, le_antisymm ?_ ?_⟩
  · exact csSup_le (hne.image _) (by rintro _ ⟨z, hz, rfl⟩; exact hm hz)
  · exact le_csSup (hsc.bddAbove_of_isCompact hs) (mem_image_of_mem _ hy)

theorem dist_le_of_supConvolutionOn_eq
    {u : X → ℝ} {s : Set X} {K : ℝ≥0} (hu : LipschitzOnWith K u s)
    {ε : ℝ} (hε : 0 < ε) {x y : X} (hx : x ∈ s) (hy : y ∈ s)
    (hmax : supConvolutionOn s u ε x = u y - dist x y ^ 2 / (2 * ε)) :
    dist x y ≤ 2 * ε * K := by
  have hlo := (supConvolutionOn_sub_mem_Icc_of_lipschitzOnWith hu hε hx).1
  rw [hmax] at hlo
  have h := hu.dist_le_mul y hy x hx
  rw [Real.dist_eq, dist_comm y x] at h
  have hval := (le_abs_self (u y - u x)).trans h
  have hpen : dist x y ^ 2 / (2 * ε) ≤ K * dist x y := by linarith
  have hmul := (div_le_iff₀ (show 0 < 2 * ε by positivity)).mp hpen
  by_cases hd : dist x y = 0
  · rw [hd]
    positivity
  · apply (mul_le_mul_iff_right₀ (lt_of_le_of_ne dist_nonneg (Ne.symm hd))).mp
    nlinarith [hmul]

private theorem bddAbove_quadratic_penalty
    {u : X → ℝ} {s : Set X} (hu : BddAbove (u '' s)) {ε : ℝ} (hε : 0 < ε) (x : X) :
    BddAbove ((fun y => u y - dist x y ^ 2 / (2 * ε)) '' s) := by
  obtain ⟨C, hC⟩ := hu
  refine ⟨C, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (sub_le_self _ (div_nonneg (sq_nonneg _) (by positivity))).trans (hC (mem_image_of_mem u hy))

theorem convexOn_supConvolutionOn_add_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u : E → ℝ} {s : Set E} (hs : s.Nonempty) (hu : BddAbove (u '' s))
    {ε : ℝ} (hε : 0 < ε) :
    ConvexOn ℝ univ (fun x => supConvolutionOn s u ε x + ‖x‖ ^ 2 / (2 * ε)) := by
  have hid (x y : E) : u y - dist x y ^ 2 / (2 * ε) + ‖x‖ ^ 2 / (2 * ε) =
      u y + inner ℝ x y / ε - ‖y‖ ^ 2 / (2 * ε) := by
    rw [dist_eq_norm, norm_sub_sq_real]
    field_simp
    ring
  have hle (x : E) {y : E} (hy : y ∈ s) :
      u y + inner ℝ x y / ε - ‖y‖ ^ 2 / (2 * ε) ≤
        supConvolutionOn s u ε x + ‖x‖ ^ 2 / (2 * ε) := by
    rw [← hid x y]
    exact add_le_add (le_csSup (bddAbove_quadratic_penalty hu hε x)
      (mem_image_of_mem _ hy)) le_rfl
  refine ⟨convex_univ, ?_⟩
  intro x hx z hz a b ha hb hab
  simp only [smul_eq_mul]
  apply le_sub_iff_add_le.mp
  apply csSup_le (hs.image _)
  rintro _ ⟨y, hy, rfl⟩
  have hlin : u y + inner ℝ (a • x + b • z) y / ε - ‖y‖ ^ 2 / (2 * ε) =
      a * (u y + inner ℝ x y / ε - ‖y‖ ^ 2 / (2 * ε)) +
        b * (u y + inner ℝ z y / ε - ‖y‖ ^ 2 / (2 * ε)) := by
    simp only [inner_add_left, real_inner_smul_left]
    calc
      _ = (a + b) * (u y - ‖y‖ ^ 2 / (2 * ε)) +
          a * (inner ℝ x y / ε) + b * (inner ℝ z y / ε) := by rw [hab]; ring
      _ = _ := by ring
  have hsum := add_le_add (mul_le_mul_of_nonneg_left (hle x hy) ha)
    (mul_le_mul_of_nonneg_left (hle z hy) hb)
  rw [← hlin, ← hid (a • x + b • z) y] at hsum
  linarith

theorem isLocalMax_sub_translate_of_supConvolutionOn
    {E : Type*} [NormedAddCommGroup E] {u φ : E → ℝ} {s : Set E}
    (hu : BddAbove (u '' s)) {ε : ℝ} (hε : 0 < ε) {x y : E}
    (hy : y ∈ interior s)
    (hmax : supConvolutionOn s u ε x = u y - dist x y ^ 2 / (2 * ε))
    (hφ : IsLocalMax (fun z => supConvolutionOn s u ε z - φ z) x) :
    IsLocalMax (fun z => u z - φ (x + (z - y))) y := by
  have ht : Tendsto (fun z : E => x + (z - y)) (𝓝 y) (𝓝 x) := by
    have hc : Continuous (fun z : E => x + (z - y)) := by fun_prop
    simpa only [sub_self, add_zero] using hc.tendsto y
  have hevent := ht hφ
  filter_upwards [hevent, isOpen_interior.mem_nhds hy] with z hz hzmem
  have hdist : dist (x + (z - y)) z = dist x y := by
    simp only [dist_eq_norm]
    congr 1
    abel
  have hle : u z - dist x y ^ 2 / (2 * ε) ≤ supConvolutionOn s u ε (x + (z - y)) := by
    have h := le_csSup (bddAbove_quadratic_penalty hu hε (x + (z - y)))
      (mem_image_of_mem (fun w => u w - dist (x + (z - y)) w ^ 2 / (2 * ε))
        (interior_subset hzmem))
    simpa only [hdist, supConvolutionOn] using h
  change supConvolutionOn s u ε (x + (z - y)) - φ (x + (z - y)) ≤
    supConvolutionOn s u ε x - φ x at hz
  change u z - φ (x + (z - y)) ≤ u y - φ (x + (y - y))
  rw [hmax] at hz
  rw [sub_self, add_zero]
  linarith

end DifferentialGeometry.Analysis.Convex

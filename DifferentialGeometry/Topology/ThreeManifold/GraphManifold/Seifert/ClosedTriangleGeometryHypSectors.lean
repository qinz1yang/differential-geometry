import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypPatches
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatSectors

/-!
# Angle domains in the vertex discs of a hyperbolic closed triangle fold

Lane B3c (design `docs/geometrization/handoffs/20261004-design-b3c-hyperbolic-rows.md`, §3; the
hyperbolic analogue of B3's `ClosedTriangleGeometryFlatSectors`). On the unit disc the side
functions are positive multiples of the imaginary parts of CF's rotated Möbius coordinates
(`HypFold.rotOne_im_mul_normSq`, `HypFold.rotOne_rot_im_mul_normSq`,
`HypFold.wallSide_two_eq_rotTwo`, `HypFold.rotTwo_rot_im_mul_normSq`,
`HypFold.wallSide_one_eq_neg_im`), so the signs of the two walls through a vertex give the sector of
its coordinate (`im_rotOne_pos`, …). Hence the main set meets each vertex disc only in the good
sector of that vertex, where the apex angle lies in `(-π/2, 3π/2)`: `-θ₁/2 < arg rotOne < 3θ₁/2` in
`discOne` (`sector_one`), the same for `rotTwo` in `discTwo` (`sector_two`) and for `z` in
`discThree` (`sector_three`); the patches give the wedges of their definitions or are excluded by
their image conditions (`re_f_of_mem_discOne`, `re_f_of_mem_discTwo`, `norm_f_of_mem_discThree`).
-/

set_option autoImplicit false

noncomputable section

open Set Complex
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

namespace ClosedTriangle

namespace Hyp

open TwoConeFold

variable {σ : CompactShape} {D : σ.FoldData} (hσ : σ.curv = .hyperbolic)
include hσ

omit hσ in
theorem one_sub_sideTan_sq_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : 0 < 1 - t ^ 2 := by
  nlinarith

theorem im_rotOne_pos {z : ℂ} (hz : ‖z‖ < 1) (h : 0 < σ.wallSide 1 z) :
    0 < (σ.rotOne z).im := by
  have e := HypFold.rotOne_im_mul_normSq hσ hz
  have hp := HypFold.normSq_pos_of_ne (HypFold.one_sub_conj_vertexOne_mul_ne_zero hσ hz)
  have ht := one_sub_sideTan_sq_pos (HypFold.sideOneThree_pos hσ)
    (HypFold.sideOneThree_lt_one hσ)
  by_contra hn
  rw [not_lt] at hn
  nlinarith [mul_pos ht h]

theorem im_rotTwo_pos {z : ℂ} (hz : ‖z‖ < 1) (h : 0 < σ.wallSide 2 z) :
    0 < (σ.rotTwo z).im := by
  have e := HypFold.wallSide_two_eq_rotTwo hσ z
  have hp := HypFold.normSq_pos_of_ne (HypFold.one_sub_vertexTwo_mul_ne_zero hσ hz)
  by_contra hn
  rw [not_lt] at hn
  nlinarith

theorem im_rot_rotTwo_neg {z : ℂ} (hz : ‖z‖ < 1) (h : 0 < σ.wallSide 0 z) :
    (exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im < 0 := by
  have e := HypFold.rotTwo_rot_im_mul_normSq hσ z
  have hp := HypFold.normSq_pos_of_ne (HypFold.one_sub_vertexTwo_mul_ne_zero hσ hz)
  have ht := one_sub_sideTan_sq_pos (HypFold.sideTwoThree_pos hσ)
    (HypFold.sideTwoThree_lt_one hσ)
  by_contra hn
  rw [not_lt] at hn
  nlinarith [mul_pos ht h]

theorem im_rot_rotOne_neg {z : ℂ} (hz : ‖z‖ < 1) (h : 0 < σ.wallSide 2 z) :
    (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im < 0 := by
  have e := HypFold.rotOne_rot_im_mul_normSq hσ hz
  have h2 := im_rotTwo_pos hσ hz h
  have hs0 := HypFold.sideOneTwo_pos hσ
  have hs1 := HypFold.sideOneTwo_lt_one hσ
  have hne : (1 : ℂ) - (HypFold.sideOneTwo σ : ℂ) * σ.rotTwo z ≠ 0 := by
    intro h0
    have hn := HypFold.norm_rotTwo_lt_one hσ hz
    have : (HypFold.sideOneTwo σ : ℂ) * σ.rotTwo z = 1 := by linear_combination -h0
    have := congrArg norm this
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le, norm_one] at this
    nlinarith [norm_nonneg (σ.rotTwo z)]
  have hp := HypFold.normSq_pos_of_ne hne
  have ht := one_sub_sideTan_sq_pos hs0 hs1
  by_contra hn
  rw [not_lt] at hn
  nlinarith [mul_pos ht h2]

omit hσ in
theorem im_rot_three_neg {z : ℂ} (h : 0 < σ.wallSide 1 z) :
    (exp (-((σ.θ₃ : ℂ) * I)) * z).im < 0 := by
  have := HypFold.wallSide_one_eq_neg_im (σ := σ) z
  linarith

theorem re_f_of_mem_discOne {z : ℂ} (hd : z ∈ discOne D) : 1 ≤ (D.f z).re := by
  rw [(f_of_mem_discOne hσ hd).2]
  have hn : ‖σ.rotOne z‖ ≤ 1 / 2 := (le_of_lt hd.2).trans (radOne_le_half D)
  have hp : ‖σ.rotOne z ^ σ.p₁ / 2‖ ≤ 1 / 2 := by
    rw [norm_div, norm_pow, Complex.norm_two]
    have : ‖σ.rotOne z‖ ^ σ.p₁ ≤ 1 := pow_le_one₀ (norm_nonneg _) (by linarith)
    linarith
  have := abs_le.mp ((abs_re_le_norm _).trans hp)
  simp only [div_ofNat_re] at this
  rw [add_re]
  norm_num
  linarith [this.1]

theorem re_f_of_mem_discTwo {z : ℂ} (hd : z ∈ discTwo D) : (D.f z).re ≤ -1 := by
  rw [(f_of_mem_discTwo hσ hd).2]
  have hn : ‖σ.rotTwo z‖ ≤ 1 / 2 := (le_of_lt hd.2).trans (radTwo_le_half D)
  have hp : ‖σ.rotTwo z ^ σ.p₂ / 2‖ ≤ 1 / 2 := by
    rw [norm_div, norm_pow, Complex.norm_two]
    have : ‖σ.rotTwo z‖ ^ σ.p₂ ≤ 1 := pow_le_one₀ (norm_nonneg _) (by linarith)
    linarith
  have := abs_le.mp ((abs_re_le_norm _).trans hp)
  simp only [div_ofNat_re] at this
  rw [add_re]
  norm_num
  linarith [this.2]

omit hσ in
theorem norm_f_of_mem_discThree {z : ℂ} (hd : z ∈ discThree D) (h0 : z ≠ 0) :
    3 ≤ ‖D.f z‖ := by
  rw [(f_of_mem_discThree hd h0).2, compactOuterGerm, norm_neg, norm_mul, Complex.norm_real,
    norm_pow, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm,
    div_self (norm_ne_zero_iff.mpr h0), one_pow, mul_one]
  have hn : ‖z‖ ^ σ.p₃ ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) ((le_of_lt hd).trans (by linarith [radThree_le_half D]))
  rw [Real.norm_of_nonneg (by linarith)]
  linarith

theorem sector_one {z : ℂ} (hm : z ∈ mainSet D) (hd : z ∈ discOne D) :
    σ.rotOne z ≠ 0 ∧ -(σ.θ₁ / 2) < arg (σ.rotOne z) ∧ arg (σ.rotOne z) < 3 * σ.θ₁ / 2 := by
  have hnd : ¬ radOne D < ‖σ.rotOne z‖ := not_lt.mpr (le_of_lt hd.2)
  have hθ := σ.θ₁_pos
  rcases hm with ((h | h) | h) | h
  · obtain ⟨hne, a, b⟩ := arg_mem_of_sides σ.θ₁_pos σ.θ₁_le (im_rotOne_pos hσ hd.1 (h.2 1))
      (im_rot_rotOne_neg hσ hd.1 (h.2 2))
    exact ⟨hne, by linarith, by linarith⟩
  · exfalso
    have := re_f_of_mem_discOne hσ hd
    linarith [h.2.2.2.2.2.1]
  · rcases h.2.2.2.2.2.2.1 with h' | h'
    · exact absurd h' hnd
    · obtain ⟨hne, a, b⟩ := arg_of_wedge h'
      exact ⟨hne, a, by linarith⟩
  · rcases h.2.2.2.2.2.2.2.2.1 with h' | h'
    · exact absurd h' hnd
    · obtain ⟨hne, a, b⟩ := arg_of_rot_wedge σ.θ₁_pos σ.θ₁_le h'
      exact ⟨hne, by linarith, b⟩

theorem sector_two {z : ℂ} (hm : z ∈ mainSet D) (hd : z ∈ discTwo D) :
    σ.rotTwo z ≠ 0 ∧ -(σ.θ₂ / 2) < arg (σ.rotTwo z) ∧ arg (σ.rotTwo z) < 3 * σ.θ₂ / 2 := by
  have hnd : ¬ radTwo D < ‖σ.rotTwo z‖ := not_lt.mpr (le_of_lt hd.2)
  have hθ := σ.θ₂_pos
  rcases hm with ((h | h) | h) | h
  · obtain ⟨hne, a, b⟩ := arg_mem_of_sides σ.θ₂_pos σ.θ₂_le (im_rotTwo_pos hσ hd.1 (h.2 2))
      (im_rot_rotTwo_neg hσ hd.1 (h.2 0))
    exact ⟨hne, by linarith, by linarith⟩
  · rcases h.2.2.2.2.2.2.1 with h' | h'
    · exact absurd h' hnd
    · obtain ⟨hne, a, b⟩ := arg_of_rot_wedge σ.θ₂_pos σ.θ₂_le h'
      exact ⟨hne, by linarith, b⟩
  · exfalso
    have := re_f_of_mem_discTwo hσ hd
    linarith [h.2.2.2.2.2.1]
  · rcases h.2.2.2.2.2.2.2.2.2 with h' | h'
    · exact absurd h' hnd
    · obtain ⟨hne, a, b⟩ := arg_of_wedge h'
      exact ⟨hne, a, by linarith⟩

theorem sector_three {z : ℂ} (hm : z ∈ mainSet D) (hd : z ∈ discThree D) :
    z ≠ 0 ∧ -(σ.θ₃ / 2) < arg z ∧ arg z < 3 * σ.θ₃ / 2 := by
  have hnd : ¬ radThree D < ‖z‖ := not_lt.mpr (le_of_lt hd)
  have hθ := σ.θ₃_pos
  rcases hm with ((h | h) | h) | h
  · obtain ⟨hne, a, b⟩ := arg_mem_of_sides σ.θ₃_pos σ.θ₃_le (h.2 0) (im_rot_three_neg (h.2 1))
    exact ⟨hne, by linarith, by linarith⟩
  · rcases h.2.2.2.2.2.2.2 with h' | h'
    · exact absurd h' hnd
    · obtain ⟨hne, a, b⟩ := arg_of_wedge h'
      exact ⟨hne, a, by linarith⟩
  · rcases h.2.2.2.2.2.2.2 with h' | h'
    · exact absurd h' hnd
    · obtain ⟨hne, a, b⟩ := arg_of_rot_wedge σ.θ₃_pos σ.θ₃_le h'
      exact ⟨hne, by linarith, b⟩
  · exfalso
    have h0 : z ≠ 0 := by
      intro h0
      have := h.2.1
      rw [h0, σ.wallSide_zero_eq, zero_im] at this
      linarith [kap_pos D hσ]
    have h3 := norm_f_of_mem_discThree hd h0
    have h4 := h.2.2.2.2.2.2.2.1
    rw [normSq_eq_norm_sq] at h4
    nlinarith [norm_nonneg (D.f z)]

end Hyp

end ClosedTriangle

end GC.Seifert

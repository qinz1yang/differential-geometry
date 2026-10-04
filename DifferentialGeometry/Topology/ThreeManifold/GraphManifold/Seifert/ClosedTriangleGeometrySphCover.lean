import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphSectors

/-!
# The spherical base layout: cover of the triangle and existence

Lane B3d2 (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §5, with
review 32 §5.4; the spherical analogue of B3c's `ClosedTriangleGeometryHypCover`). Every point of
the spherical triangle other than the outer vertex lies in the main set or in a vertex disc
(`cover`): interior points are in the open triangle, the vertices `v₁`, `v₂` are the centres of
their discs, and every other point of wall `i` satisfies all conditions of patch `i` strictly.
Indeed the two other side functions vanish together with `wᵢ` only at the vertices of the wall,
the gauges have positive real part on the triangle, the wall images of `f` come from CF's generic
wall facts, the rotated coordinates of the wall's vertices are positive real multiples of the
wedge axes (`mem_wedge_of_real`), `rᵢ` fixes the wall, and on wall 2 the gauge defect is exactly
`2 arg (1 + v₂ v₁)` (`psiS_sub_psiS_of_wall`, since there `1 + w̄₁ w = 1 + t₁₂ rotTwo z > 0`).
No uniform margin is used. In the coordinate of `v₂` the vertex `v₁` lies on the axis of wall 2
(`rotTwo_vertexOne_real`). Collecting the fields of `SphDiscs`, `SphPatches` and `SphSectors`
gives a base layout for every spherical datum (`exists_sphLayout`).
-/

set_option autoImplicit false

noncomputable section

open Set Complex
open scoped ComplexConjugate

namespace GC.Seifert

namespace ClosedTriangle

namespace Sph

namespace Lay

open TwoConeFold

variable (K : SphDatum)

section Walls

theorem mem_wedge_of_real {w : ℂ} {a : ℝ} (ha : 0 < a) (hw : w ≠ 0) (hre : 0 ≤ w.re)
    (him : w.im = 0) : w ∈ wedgeSet a :=
  ⟨hw, by rw [arg_eq_zero_iff.mpr ⟨hre, him⟩, abs_zero]; exact ha⟩

theorem re_exp_neg_mul (θ : ℝ) (w : ℂ) :
    (exp (-((θ : ℂ) * I)) * w).re = Real.cos θ * w.re + Real.sin θ * w.im := by
  rw [CompactShape.exp_neg_ofReal_mul_I_sph, mul_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
    Real.cos_neg, Real.sin_neg]
  ring

theorem eq_zero_of_walls {z : ℂ} (h0 : K.σ.wallSide 0 z = 0) (h1 : K.σ.wallSide 1 z = 0) :
    z = 0 := by
  rw [K.σ.wallSide_one_eq] at h1
  rw [K.σ.wallSide_zero_eq] at h0
  rw [h0, mul_zero, sub_zero] at h1
  have hr : z.re = 0 := (mul_eq_zero.mp h1).resolve_left K.σ.sin_θ₃_pos.ne'
  exact Complex.ext (by rw [hr, zero_re]) (by rw [h0, zero_im])

theorem pos_of_ne {x : ℝ} (h : 0 ≤ x) (hne : x ≠ 0) : 0 < x := lt_of_le_of_ne h (Ne.symm hne)

theorem mem_discOne_vertexOne : K.σ.vertexOne ∈ discOneR K (radOne K) := by
  refine ⟨ne_of_re_pos
    (re_pos_of_triangle K (CompactShape.vertexOne_mem_triangle_sph K.hσ)).1, ?_⟩
  rw [CompactShape.rotOne_vertexOne_sph K.hσ, norm_zero]
  exact radOne_pos K

theorem mem_discTwo_vertexTwo : K.σ.vertexTwo ∈ discTwoR K (radTwo K) := by
  refine ⟨ne_of_re_pos
    (re_pos_of_triangle K (CompactShape.vertexTwo_mem_triangle_sph K.hσ)).2, ?_⟩
  rw [CompactShape.rotTwo_vertexTwo_sph K.hσ, norm_zero]
  exact radTwo_pos K

theorem im_rotTwo_eq_zero {z : ℂ} (hz : z ∈ K.σ.triangle) (hw : K.σ.wallSide 2 z = 0) :
    (K.σ.rotTwo z).im = 0 := by
  have e := CompactShape.wallSide_two_eq_sph K.hσ z
  have hp := normSq_vertexTwo_pos K (re_pos_of_triangle K hz).2
  rw [hw] at e
  exact (mul_eq_zero.mp e.symm).resolve_right hp.ne'

theorem goodZero_of_wall {z : ℂ} (hz : z ∈ K.σ.triangle) (hw : K.σ.wallSide 0 z = 0)
    (h0 : z ≠ 0) (h2 : z ≠ K.σ.vertexTwo) : goodZero K z := by
  have hre := re_pos_of_triangle K hz
  have hw1 : 0 < K.σ.wallSide 1 z :=
    pos_of_ne (hz.2 1) fun e => h0 (eq_zero_of_walls K hw e)
  have hw2 : 0 < K.σ.wallSide 2 z :=
    pos_of_ne (hz.2 2) fun e => h2 (K.σ.eq_vertexTwo_of_wallZero hz hw e)
  have hμ := sphMu_pos K
  refine ⟨hw1, hw2, hre.1, hre.2, (K.D.re_f_wallZero ⟨hz, hw⟩ h0 h2).2, ?_, Or.inr ?_,
    Or.inr ?_⟩
  · rw [show z.im = 0 from hw, abs_zero]
    linarith
  · have hne := rotTwo_ne_zero K (ne_of_re_pos hre.2) h2
    refine mem_wedge_of_real (by linarith [K.σ.θ₂_pos])
      (mul_ne_zero (Complex.exp_ne_zero _) hne) ?_ ?_
    · rw [re_exp_neg_mul]
      exact add_nonneg (mul_nonneg K.σ.cos_θ₂_nonneg (CompactShape.re_rotTwo_nonneg_sph K.hσ hz))
        (mul_nonneg K.σ.sin_θ₂_pos.le (CompactShape.sector_two_sph K.hσ hz).1)
    · rw [im_exp_neg_mul]
      have e := CompactShape.wallSide_zero_eq_rotTwo_sph K.hσ z
      have hp := normSq_vertexTwo_pos K hre.2
      rw [hw, zero_mul] at e
      rw [(mul_eq_zero.mp e.symm).resolve_right hp.ne', neg_zero]
  · exact mem_wedge_of_real (by linarith [K.σ.θ₃_pos]) h0
      (CompactShape.re_nonneg_of_mem_sph K.hσ hz) hw

theorem goodOne_of_wall {z : ℂ} (hz : z ∈ K.σ.triangle) (hw : K.σ.wallSide 1 z = 0)
    (h0 : z ≠ 0) (h1 : z ≠ K.σ.vertexOne) : goodOne K z := by
  have hre := re_pos_of_triangle K hz
  have hw0 : 0 < K.σ.wallSide 0 z :=
    pos_of_ne (hz.2 0) fun e => h0 (eq_zero_of_walls K e hw)
  have hw2 : 0 < K.σ.wallSide 2 z :=
    pos_of_ne (hz.2 2) fun e => h1 (K.σ.eq_vertexOne_of_wallOne hz hw e)
  refine ⟨hw0, hw2, hre.1, hre.2, (K.D.re_f_wallOne ⟨hz, hw⟩ h0 h1).1, Or.inr ?_, Or.inr ?_⟩
  · refine mem_wedge_of_real (by linarith [K.σ.θ₁_pos])
      (rotOne_ne_zero K (ne_of_re_pos hre.1) h1) (CompactShape.re_rotOne_nonneg_sph K.hσ hz) ?_
    have e := CompactShape.wallSide_one_eq_rotOne_sph K.hσ z
    have hp : 0 < normSq (1 + conj K.σ.vertexOne * z) := normSq_pos.mpr (ne_of_re_pos hre.1)
    rw [hw, zero_mul] at e
    exact (mul_eq_zero.mp e.symm).resolve_right hp.ne'
  · refine mem_wedge_of_real (by linarith [K.σ.θ₃_pos])
      (mul_ne_zero (Complex.exp_ne_zero _) h0) ?_ ?_
    · rw [re_exp_neg_mul]
      exact add_nonneg (mul_nonneg K.σ.cos_θ₃_nonneg (CompactShape.re_nonneg_of_mem_sph K.hσ hz))
        (mul_nonneg K.σ.sin_θ₃_pos.le (CompactShape.im_nonneg_of_mem_sph K.hσ hz))
    · rw [im_exp_neg_mul]
      change -K.σ.wallSide 1 z = 0
      rw [hw, neg_zero]

theorem one_add_mul_rotTwo_pos {z : ℂ} (hz : z ∈ K.σ.triangle) :
    0 < (1 + (K.σ.sphTOneTwo : ℂ) * K.σ.rotTwo z).re := by
  rw [add_re, one_re, re_ofReal_mul]
  have := mul_nonneg (CompactShape.tOneTwo_pos_sph K.hσ).le
    (CompactShape.re_rotTwo_nonneg_sph K.hσ hz)
  linarith

theorem goodTwo_of_wall {z : ℂ} (hz : z ∈ K.σ.triangle) (hw : K.σ.wallSide 2 z = 0)
    (h0 : z ≠ 0) (h1 : z ≠ K.σ.vertexOne) (h2 : z ≠ K.σ.vertexTwo) : goodTwo K z := by
  have hre := re_pos_of_triangle K hz
  have hw0 : 0 < K.σ.wallSide 0 z :=
    pos_of_ne (hz.2 0) fun e => h2 (K.σ.eq_vertexTwo_of_wallZero hz e hw)
  have hw1 : 0 < K.σ.wallSide 1 z :=
    pos_of_ne (hz.2 1) fun e => h1 (K.σ.eq_vertexOne_of_wallOne hz e hw)
  have hf := K.D.re_f_wallTwo ⟨hz, hw⟩ h1 h2
  have hfi := K.D.im_f_of_wall ⟨hz, hw⟩ h0
  have him := im_rotTwo_eq_zero K hz hw
  refine ⟨hw0, hw1, hre.1, hre.2, hf.1, hf.2, ?_, Or.inr ?_, Or.inr ?_⟩
  · rw [normSq_apply, hfi, mul_zero, add_zero]
    nlinarith [hf.1, hf.2]
  · refine mem_wedge_of_real (by linarith [K.σ.θ₁_pos])
      (mul_ne_zero (Complex.exp_ne_zero _) (rotOne_ne_zero K (ne_of_re_pos hre.1) h1)) ?_ ?_
    · rw [re_exp_neg_mul]
      exact add_nonneg (mul_nonneg K.σ.cos_θ₁_nonneg (CompactShape.re_rotOne_nonneg_sph K.hσ hz))
        (mul_nonneg K.σ.sin_θ₁_pos.le (CompactShape.sector_one_sph K.hσ hz).1)
    · rw [im_exp_neg_mul]
      have e := CompactShape.wallSide_two_eq_rotOne_sph K.hσ (ne_of_re_pos hre.1)
        (ne_of_re_pos hre.2)
      have hp : 0 < normSq (1 + (K.σ.sphTOneTwo : ℂ) * K.σ.rotTwo z) :=
        normSq_pos.mpr (ne_of_re_pos (one_add_mul_rotTwo_pos K hz))
      rw [him, mul_zero] at e
      rw [(mul_eq_zero.mp e).resolve_right hp.ne', neg_zero]
  · exact mem_wedge_of_real (by linarith [K.σ.θ₂_pos])
      (rotTwo_ne_zero K (ne_of_re_pos hre.2) h2) (CompactShape.re_rotTwo_nonneg_sph K.hσ hz) him

theorem discA_eq (w : ℂ) : discA K.σ.sphTTwoThree w = discV K.σ.vertexTwo w := by
  unfold discA discV
  rw [conj_vertexTwo_sph K.σ]
  rfl

theorem conj_discA_mul {z : ℂ} :
    conj (discA K.σ.sphTTwoThree K.σ.vertexOne) * discA K.σ.sphTTwoThree z =
      (K.σ.sphTOneTwo : ℂ) * K.σ.rotTwo z := by
  rw [discA_eq, discA_eq]
  have hE := conj_exp_mul_exp_sph K.σ.θ₂
  have h1 : exp ((K.σ.θ₂ : ℂ) * I) * discV K.σ.vertexTwo K.σ.vertexOne =
      -(K.σ.sphTOneTwo : ℂ) := by
    have := CompactShape.rotTwo_vertexOne_sph K.hσ
    rw [rotTwo_eq_of_sph K.hσ] at this
    linear_combination -this
  have h1' : conj (exp ((K.σ.θ₂ : ℂ) * I)) * conj (discV K.σ.vertexTwo K.σ.vertexOne) =
      -(K.σ.sphTOneTwo : ℂ) := by
    rw [← map_mul, h1, map_neg, conj_ofReal]
  have h2 : exp ((K.σ.θ₂ : ℂ) * I) * discV K.σ.vertexTwo z = -K.σ.rotTwo z := by
    rw [rotTwo_eq_of_sph K.hσ]
    ring
  linear_combination (-(conj (discV K.σ.vertexTwo K.σ.vertexOne) *
    discV K.σ.vertexTwo z)) * hE + (exp ((K.σ.θ₂ : ℂ) * I) * discV K.σ.vertexTwo z) * h1' -
    (K.σ.sphTOneTwo : ℂ) * h2

theorem psiS_sub_of_wallTwo {z : ℂ} (hz : z ∈ K.σ.triangle) (hw : K.σ.wallSide 2 z = 0) :
    psiS K.σ.vertexOne z - psiS K.σ.vertexTwo z = arg (1 + K.σ.vertexTwo * K.σ.vertexOne) := by
  have hz' : 0 < (1 + (K.σ.sphTTwoThree : ℂ) * z).re := by
    have := (re_pos_of_triangle K hz).2
    rwa [conj_vertexTwo_sph K.σ] at this
  have hB : 0 < (1 + (K.σ.sphTTwoThree : ℂ) * K.σ.vertexOne).re := by
    have := (re_pos_of_triangle K (CompactShape.vertexOne_mem_triangle_sph K.hσ)).2
    rwa [conj_vertexTwo_sph K.σ] at this
  have hY : 0 < (1 + conj (discA K.σ.sphTTwoThree K.σ.vertexOne) *
      discA K.σ.sphTTwoThree z).re := by
    rw [conj_discA_mul]
    exact one_add_mul_rotTwo_pos K hz
  have hY' : (1 + conj (discA K.σ.sphTTwoThree K.σ.vertexOne) *
      discA K.σ.sphTTwoThree z).im = 0 := by
    rw [conj_discA_mul, add_im, one_im, im_ofReal_mul, im_rotTwo_eq_zero K hz hw, mul_zero,
      zero_add]
  exact psiS_sub_psiS_of_wall (a := K.σ.sphTTwoThree) hz' hB hY hY'

theorem mem_patchZero_of_wall {z : ℂ} (hz : z ∈ K.σ.triangle) (hw : K.σ.wallSide 0 z = 0)
    (h0 : z ≠ 0) (h2 : z ≠ K.σ.vertexTwo) : z ∈ patchZero K := by
  have hg := goodZero_of_wall K hz hw h0 h2
  have hr : conj z = z := CompactShape.refl_zero_eq_self_sph hw
  exact ⟨K.D.foldWall_diff_subset_V 0 ⟨⟨hz, hw⟩, h0⟩, hg, by rw [hr]; exact hg⟩

theorem mem_patchOne_of_wall {z : ℂ} (hz : z ∈ K.σ.triangle) (hw : K.σ.wallSide 1 z = 0)
    (h0 : z ≠ 0) (h1 : z ≠ K.σ.vertexOne) : z ∈ patchOne K := by
  have hg := goodOne_of_wall K hz hw h0 h1
  have hr : K.σ.refl 1 z = z := CompactShape.refl_one_eq_self_sph hw
  exact ⟨K.D.foldWall_diff_subset_V 1 ⟨⟨hz, hw⟩, h0⟩, hg, by rw [hr]; exact hg⟩

theorem mem_patchTwo_of_wall {z : ℂ} (hz : z ∈ K.σ.triangle) (hw : K.σ.wallSide 2 z = 0)
    (h0 : z ≠ 0) (h1 : z ≠ K.σ.vertexOne) (h2 : z ≠ K.σ.vertexTwo) : z ∈ patchTwo K := by
  have hg := goodTwo_of_wall K hz hw h0 h1 h2
  have hd : 1 + K.σ.vertexTwo * z ≠ 0 := by
    have := ne_of_re_pos (re_pos_of_triangle K hz).2
    rwa [conj_vertexTwo_sph K.σ] at this
  have hr : K.σ.refl 2 z = z := CompactShape.refl_two_eq_self_sph K.hσ hw hd
  refine ⟨K.D.foldWall_diff_subset_V 2 ⟨⟨hz, hw⟩, h0⟩, hg, by rw [hr]; exact hg, ?_⟩
  have key := psiS_sub_of_wallTwo K hz hw
  unfold defect
  rw [hr]
  have e : psiS K.σ.vertexOne z + psiS K.σ.vertexOne z - psiS K.σ.vertexTwo z -
      psiS K.σ.vertexTwo z - 2 * arg (1 + K.σ.vertexTwo * K.σ.vertexOne) =
      2 * (psiS K.σ.vertexOne z - psiS K.σ.vertexTwo z -
        arg (1 + K.σ.vertexTwo * K.σ.vertexOne)) := by ring
  rw [e, key, sub_self, mul_zero, abs_zero]
  exact Real.pi_pos

end Walls

section Cover

theorem cover : K.σ.triangle \ {0} ⊆ mainSet K ∪ discOneR K (radOne K) ∪
    discTwoR K (radTwo K) ∪ discThreeR (radThree K) := by
  rintro z ⟨hz, h0⟩
  have h0' : z ≠ 0 := h0
  have hP0 : z ∈ patchZero K → z ∈ mainSet K ∪ discOneR K (radOne K) ∪
      discTwoR K (radTwo K) ∪ discThreeR (radThree K) := fun h =>
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  have hP1 : z ∈ patchOne K → z ∈ mainSet K ∪ discOneR K (radOne K) ∪
      discTwoR K (radTwo K) ∪ discThreeR (radThree K) := fun h =>
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
  have hP2 : z ∈ patchTwo K → z ∈ mainSet K ∪ discOneR K (radOne K) ∪
      discTwoR K (radTwo K) ∪ discThreeR (radThree K) := fun h =>
    Or.inl (Or.inl (Or.inl (Or.inr h)))
  have hD1 : z = K.σ.vertexOne → z ∈ mainSet K ∪ discOneR K (radOne K) ∪
      discTwoR K (radTwo K) ∪ discThreeR (radThree K) := fun h =>
    Or.inl (Or.inl (Or.inr (by rw [h]; exact mem_discOne_vertexOne K)))
  have hD2 : z = K.σ.vertexTwo → z ∈ mainSet K ∪ discOneR K (radOne K) ∪
      discTwoR K (radTwo K) ∪ discThreeR (radThree K) := fun h =>
    Or.inl (Or.inr (by rw [h]; exact mem_discTwo_vertexTwo K))
  by_cases hi : ∀ i, 0 < K.σ.wallSide i z
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨hz.1, hi⟩)))))
  simp only [not_forall, not_lt] at hi
  obtain ⟨i, hi⟩ := hi
  have hw : K.σ.wallSide i z = 0 := le_antisymm hi (hz.2 i)
  fin_cases i
  · by_cases h2 : z = K.σ.vertexTwo
    · exact hD2 h2
    · exact hP0 (mem_patchZero_of_wall K hz hw h0' h2)
  · by_cases h1 : z = K.σ.vertexOne
    · exact hD1 h1
    · exact hP1 (mem_patchOne_of_wall K hz hw h0' h1)
  · by_cases h1 : z = K.σ.vertexOne
    · exact hD1 h1
    by_cases h2 : z = K.σ.vertexTwo
    · exact hD2 h2
    · exact hP2 (mem_patchTwo_of_wall K hz hw h0' h1 h2)

theorem rotTwo_vertexOne_real : exp (-(2 * (K.σ.θ₂ : ℂ) * I)) *
    conj (discV K.σ.vertexTwo K.σ.vertexOne) = discV K.σ.vertexTwo K.σ.vertexOne := by
  have e : discV K.σ.vertexTwo K.σ.vertexOne =
      -(exp (-((K.σ.θ₂ : ℂ) * I)) * K.σ.sphTOneTwo) :=
    CompactShape.sphMoeb_vertexTwo_vertexOne K.hσ
  rw [e, map_neg, map_mul, CompactShape.conj_exp_neg_sph, conj_ofReal]
  have h : exp (-(2 * (K.σ.θ₂ : ℂ) * I)) * exp ((K.σ.θ₂ : ℂ) * I) =
      exp (-((K.σ.θ₂ : ℂ) * I)) := by
    rw [← Complex.exp_add]
    ring_nf
  linear_combination (-(K.σ.sphTOneTwo : ℂ)) * h

end Cover

end Lay

theorem exists_sphLayout (K : SphDatum) : Nonempty (SphLayout K) :=
  ⟨{ radOne := Lay.radOne K
     radTwo := Lay.radTwo K
     radThree := Lay.radThree K
     radOne_pos := Lay.radOne_pos K
     radTwo_pos := Lay.radTwo_pos K
     radThree_pos := Lay.radThree_pos K
     radOne_le_apex := Lay.radOne_le_apex K
     radTwo_le_apex := Lay.radTwo_le_apex K
     radThree_le_apex := Lay.radThree_le_apex K
     radOne_le_half := Lay.radOne_le_half K
     radTwo_le_half := Lay.radTwo_le_half K
     radThree_le_half := Lay.radThree_le_half K
     discOne_slit := Lay.discOne_slit K
     discTwo_slit := Lay.discTwo_slit K
     discOne_den := Lay.discOne_den K
     discTwo_den := Lay.discTwo_den K
     discOne_im_pos := Lay.discOne_im_pos K
     disjoint_one_two := Lay.disjoint_one_two K
     disjoint_one_three := Lay.disjoint_one_three K
     disjoint_two_three := Lay.disjoint_two_three K
     disjoint_two_mirror := Lay.disjoint_two_mirror K
     disjoint_three_mirror := Lay.disjoint_three_mirror K
     discOne_sector := Lay.discOne_sector K
     discTwo_sector := Lay.discTwo_sector K
     discThree_sector := Lay.discThree_sector K
     triangle_sector_one := Lay.triangle_sector_one K
     triangle_sector_two := Lay.triangle_sector_two K
     triangle_sector_three := Lay.triangle_sector_three K
     patchZero := Lay.patchZero K
     patchOne := Lay.patchOne K
     patchTwo := Lay.patchTwo K
     isOpen_patchZero := Lay.isOpen_patchZero K
     isOpen_patchOne := Lay.isOpen_patchOne K
     isOpen_patchTwo := Lay.isOpen_patchTwo K
     patchZero_spec := Lay.patchZero_spec K
     patchOne_spec := Lay.patchOne_spec K
     patchTwo_spec := Lay.patchTwo_spec K
     patchZero_out := Lay.patchZero_out K
     patchOne_out := Lay.patchOne_out K
     patchTwo_out := Lay.patchTwo_out K
     main_ne := Lay.main_ne K
     main_slit := Lay.main_slit K
     main_conj := Lay.main_conj K
     main_mirror := Lay.main_mirror K
     main_window_one := Lay.main_window_one K
     main_window_two := Lay.main_window_two K
     main_window_three := Lay.main_window_three K
     rotTwo_vertexOne_real := Lay.rotTwo_vertexOne_real K
     patchTwo_window := Lay.patchTwo_window K
     cover := Lay.cover K }⟩

end Sph

end ClosedTriangle

end GC.Seifert

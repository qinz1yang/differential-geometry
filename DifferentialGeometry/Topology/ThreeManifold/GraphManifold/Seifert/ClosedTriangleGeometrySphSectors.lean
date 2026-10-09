import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphPatches

/-!
# Angle windows in the vertex discs of a spherical closed triangle fold

Lane B3d2 (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §5; the
spherical analogue of B3c's `ClosedTriangleGeometryHypSectors`). On the vertex discs the fold
datum is the apex germ (`f_of_mem_discOne`, `f_of_mem_discTwo`) resp. the outer germ
(`f_of_mem_discThree`), so `Re f ≥ 1` on the disc of `v₁`, `Re f ≤ -1` on the disc of `v₂` and
`|f| ≥ 3` on the punctured disc of `0`. The side functions are positive multiples of the
imaginary parts of the rotated disc coordinates (CF-S's `wallSide_one_eq_rotOne_sph`,
`wallSide_two_eq_rotOne_sph`, `wallSide_two_eq_sph`, `wallSide_zero_eq_rotTwo_sph`), so in the
open triangle the coordinate of a vertex lies in the open sector `(0, θⱼ)`; in the patches it lies
in the wedge of the patch definition, or the patch misses the disc by its image condition. Hence
on the main set the angles lie in the good windows `(-θⱼ/2, 3θⱼ/2)` (`main_window_one`,
`main_window_two`, `main_window_three`).
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

section Germs

theorem mem_apexDisc_one {z : ℂ} (hz : z ∈ discOneR K (radOne K)) :
    z ∈ K.σ.apexDisc K.σ.vertexOne (K.D.apexRadius 0) := by
  refine ⟨?_, ?_⟩
  · rw [K.σ.eps_of_sph K.hσ]
    have := hz.1
    simpa using this
  · rw [disc_of_sph K.hσ, ← norm_rotOne_eq]
    exact lt_of_lt_of_le hz.2 (radOne_le_apex K)

theorem mem_apexDisc_two {z : ℂ} (hz : z ∈ discTwoR K (radTwo K)) :
    z ∈ K.σ.apexDisc K.σ.vertexTwo (K.D.apexRadius 1) := by
  refine ⟨?_, ?_⟩
  · rw [K.σ.eps_of_sph K.hσ]
    have := hz.1
    simpa using this
  · rw [disc_of_sph K.hσ, ← norm_rotTwo_eq]
    exact lt_of_lt_of_le hz.2 (radTwo_le_apex K)

theorem re_f_of_mem_discOne {z : ℂ} (hz : z ∈ discOneR K (radOne K)) : 1 ≤ (K.D.f z).re := by
  rw [(K.D.f_apexOne z (mem_apexDisc_one K hz)).2]
  have hn : ‖K.σ.rotOne z‖ ≤ 1 / 2 := (le_of_lt hz.2).trans (radOne_le_half K)
  have hp : ‖K.σ.rotOne z ^ K.σ.p₁ / 2‖ ≤ 1 / 2 := by
    rw [norm_div, norm_pow, Complex.norm_two]
    have : ‖K.σ.rotOne z‖ ^ K.σ.p₁ ≤ 1 := pow_le_one₀ (norm_nonneg _) (by linarith)
    linarith
  have := abs_le.mp ((abs_re_le_norm _).trans hp)
  simp only [div_ofNat_re] at this
  rw [add_re]
  norm_num
  linarith [this.1]

theorem re_f_of_mem_discTwo {z : ℂ} (hz : z ∈ discTwoR K (radTwo K)) : (K.D.f z).re ≤ -1 := by
  rw [(K.D.f_apexTwo z (mem_apexDisc_two K hz)).2]
  have hn : ‖K.σ.rotTwo z‖ ≤ 1 / 2 := (le_of_lt hz.2).trans (radTwo_le_half K)
  have hp : ‖K.σ.rotTwo z ^ K.σ.p₂ / 2‖ ≤ 1 / 2 := by
    rw [norm_div, norm_pow, Complex.norm_two]
    have : ‖K.σ.rotTwo z‖ ^ K.σ.p₂ ≤ 1 := pow_le_one₀ (norm_nonneg _) (by linarith)
    linarith
  have := abs_le.mp ((abs_re_le_norm _).trans hp)
  simp only [div_ofNat_re] at this
  rw [add_re]
  norm_num
  linarith [this.2]

theorem norm_f_of_mem_discThree {z : ℂ} (hz : z ∈ discThreeR (radThree K)) (h0 : z ≠ 0) :
    3 ≤ ‖K.D.f z‖ := by
  rw [(K.D.f_outer z (norm_pos_iff.mpr h0) (lt_of_lt_of_le hz (radThree_le_apex K))).2,
    compactOuterGerm, norm_neg, norm_mul, Complex.norm_real, norm_pow, norm_div,
    Complex.norm_conj, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr h0), one_pow,
    mul_one]
  have hn : ‖z‖ ^ K.σ.p₃ ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) ((le_of_lt hz).trans (by linarith [radThree_le_half K]))
  rw [Real.norm_of_nonneg (by linarith)]
  linarith

end Germs

section Windows

theorem normSq_vertexTwo_pos {z : ℂ} (h : 0 < (1 + conj K.σ.vertexTwo * z).re) :
    0 < normSq (1 + K.σ.vertexTwo * z) := by
  rw [conj_vertexTwo_sph K.σ] at h
  exact normSq_pos.mpr (ne_of_re_pos h)

theorem im_rotOne_pos {z : ℂ} (hd : 1 + conj K.σ.vertexOne * z ≠ 0)
    (h : 0 < K.σ.wallSide 1 z) : 0 < (K.σ.rotOne z).im := by
  have e := CompactShape.wallSide_one_eq_rotOne_sph K.hσ z
  have hp : 0 < normSq (1 + conj K.σ.vertexOne * z) := normSq_pos.mpr hd
  have ht : 0 < 1 + K.σ.sphTOneThree ^ 2 := by positivity
  by_contra hn
  rw [not_lt] at hn
  nlinarith [mul_pos h ht]

theorem im_rotTwo_pos {z : ℂ} (hd : 0 < (1 + conj K.σ.vertexTwo * z).re)
    (h : 0 < K.σ.wallSide 2 z) : 0 < (K.σ.rotTwo z).im := by
  have e := CompactShape.wallSide_two_eq_sph K.hσ z
  have hp := normSq_vertexTwo_pos K hd
  by_contra hn
  rw [not_lt] at hn
  nlinarith

theorem im_rot_rotOne_neg {z : ℂ} (hd1 : 1 + conj K.σ.vertexOne * z ≠ 0)
    (hd2 : 0 < (1 + conj K.σ.vertexTwo * z).re) (h : 0 < K.σ.wallSide 2 z) :
    (exp (-((K.σ.θ₁ : ℂ) * I)) * K.σ.rotOne z).im < 0 := by
  have e := CompactShape.wallSide_two_eq_rotOne_sph K.hσ hd1 (ne_of_re_pos hd2)
  have h2 := im_rotTwo_pos K hd2 h
  have ht : 0 < 1 + K.σ.sphTOneTwo ^ 2 := by positivity
  have hX : 0 < (exp ((K.σ.θ₁ : ℂ) * I) * conj (K.σ.rotOne z)).im := by
    by_contra hn
    rw [not_lt] at hn
    nlinarith [mul_pos ht h2, normSq_nonneg (1 + (K.σ.sphTOneTwo : ℂ) * K.σ.rotTwo z)]
  rw [im_exp_neg_mul]
  linarith

theorem im_rot_rotTwo_neg {z : ℂ} (hd : 0 < (1 + conj K.σ.vertexTwo * z).re)
    (h : 0 < K.σ.wallSide 0 z) : (exp (-((K.σ.θ₂ : ℂ) * I)) * K.σ.rotTwo z).im < 0 := by
  have e := CompactShape.wallSide_zero_eq_rotTwo_sph K.hσ z
  have hp := normSq_vertexTwo_pos K hd
  have ht : 0 < 1 + K.σ.sphTTwoThree ^ 2 := by positivity
  have hX : 0 < (exp ((K.σ.θ₂ : ℂ) * I) * conj (K.σ.rotTwo z)).im := by
    by_contra hn
    rw [not_lt] at hn
    nlinarith [mul_pos h ht]
  rw [im_exp_neg_mul]
  linarith

theorem im_rot_three_neg {z : ℂ} (h : 0 < K.σ.wallSide 1 z) :
    (exp (-((K.σ.θ₃ : ℂ) * I)) * z).im < 0 := by
  rw [im_exp_neg_mul]
  change 0 < (exp ((K.σ.θ₃ : ℂ) * I) * conj z).im at h
  linarith

theorem main_window_one : ∀ z ∈ mainSet K, z ∈ discOneR K (radOne K) →
    -(K.σ.θ₁ / 2) < arg (K.σ.rotOne z) ∧ arg (K.σ.rotOne z) < 3 * K.σ.θ₁ / 2 := by
  intro z hm hd
  have hnd : ¬ radOne K < ‖K.σ.rotOne z‖ := not_lt.mpr (le_of_lt hd.2)
  have hθ := K.σ.θ₁_pos
  rcases hm with ((h | h) | h) | h
  · have hre := (re_pos_of_triangle K (K.σ.openTriangle_subset h)).2
    obtain ⟨-, a, b⟩ := arg_mem_of_sides K.σ.θ₁_pos K.σ.θ₁_le (im_rotOne_pos K hd.1 (h.2 1))
      (im_rot_rotOne_neg K hd.1 hre (h.2 2))
    exact ⟨by linarith, by linarith⟩
  · exfalso
    obtain ⟨-, ⟨-, -, -, -, hf, -⟩, -⟩ := h
    have := re_f_of_mem_discOne K hd
    linarith
  · obtain ⟨-, ⟨-, -, -, -, -, hw, -⟩, -⟩ := h
    rcases hw with h' | h'
    · exact absurd h' hnd
    · obtain ⟨-, a, b⟩ := arg_of_wedge h'
      exact ⟨a, by linarith⟩
  · obtain ⟨-, ⟨-, -, -, -, -, -, -, hw, -⟩, -⟩ := h
    rcases hw with h' | h'
    · exact absurd h' hnd
    · obtain ⟨-, a, b⟩ := arg_of_rot_wedge K.σ.θ₁_pos K.σ.θ₁_le h'
      exact ⟨by linarith, b⟩

theorem main_window_two : ∀ z ∈ mainSet K, z ∈ discTwoR K (radTwo K) →
    -(K.σ.θ₂ / 2) < arg (K.σ.rotTwo z) ∧ arg (K.σ.rotTwo z) < 3 * K.σ.θ₂ / 2 := by
  intro z hm hd
  have hnd : ¬ radTwo K < ‖K.σ.rotTwo z‖ := not_lt.mpr (le_of_lt hd.2)
  have hθ := K.σ.θ₂_pos
  rcases hm with ((h | h) | h) | h
  · have hre := (re_pos_of_triangle K (K.σ.openTriangle_subset h)).2
    obtain ⟨-, a, b⟩ := arg_mem_of_sides K.σ.θ₂_pos K.σ.θ₂_le (im_rotTwo_pos K hre (h.2 2))
      (im_rot_rotTwo_neg K hre (h.2 0))
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨-, ⟨-, -, -, -, -, -, hw, -⟩, -⟩ := h
    rcases hw with h' | h'
    · exact absurd h' hnd
    · obtain ⟨-, a, b⟩ := arg_of_rot_wedge K.σ.θ₂_pos K.σ.θ₂_le h'
      exact ⟨by linarith, b⟩
  · exfalso
    obtain ⟨-, ⟨-, -, -, -, hf, -⟩, -⟩ := h
    have := re_f_of_mem_discTwo K hd
    linarith
  · obtain ⟨-, ⟨-, -, -, -, -, -, -, -, hw⟩, -⟩ := h
    rcases hw with h' | h'
    · exact absurd h' hnd
    · obtain ⟨-, a, b⟩ := arg_of_wedge h'
      exact ⟨a, by linarith⟩

theorem main_window_three : ∀ z ∈ mainSet K, z ∈ discThreeR (radThree K) →
    -(K.σ.θ₃ / 2) < arg z ∧ arg z < 3 * K.σ.θ₃ / 2 := by
  intro z hm hd
  have hnd : ¬ radThree K < ‖z‖ := not_lt.mpr (le_of_lt hd)
  have hθ := K.σ.θ₃_pos
  rcases hm with ((h | h) | h) | h
  · obtain ⟨-, a, b⟩ := arg_mem_of_sides (w := z) K.σ.θ₃_pos K.σ.θ₃_le (h.2 0)
      (im_rot_three_neg K (h.2 1))
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨-, ⟨-, -, -, -, -, -, -, hw⟩, -⟩ := h
    rcases hw with h' | h'
    · exact absurd h' hnd
    · obtain ⟨-, a, b⟩ := arg_of_wedge h'
      exact ⟨a, by linarith⟩
  · obtain ⟨-, ⟨-, -, -, -, -, -, hw⟩, -⟩ := h
    rcases hw with h' | h'
    · exact absurd h' hnd
    · obtain ⟨-, a, b⟩ := arg_of_rot_wedge K.σ.θ₃_pos K.σ.θ₃_le h'
      exact ⟨by linarith, b⟩
  · exfalso
    obtain ⟨-, ⟨h0, -, -, -, -, -, hn, -⟩, -⟩ := h
    have hz0 : z ≠ 0 := by
      intro e
      rw [e, CompactShape.wallSide_zero_zero_sph] at h0
      exact lt_irrefl _ h0
    have h3 := norm_f_of_mem_discThree K hd hz0
    rw [normSq_eq_norm_sq] at hn
    nlinarith [norm_nonneg (K.D.f z)]

end Windows

end Lay

end Sph

end ClosedTriangle

end GC.Seifert

import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypShape

/-!
# The hyperbolic compact triangle: reflections and vertices

Lane CF-H, tier 1 (design
`docs/geometrization/handoffs/20261004-design-cf-compact-triangle-fold.md`,
§2, curvature `-1`). The three reflections of `CompactShape` preserve the unit disc
(`norm_refl_lt_one`), which lies in their chart domains (`mem_reflChart`), are involutions there
(`refl_refl`), fix their wall pointwise (`refl_eq_self`), reverse the side function of their wall
up to a positive factor (`wallSide_refl`), and preserve the pseudo-hyperbolic distance to the two
vertices of their wall (`norm_disc_refl_*`): in the coordinate `rotTwo` the reflection in wall 2
is complex conjugation (`rotTwo_refl_two`).

The vertices lie on their walls and in the triangle (`zero_mem_triangle`,
`vertexOne_mem_triangle`, `vertexTwo_mem_triangle`). On the real axis and on the ray of wall 1 the
side function of wall 2 factors through the two roots `t` and `1/t` of the geodesic circle
(`wallSide_two_ofReal`, `wallSide_two_ray`).
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate

namespace GC.Seifert

namespace HypFold

variable {σ : CompactShape}

theorem mobInv_eq_mob_neg (a w : ℂ) : mobInv a w = mob (-a) w := by
  simp [mobInv, mob, map_neg, sub_neg_eq_add]

theorem norm_mobInv_lt_one {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) : ‖mobInv a w‖ < 1 := by
  rw [mobInv_eq_mob_neg]
  exact norm_mob_lt_one (by rwa [norm_neg]) hw

section Hyp

variable (h : σ.curv = .hyperbolic)
include h

theorem reflTwoAux_eq (z : ℂ) :
    σ.reflTwoAux z = exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (mob σ.vertexTwo z) := by
  rw [CompactShape.reflTwoAux, CompactShape.disc_eq_mob h]

theorem refl_two_eq (z : ℂ) :
    σ.refl 2 z = mobInv σ.vertexTwo (exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (mob σ.vertexTwo z)) := by
  change σ.discInv σ.vertexTwo (σ.reflTwoAux z) = _
  rw [CompactShape.discInv_eq_mobInv h, reflTwoAux_eq h]

omit h in
theorem norm_exp_neg_two (x : ℝ) : ‖exp (-(2 * (x : ℂ) * I))‖ = 1 := by
  rw [show -(2 * (x : ℂ) * I) = ((-(2 * x) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

omit h in
theorem norm_exp_two (x : ℝ) : ‖exp (2 * (x : ℂ) * I)‖ = 1 := by
  rw [show 2 * (x : ℂ) * I = ((2 * x : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem norm_reflTwoAux {z : ℂ} : ‖σ.reflTwoAux z‖ = ‖mob σ.vertexTwo z‖ := by
  rw [reflTwoAux_eq h, norm_mul, norm_exp_neg_two, one_mul, Complex.norm_conj]

theorem norm_refl_lt_one (i : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) : ‖σ.refl i z‖ < 1 := by
  fin_cases i
  · change ‖conj z‖ < 1
    rwa [Complex.norm_conj]
  · change ‖exp (2 * (σ.θ₃ : ℂ) * I) * conj z‖ < 1
    rwa [norm_mul, norm_exp_two, one_mul, Complex.norm_conj]
  · change ‖σ.refl 2 z‖ < 1
    rw [refl_two_eq h]
    apply norm_mobInv_lt_one (norm_vertexTwo_lt_one h)
    rw [norm_mul, norm_exp_neg_two, one_mul, Complex.norm_conj]
    exact norm_mob_lt_one (norm_vertexTwo_lt_one h) hz

theorem mem_reflChart (i : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) : z ∈ σ.reflChart i := by
  fin_cases i
  · exact Set.mem_univ z
  · exact Set.mem_univ z
  · refine ⟨?_, ?_⟩
    · rw [CompactShape.eps_hyp h, Complex.ofReal_one, one_mul]
      exact one_sub_conj_mul_ne_zero (norm_vertexTwo_lt_one h) hz
    · rw [CompactShape.eps_hyp h, Complex.ofReal_one, one_mul]
      apply one_add_conj_mul_ne_zero (norm_vertexTwo_lt_one h)
      rw [norm_reflTwoAux h]
      exact norm_mob_lt_one (norm_vertexTwo_lt_one h) hz

theorem mob_vertexTwo_refl_two {z : ℂ} (hz : ‖z‖ < 1) :
    mob σ.vertexTwo (σ.refl 2 z) = exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (mob σ.vertexTwo z) := by
  rw [refl_two_eq h, mob_mobInv (normSq_vertexTwo_ne_one h)]
  apply one_add_conj_mul_ne_zero (norm_vertexTwo_lt_one h)
  rw [norm_mul, norm_exp_neg_two, one_mul, Complex.norm_conj]
  exact norm_mob_lt_one (norm_vertexTwo_lt_one h) hz

theorem rotTwo_refl_two {z : ℂ} (hz : ‖z‖ < 1) : σ.rotTwo (σ.refl 2 z) = conj (σ.rotTwo z) := by
  rw [rotTwo_eq_mul_mob h, rotTwo_eq_mul_mob h, mob_vertexTwo_refl_two h hz, map_mul, map_neg,
    ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← mul_assoc, neg_mul,
    neg_mul, ← Complex.exp_add]
  rw [show (σ.θ₂ : ℂ) * I + -(2 * (σ.θ₂ : ℂ) * I) = (σ.θ₂ : ℂ) * -I by ring, neg_mul]

theorem refl_refl (i : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) : σ.refl i (σ.refl i z) = z := by
  fin_cases i
  · exact Complex.conj_conj z
  · change exp (2 * (σ.θ₃ : ℂ) * I) * conj (exp (2 * (σ.θ₃ : ℂ) * I) * conj z) = z
    rw [map_mul, Complex.conj_conj, ← Complex.exp_conj, map_mul, map_mul, Complex.conj_ofReal,
      Complex.conj_I, ← mul_assoc, ← Complex.exp_add, show conj (2 : ℂ) = 2 from map_ofNat _ 2]
    ring_nf
    rw [Complex.exp_zero, one_mul]
  · change σ.refl 2 (σ.refl 2 z) = z
    have hz' := norm_refl_lt_one h 2 hz
    rw [refl_two_eq h (σ.refl 2 z), mob_vertexTwo_refl_two h hz, map_mul, Complex.conj_conj,
      ← Complex.exp_conj, ← mul_assoc, map_neg, map_mul, map_mul, Complex.conj_ofReal,
      Complex.conj_I, show conj (2 : ℂ) = 2 from map_ofNat _ 2, ← Complex.exp_add]
    ring_nf
    rw [Complex.exp_zero, one_mul, mobInv_mob (normSq_vertexTwo_ne_one h)
      (one_sub_conj_mul_ne_zero (norm_vertexTwo_lt_one h) hz)]

omit h in
theorem wallSide_refl_zero (z : ℂ) : σ.wallSide 0 (σ.refl 0 z) = -σ.wallSide 0 z := by
  change (conj z).im = -z.im
  rw [Complex.conj_im]

omit h in
theorem wallSide_refl_one (z : ℂ) : σ.wallSide 1 (σ.refl 1 z) = -σ.wallSide 1 z := by
  change (exp ((σ.θ₃ : ℂ) * I) * conj (exp (2 * (σ.θ₃ : ℂ) * I) * conj z)).im = _
  have e : exp ((σ.θ₃ : ℂ) * I) * conj (exp (2 * (σ.θ₃ : ℂ) * I) * conj z) =
      exp (-((σ.θ₃ : ℂ) * I)) * z := by
    rw [map_mul, Complex.conj_conj, ← Complex.exp_conj, ← mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  rw [e, wallSide_one_eq_neg_im, neg_neg]

theorem wallSide_refl_two {z : ℂ} (hz : ‖z‖ < 1) :
    σ.wallSide 2 (σ.refl 2 z) = -(normSq (1 - σ.vertexTwo * σ.refl 2 z) /
      normSq (1 - σ.vertexTwo * z)) * σ.wallSide 2 z := by
  have hp := normSq_pos_of_ne (one_sub_vertexTwo_mul_ne_zero h hz)
  rw [wallSide_two_eq_rotTwo h, wallSide_two_eq_rotTwo h, rotTwo_refl_two h hz, Complex.conj_im]
  field_simp

theorem wallSide_refl (i : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ c : ℝ, 0 < c ∧ σ.wallSide i (σ.refl i z) = -c * σ.wallSide i z := by
  fin_cases i
  · refine ⟨1, one_pos, ?_⟩
    change σ.wallSide 0 (σ.refl 0 z) = -1 * σ.wallSide 0 z
    rw [wallSide_refl_zero]
    ring
  · refine ⟨1, one_pos, ?_⟩
    change σ.wallSide 1 (σ.refl 1 z) = -1 * σ.wallSide 1 z
    rw [wallSide_refl_one]
    ring
  · refine ⟨_, div_pos (normSq_pos_of_ne (one_sub_vertexTwo_mul_ne_zero h
      (norm_refl_lt_one h 2 hz))) (normSq_pos_of_ne (one_sub_vertexTwo_mul_ne_zero h hz)),
      wallSide_refl_two h hz⟩

theorem refl_eq_self (i : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) (hw : σ.wallSide i z = 0) :
    σ.refl i z = z := by
  fin_cases i
  · change conj z = z
    exact Complex.conj_eq_iff_im.2 hw
  · change exp (2 * (σ.θ₃ : ℂ) * I) * conj z = z
    have hw' : (exp (-((σ.θ₃ : ℂ) * I)) * z).im = 0 := by
      have := wallSide_one_eq_neg_im (σ := σ) z
      change σ.wallSide 1 z = 0 at hw
      linarith
    have hc : conj (exp (-((σ.θ₃ : ℂ) * I)) * z) = exp (-((σ.θ₃ : ℂ) * I)) * z :=
      Complex.conj_eq_iff_im.2 hw'
    rw [map_mul, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I] at hc
    calc exp (2 * (σ.θ₃ : ℂ) * I) * conj z
        = exp ((σ.θ₃ : ℂ) * I) * (exp (-((σ.θ₃ : ℂ) * -I)) * conj z) := by
          rw [← mul_assoc, ← Complex.exp_add]
          ring_nf
      _ = exp ((σ.θ₃ : ℂ) * I) * (exp (-((σ.θ₃ : ℂ) * I)) * z) := by rw [hc]
      _ = z := by rw [← mul_assoc, exp_mul_exp_neg, one_mul]
  · change σ.refl 2 z = z
    have hp := normSq_pos_of_ne (one_sub_vertexTwo_mul_ne_zero h hz)
    change σ.wallSide 2 z = 0 at hw
    rw [wallSide_two_eq_rotTwo h] at hw
    have him : (σ.rotTwo z).im = 0 := (mul_eq_zero.1 hw).resolve_right hp.ne'
    have hc : conj (σ.rotTwo z) = σ.rotTwo z := Complex.conj_eq_iff_im.2 him
    rw [rotTwo_eq_mul_mob h, map_mul, map_neg, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I] at hc
    have hm : exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (mob σ.vertexTwo z) = mob σ.vertexTwo z := by
      have e2 := exp_mul_exp_neg σ.θ₂
      have : exp ((σ.θ₂ : ℂ) * I) * (exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (mob σ.vertexTwo z)) =
          exp ((σ.θ₂ : ℂ) * I) * mob σ.vertexTwo z := by
        rw [← mul_assoc, ← Complex.exp_add, show (σ.θ₂ : ℂ) * I + -(2 * (σ.θ₂ : ℂ) * I) =
          (σ.θ₂ : ℂ) * -I by ring]
        linear_combination (-1 : ℂ) * hc
      exact mul_left_cancel₀ (Complex.exp_ne_zero _) this
    rw [refl_two_eq h, hm, mobInv_mob (normSq_vertexTwo_ne_one h)
      (one_sub_conj_mul_ne_zero (norm_vertexTwo_lt_one h) hz)]

omit h in
theorem norm_mob_conj_ofReal (t : ℝ) (W : ℂ) : ‖mob (t : ℂ) (conj W)‖ = ‖mob (t : ℂ) W‖ := by
  have e := mob_conj_conj (t : ℂ) W
  rw [Complex.conj_ofReal] at e
  rw [e, Complex.norm_conj]

theorem norm_disc_refl_zero_zero (z : ℂ) : ‖σ.disc 0 (σ.refl 0 z)‖ = ‖σ.disc 0 z‖ := by
  rw [CompactShape.disc_eq_mob h, CompactShape.disc_eq_mob h, mob_zero_left, mob_zero_left]
  exact Complex.norm_conj z

theorem norm_disc_refl_zero_two (z : ℂ) :
    ‖σ.disc σ.vertexTwo (σ.refl 0 z)‖ = ‖σ.disc σ.vertexTwo z‖ := by
  rw [CompactShape.disc_eq_mob h, CompactShape.disc_eq_mob h, vertexTwo_eq]
  exact norm_mob_conj_ofReal _ z

theorem norm_disc_refl_one_zero (z : ℂ) : ‖σ.disc 0 (σ.refl 1 z)‖ = ‖σ.disc 0 z‖ := by
  rw [CompactShape.disc_eq_mob h, CompactShape.disc_eq_mob h, mob_zero_left, mob_zero_left]
  change ‖exp (2 * (σ.θ₃ : ℂ) * I) * conj z‖ = ‖z‖
  rw [norm_mul, norm_exp_two, one_mul, Complex.norm_conj]

theorem norm_disc_refl_one_one (z : ℂ) :
    ‖σ.disc σ.vertexOne (σ.refl 1 z)‖ = ‖σ.disc σ.vertexOne z‖ := by
  rw [CompactShape.disc_eq_mob h, CompactShape.disc_eq_mob h, vertexOne_eq]
  change ‖mob ((sideOneThree σ : ℂ) * exp ((σ.θ₃ : ℂ) * I))
    (exp (2 * (σ.θ₃ : ℂ) * I) * conj z)‖ = _
  set u := exp ((σ.θ₃ : ℂ) * I) with hu
  have hu1 : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hcu : conj u * u = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu1]
    norm_num
  have e1 : exp (2 * (σ.θ₃ : ℂ) * I) * conj z = u * (u * conj z) := by
    rw [hu, ← mul_assoc, ← Complex.exp_add]
    ring_nf
  have e2 : z = u * (conj u * z) := by
    rw [← mul_assoc, mul_comm u, hcu, one_mul]
  rw [e1, mul_comm (sideOneThree σ : ℂ) u, mob_mul_mul hu1, norm_mul, hu1, one_mul]
  conv_rhs => rw [e2, mob_mul_mul hu1, norm_mul, hu1, one_mul]
  rw [← norm_mob_conj_ofReal, map_mul, Complex.conj_conj]

theorem norm_disc_refl_two_two {z : ℂ} (hz : ‖z‖ < 1) :
    ‖σ.disc σ.vertexTwo (σ.refl 2 z)‖ = ‖σ.disc σ.vertexTwo z‖ := by
  rw [CompactShape.disc_eq_mob h, CompactShape.disc_eq_mob h, mob_vertexTwo_refl_two h hz,
    norm_mul, norm_exp_neg_two, one_mul, Complex.norm_conj]

theorem norm_disc_vertexOne_eq {z : ℂ} (hz : ‖z‖ < 1) :
    ‖σ.disc σ.vertexOne z‖ = ‖mob (sideOneTwo σ : ℂ) (σ.rotTwo z)‖ := by
  rw [CompactShape.disc_eq_mob h, ← norm_rotOne h, rotOne_eq_mob_rotTwo h hz, norm_mul,
    norm_neg, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem norm_disc_refl_two_one {z : ℂ} (hz : ‖z‖ < 1) :
    ‖σ.disc σ.vertexOne (σ.refl 2 z)‖ = ‖σ.disc σ.vertexOne z‖ := by
  rw [norm_disc_vertexOne_eq h (norm_refl_lt_one h 2 hz), norm_disc_vertexOne_eq h hz,
    rotTwo_refl_two h hz, norm_mob_conj_ofReal]

omit h in
theorem wallSide_zero_zero : σ.wallSide 0 0 = 0 := by
  change (0 : ℂ).im = 0
  simp

omit h in
theorem wallSide_one_zero : σ.wallSide 1 0 = 0 := by
  rw [wallSide_one_apply]
  simp

omit h in
theorem wallSide_zero_vertexTwo : σ.wallSide 0 σ.vertexTwo = 0 := by
  change σ.vertexTwo.im = 0
  rw [vertexTwo_eq, ofReal_im]

omit h in
theorem wallSide_one_vertexOne : σ.wallSide 1 σ.vertexOne = 0 := by
  rw [wallSide_one_apply, vertexOne_eq, exp_ofReal_mul_I_eq]
  simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im]
  ring

theorem wallSide_two_vertexOne : σ.wallSide 2 σ.vertexOne = 0 := by
  rw [wallSide_two_eq_rotTwo h, rotTwo_vertexOne h, ofReal_im, zero_mul]

theorem wallSide_two_vertexTwo : σ.wallSide 2 σ.vertexTwo = 0 := by
  rw [wallSide_two_eq_rotTwo h, rotTwo_eq_mul_mob h, mob_self, mul_zero, zero_im, zero_mul]

theorem wallSide_two_zero : σ.wallSide 2 0 = sideTwoThree σ * Real.sin σ.θ₂ := by
  rw [wallSide_two_apply h]
  simp

theorem zero_mem_triangle : (0 : ℂ) ∈ σ.triangle := by
  refine ⟨?_, ?_⟩
  · rw [CompactShape.plane_hyp h]
    simp
  · intro i
    fin_cases i
    · exact (wallSide_zero_zero (σ := σ)).ge
    · exact (wallSide_one_zero (σ := σ)).ge
    · change 0 ≤ σ.wallSide 2 0
      rw [wallSide_two_zero h]
      exact mul_nonneg (sideTwoThree_pos h).le (sin_pos_of_le (θ₂_pos σ) (θ₂_le σ)).le

theorem vertexTwo_mem_triangle : σ.vertexTwo ∈ σ.triangle := by
  refine ⟨?_, ?_⟩
  · rw [CompactShape.plane_hyp h]
    simpa using norm_vertexTwo_lt_one h
  · intro i
    fin_cases i
    · exact (wallSide_zero_vertexTwo (σ := σ)).ge
    · change 0 ≤ σ.wallSide 1 σ.vertexTwo
      rw [wallSide_one_apply, vertexTwo_eq, ofReal_re, ofReal_im, mul_zero, sub_zero]
      exact mul_nonneg (sin_pos_of_le (θ₃_pos σ) (θ₃_le σ)).le (sideTwoThree_pos h).le
    · exact (wallSide_two_vertexTwo h).ge

theorem vertexOne_mem_triangle : σ.vertexOne ∈ σ.triangle := by
  refine ⟨?_, ?_⟩
  · rw [CompactShape.plane_hyp h]
    simpa using norm_vertexOne_lt_one h
  · intro i
    fin_cases i
    · change 0 ≤ σ.vertexOne.im
      rw [vertexOne_eq, exp_ofReal_mul_I_eq]
      simp only [mul_im, add_re, add_im, ofReal_re, ofReal_im, mul_re, I_re, I_im]
      have := mul_nonneg (sideOneThree_pos h).le (sin_pos_of_le (θ₃_pos σ) (θ₃_le σ)).le
      linarith
    · exact (wallSide_one_vertexOne (σ := σ)).ge
    · exact (wallSide_two_vertexOne h).ge

theorem wallSide_two_ofReal (x : ℝ) : σ.wallSide 2 (x : ℂ) =
    Real.sin σ.θ₂ * (sideTwoThree σ - x) * (1 - sideTwoThree σ * x) := by
  rw [wallSide_two_apply h]
  simp only [normSq_ofReal, ofReal_re, ofReal_im, mul_zero, sub_zero]
  ring

theorem wallSide_two_ray (x : ℝ) : sideOneThree σ * σ.wallSide 2 ((x : ℂ) * exp ((σ.θ₃ : ℂ) * I)) =
    sideTwoThree σ * Real.sin σ.θ₂ * (sideOneThree σ - x) * (1 - sideOneThree σ * x) := by
  have h0 := wallSide_two_vertexOne h
  rw [wallSide_two_apply h] at h0 ⊢
  rw [vertexOne_eq] at h0
  have hn : ∀ y : ℝ, normSq ((y : ℂ) * exp ((σ.θ₃ : ℂ) * I)) = y ^ 2 := by
    intro y
    rw [map_mul, normSq_ofReal, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    ring
  rw [hn] at h0 ⊢
  rw [exp_ofReal_mul_I_eq] at h0 ⊢
  simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
    sub_zero, mul_one, zero_add, add_zero, zero_mul] at h0 ⊢
  linear_combination x * h0

end Hyp

end HypFold

end GC.Seifert

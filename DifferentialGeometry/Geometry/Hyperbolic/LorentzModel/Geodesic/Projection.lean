/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.GromovProduct

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.GeodesicProjection

open DifferentialGeometry.Hyperbolic DifferentialGeometry.HyperbolicConvexity DifferentialGeometry.GromovBoundary

variable {n : ℕ}

theorem key_poly_ineq {A B C : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C) :
    16 * ((A*B*C - A*C + A - 1) * (A*B*C - B*C + B - 1))
    ≤ (4*C + 1) ^ 2 * (A*B - 1) ^ 2 := by
  have hpa : (0:ℝ) ≤ A - 1 := by linarith
  have hpb : (0:ℝ) ≤ B - 1 := by linarith
  have hpc : (0:ℝ) ≤ C - 1 := by linarith
  have hD : (4*C + 1) ^ 2 * (A*B - 1) ^ 2
      - 16 * ((A*B*C - A*C + A - 1) * (A*B*C - B*C + B - 1))
      = 8*(A-1) ^ 2*(B-1) ^ 2*(C-1) + 9*(A-1) ^ 2*(B-1) ^ 2
        + 16*(A-1) ^ 2*(B-1)*(C-1) ^ 2 + 32*(A-1) ^ 2*(B-1)*(C-1) + 18*(A-1) ^ 2*(B-1)
        + 16*(A-1) ^ 2*(C-1) ^ 2 + 24*(A-1) ^ 2*(C-1) + 9*(A-1) ^ 2
        + 16*(A-1)*(B-1) ^ 2*(C-1) ^ 2 + 32*(A-1)*(B-1) ^ 2*(C-1) + 18*(A-1)*(B-1) ^ 2
        + 16*(A-1)*(B-1)*(C-1) ^ 2 + 48*(A-1)*(B-1)*(C-1) + 18*(A-1)*(B-1)
        + 16*(B-1) ^ 2*(C-1) ^ 2 + 24*(B-1) ^ 2*(C-1) + 9*(B-1) ^ 2 := by
    ring
  have hnn : (0:ℝ) ≤ 8*(A-1) ^ 2*(B-1) ^ 2*(C-1) + 9*(A-1) ^ 2*(B-1) ^ 2
      + 16*(A-1) ^ 2*(B-1)*(C-1) ^ 2 + 32*(A-1) ^ 2*(B-1)*(C-1) + 18*(A-1) ^ 2*(B-1)
      + 16*(A-1) ^ 2*(C-1) ^ 2 + 24*(A-1) ^ 2*(C-1) + 9*(A-1) ^ 2
      + 16*(A-1)*(B-1) ^ 2*(C-1) ^ 2 + 32*(A-1)*(B-1) ^ 2*(C-1) + 18*(A-1)*(B-1) ^ 2
      + 16*(A-1)*(B-1)*(C-1) ^ 2 + 48*(A-1)*(B-1)*(C-1) + 18*(A-1)*(B-1)
      + 16*(B-1) ^ 2*(C-1) ^ 2 + 24*(B-1) ^ 2*(C-1) + 9*(B-1) ^ 2 := by
    positivity
  linarith [hD, hnn]

theorem cosh_add_exp (s t : ℝ) :
    Real.cosh (s + t)
      = ((Real.exp s * Real.exp t) ^ 2 + 1) / (2 * (Real.exp s * Real.exp t)) := by
  rw [Real.cosh_eq, Real.exp_add, Real.exp_neg, Real.exp_add]
  field_simp [Real.exp_ne_zero s, Real.exp_ne_zero t]

theorem sinh_add_exp (s t : ℝ) :
    Real.sinh (s + t)
      = ((Real.exp s * Real.exp t) ^ 2 - 1) / (2 * (Real.exp s * Real.exp t)) := by
  rw [Real.sinh_eq, Real.exp_add, Real.exp_neg, Real.exp_add]
  field_simp [Real.exp_ne_zero s, Real.exp_ne_zero t]

noncomputable def orthCoeff (o x y : HUpper n) : ℝ :=
  - lorB o.val (dirVec x y)

theorem cosh_dist_geod (o x y : HUpper n) (hd : x ≠ y) (t : ℝ) :
    Real.cosh (dist o (geodFromTo x y hd t))
      = Real.cosh t * Real.cosh (dist o x) + Real.sinh t * orthCoeff o x y := by
  rw [cosh_dist]
  change - lorB o.val (Real.cosh t • x.val + Real.sinh t • dirVec x y) = _
  rw [lorB_add_right, lorB_smul_right, lorB_smul_right, cosh_dist o x,
    show orthCoeff o x y = - lorB o.val (dirVec x y) from rfl]
  ring

theorem orthCoeff_sq_le (o x y : HUpper n) (hd : x ≠ y) :
    orthCoeff o x y ^ 2 ≤ Real.sinh (dist o x) ^ 2 := by
  set A := dist o x with hA
  set K := orthCoeff o x y with hK
  set w := o.val - Real.cosh A • x.val with hw
  have h1 : lorB o.val x.val = - Real.cosh A := by rw [cosh_dist o x]; ring
  have hwor : lorB w x.val = 0 := by
    rw [hw, lorB_sub_left, lorB_smul_left, x.is_unit, h1]
    ring
  have h3 : lorB x.val o.val = - Real.cosh A := by rw [lorB_comm x.val o.val]; exact h1
  have hww : lorB w w = Real.sinh A ^ 2 := by
    have h2 : Real.cosh A ^ 2 - Real.sinh A ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq A
    rw [hw]
    simp only [lorB_sub_left, lorB_sub_right, lorB_smul_left, lorB_smul_right, o.is_unit,
      x.is_unit, h1, h3]
    nlinarith [h2]
  have hdiror : lorB (dirVec x y) x.val = 0 := lorB_dirVec_left x y
  have hcs := lorB_sq_le_of_orth x.is_unit hwor hdiror
  rw [hww, lorB_dirVec_self hd, mul_one] at hcs
  have hKo : lorB o.val (dirVec x y) = lorB w (dirVec x y) := by
    have h3 : o.val = Real.cosh A • x.val + w := by rw [hw]; abel
    rw [h3, lorB_add_left, lorB_smul_left, lorB_comm x.val (dirVec x y),
      lorB_dirVec_left x y]
    ring
  have hK2 : K ^ 2 = lorB w (dirVec x y) ^ 2 := by
    rw [hK]
    change (- lorB o.val (dirVec x y)) ^ 2 = lorB w (dirVec x y) ^ 2
    rw [hKo, neg_sq]
  rw [hK2]
  exact hcs

theorem cosh_dist_geod_eq (o x y : HUpper n) (hd : x ≠ y) :
    ∃ R t₀ : ℝ, 1 ≤ R ∧ (∀ t : ℝ,
      Real.cosh (dist o (geodFromTo x y hd t)) = R * Real.cosh (t - t₀)) := by
  set A := dist o x with hA
  set K := orthCoeff o x y with hK
  have hKbound : K ^ 2 ≤ Real.sinh A ^ 2 := orthCoeff_sq_le o x y hd
  have hA0 : 0 ≤ A := dist_nonneg
  have hsinhA : 0 ≤ Real.sinh A := sinh_nonneg_of_nonneg hA0
  have hR2 : 1 ≤ Real.cosh A ^ 2 - K ^ 2 := by
    have h1 : Real.cosh A ^ 2 - Real.sinh A ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq A
    nlinarith [h1, hKbound, hsinhA, Real.cosh_pos A]
  set R := Real.sqrt (Real.cosh A ^ 2 - K ^ 2) with hR
  have hR1 : (1:ℝ) ≤ R := by
    have h2 : Real.sqrt 1 ≤ R := Real.sqrt_le_sqrt (by simpa using hR2)
    rwa [Real.sqrt_one] at h2
  have hRsq : R ^ 2 = Real.cosh A ^ 2 - K ^ 2 := Real.sq_sqrt (by linarith [hR2])
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  have hαR : 1 ≤ Real.cosh A / R := by
    rw [le_div_iff₀ hRpos, one_mul]
    have h2 : R ^ 2 ≤ Real.cosh A ^ 2 := by rw [hRsq]; nlinarith [sq_nonneg K]
    have h3 := sq_le_sq.mp h2
    rwa [abs_of_nonneg hRpos.le, abs_of_pos (Real.cosh_pos A)] at h3
  set t₀ := if K ≤ 0 then Real.arcosh (Real.cosh A / R) else - Real.arcosh (Real.cosh A / R)
    with ht₀
  have hcosh_t0 : Real.cosh t₀ = Real.cosh A / R := by
    by_cases hKl : K ≤ 0
    · rw [ht₀, ite_eq_left hKl, Real.cosh_arcosh hαR]
    · rw [ht₀, ite_eq_right hKl, Real.cosh_neg, Real.cosh_arcosh hαR]
  have hR2' : (Real.cosh A / R) ^ 2 - 1 = (K / R) ^ 2 := by
    field_simp [hRpos.ne']
    rw [hRsq]
    ring
  have hsinh_t0 : Real.sinh t₀ = -K / R := by
    by_cases hKl : K ≤ 0
    · rw [ht₀, ite_eq_left hKl, Real.sinh_arcosh hαR, hR2', Real.sqrt_sq_eq_abs,
        abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hKl hRpos.le)]
      ring
    · rw [ht₀, ite_eq_right hKl, Real.sinh_neg, Real.sinh_arcosh hαR, hR2', Real.sqrt_sq_eq_abs,
        abs_of_nonneg (div_nonneg (le_of_not_ge hKl) hRpos.le)]
      ring
  refine ⟨R, t₀, hR1, fun t => ?_⟩
  rw [cosh_dist_geod o x y hd t, Real.cosh_sub, hcosh_t0, hsinh_t0]
  field_simp [hRpos.ne']
  ring

theorem exp_mul_cosh_le_two_cosh_add (T : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Real.exp T * Real.cosh s ≤ 2 * Real.cosh (T + s) := by
  have h1 : Real.cosh s ≤ Real.exp s := cosh_le_exp hs
  have h2 : Real.exp T * Real.cosh s ≤ Real.exp T * Real.exp s :=
    mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  have h3 : Real.exp T * Real.exp s = Real.exp (T + s) := by rw [Real.exp_add]
  have h4 : Real.exp (T + s) ≤ 2 * Real.cosh (T + s) := by
    rw [Real.cosh_eq]
    have h5 : (0:ℝ) ≤ Real.exp (-(T + s)) := (Real.exp_pos _).le
    linarith [h5]
  linarith [h2, h3, h4]

theorem interior_bound {R u v P : ℝ} (hR : 1 ≤ R) (hu : 0 ≤ u) (hv : 0 ≤ v) (hP : 0 ≤ P)
    (hT : 0 < u + v)
    (hrel : R ^ 2 * Real.sinh (u + v) ^ 2
      = 2 * Real.cosh (u + P) * Real.cosh (v + P) * Real.cosh (u + v)
        - Real.cosh (u + P) ^ 2 - Real.cosh (v + P) ^ 2) :
    R ≤ Real.cosh (P + Real.log 2) := by
  set a := Real.exp u with ha_def
  set b := Real.exp v with hb_def
  set c := Real.exp P with hc_def
  have ha0 : (0:ℝ) < a := Real.exp_pos u
  have hb0 : (0:ℝ) < b := Real.exp_pos v
  have hc0 : (0:ℝ) < c := Real.exp_pos P
  have ha0' : a ≠ 0 := ne_of_gt ha0
  have hb0' : b ≠ 0 := ne_of_gt hb0
  have hc0' : c ≠ 0 := ne_of_gt hc0
  have ha1sq : (1:ℝ) ≤ a^2 := one_le_pow₀ (Real.one_le_exp_iff.mpr hu)
  have hb1sq : (1:ℝ) ≤ b^2 := one_le_pow₀ (Real.one_le_exp_iff.mpr hv)
  have hc1sq : (1:ℝ) ≤ c^2 := one_le_pow₀ (Real.one_le_exp_iff.mpr hP)
  have hcoshA : Real.cosh (u + P) = ((a * c) ^ 2 + 1) / (2 * (a * c)) := cosh_add_exp u P
  have hcoshB : Real.cosh (v + P) = ((b * c) ^ 2 + 1) / (2 * (b * c)) := cosh_add_exp v P
  have hcoshT : Real.cosh (u + v) = ((a * b) ^ 2 + 1) / (2 * (a * b)) := cosh_add_exp u v
  have hsinhT : Real.sinh (u + v) = ((a * b) ^ 2 - 1) / (2 * (a * b)) := sinh_add_exp u v
  have hcoshP2 : Real.cosh (P + Real.log 2) = (4 * c^2 + 1) / (4 * c) := by
    have h1 := cosh_add_exp P (Real.log 2)
    rw [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h1
    rw [← hc_def] at h1
    rw [h1]
    field_simp [hc0']
    ring
  have hnum_id : (2 * Real.cosh (u + P) * Real.cosh (v + P) * Real.cosh (u + v)
        - Real.cosh (u + P) ^ 2 - Real.cosh (v + P) ^ 2) * (4 * a^2 * b^2 * c^2)
      = (a^2*b^2*c^2 - a^2*c^2 + a^2 - 1) * (a^2*b^2*c^2 - b^2*c^2 + b^2 - 1) := by
    rw [hcoshA, hcoshB, hcoshT]
    field_simp [ha0', hb0', hc0', mul_ne_zero ha0' hc0', mul_ne_zero hb0' hc0',
      mul_ne_zero ha0' hb0']
    ring
  have hsinhT2 : Real.sinh (u + v) ^ 2 = (a^2*b^2 - 1) ^ 2 / (4 * a^2 * b^2) := by
    rw [hsinhT]
    field_simp [ha0', hb0', mul_ne_zero ha0' hb0']
    ring
  have hRHS : Real.cosh (P + Real.log 2) ^ 2 * (Real.sinh (u + v) ^ 2 * (4*a^2*b^2*c^2))
      = ((4*c^2+1) ^ 2 * (a^2*b^2-1) ^ 2)/16 := by
    rw [hcoshP2, hsinhT2]
    field_simp [ha0', hb0', hc0']
    ring
  have hLHS : R ^ 2 * (Real.sinh (u + v) ^ 2 * (4*a^2*b^2*c^2))
      = (a^2*b^2*c^2 - a^2*c^2 + a^2 - 1) * (a^2*b^2*c^2 - b^2*c^2 + b^2 - 1) := by
    linear_combination (4*a^2*b^2*c^2) * hrel + hnum_id
  have hkey := key_poly_ineq ha1sq hb1sq hc1sq
  have hstep : R ^ 2 * (Real.sinh (u + v) ^ 2 * (4*a^2*b^2*c^2))
      ≤ Real.cosh (P + Real.log 2) ^ 2 * (Real.sinh (u + v) ^ 2 * (4*a^2*b^2*c^2)) := by
    rw [hLHS, hRHS]
    linarith [hkey]
  have hfac : (0:ℝ) < Real.sinh (u + v) ^ 2 * (4*a^2*b^2*c^2) := by
    have hsinhpos : (0:ℝ) < Real.sinh (u + v) := Real.sinh_pos_iff.mpr hT
    positivity
  have hR2le : R ^ 2 ≤ Real.cosh (P + Real.log 2) ^ 2 := by
    by_contra hcon
    push Not at hcon
    have hlt := mul_lt_mul_of_pos_right hcon hfac
    linarith [hstep, hlt]
  have h1 := Real.sqrt_le_sqrt hR2le
  rwa [Real.sqrt_sq (zero_le_one.trans hR), Real.sqrt_sq (Real.cosh_pos _).le] at h1

theorem exists_dist_geodFromTo_le_gromovProduct_add (o x y : HUpper n) (hd : x ≠ y) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ dist x y ∧
      dist o (geodFromTo x y hd t) ≤ gromovProduct o x y + Real.log 2 := by
  obtain ⟨R, t₀, hR1, hform⟩ := cosh_dist_geod_eq o x y hd
  have hRpos : (0:ℝ) < R := one_pos.trans_le hR1
  have hT0 : (0:ℝ) < dist x y := dist_pos.mpr hd
  have hcoshA : Real.cosh (dist o x) = R * Real.cosh t₀ := by
    have h1 := hform 0
    rw [geodFromTo_zero hd, zero_sub, Real.cosh_neg] at h1
    exact h1
  have hcoshB : Real.cosh (dist o y) = R * Real.cosh (dist x y - t₀) := by
    have h1 := hform (dist x y)
    rwa [geodFromTo_dist hd] at h1
  have hPeq : gromovProduct o x y = (dist o x + dist o y - dist x y) / 2 := rfl
  have hP0 : (0:ℝ) ≤ gromovProduct o x y := gromovProduct_nonneg o x y
  have hlog2nn : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 * 2 by norm_num, Real.log_mul two_ne_zero two_ne_zero]
    ring
  rcases le_or_gt t₀ 0 with ht0 | ht0
  · refine ⟨0, le_refl 0, hT0.le, ?_⟩
    rw [geodFromTo_zero hd]
    set s := -t₀ with hs_def
    have hs0 : (0:ℝ) ≤ s := by rw [hs_def]; exact neg_nonneg.mpr ht0
    have ht0' : t₀ = -s := by rw [hs_def]; ring
    have hcoshA' : Real.cosh (dist o x) = R * Real.cosh s := by
      have e : Real.cosh t₀ = Real.cosh s := by rw [ht0', Real.cosh_neg]
      rw [hcoshA, e]
    have hcoshB' : Real.cosh (dist o y) = R * Real.cosh (dist x y + s) := by
      have e : dist x y - t₀ = dist x y + s := by rw [ht0']; ring
      rw [hcoshB, e]
    have h1 : Real.exp (dist o x) ≤ 2 * Real.cosh (dist o x) := by
      have hsc := sinh_le_cosh (dist o x)
      rw [← Real.cosh_add_sinh (dist o x)]
      linarith [hsc]
    have hexp : Real.exp (dist o x + dist x y) ≤ 4 * Real.exp (dist o y) := by
      calc Real.exp (dist o x + dist x y)
          = Real.exp (dist o x) * Real.exp (dist x y) := by rw [Real.exp_add]
        _ ≤ 2 * Real.cosh (dist o x) * Real.exp (dist x y) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = 2 * R * (Real.exp (dist x y) * Real.cosh s) := by rw [hcoshA']; ring
        _ ≤ 2 * R * (2 * Real.cosh (dist x y + s)) :=
            mul_le_mul_of_nonneg_left (exp_mul_cosh_le_two_cosh_add (dist x y) hs0)
              (mul_nonneg two_pos.le hRpos.le)
        _ = 4 * Real.cosh (dist o y) := by rw [hcoshB']; ring
        _ ≤ 4 * Real.exp (dist o y) :=
            mul_le_mul_of_nonneg_left (cosh_le_exp dist_nonneg) four_pos.le
    have hlog : dist o x + dist x y ≤ Real.log 4 + dist o y := by
      have h3 : Real.exp (Real.log 4 + dist o y) = 4 * Real.exp (dist o y) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 4)]
      have h2 : Real.exp (dist o x + dist x y)
          ≤ Real.exp (Real.log 4 + dist o y) := by
        rw [h3]; exact hexp
      exact Real.exp_le_exp.mp h2
    rw [hPeq]
    linarith [hlog, hlog4]
  · rcases le_or_gt (dist x y) t₀ with htT | htT
    · refine ⟨dist x y, hT0.le, le_refl _, ?_⟩
      rw [geodFromTo_dist hd]
      set s := t₀ - dist x y with hs_def
      have hs0 : (0:ℝ) ≤ s := by rw [hs_def]; linarith [htT]
      have ht0' : t₀ = dist x y + s := by rw [hs_def]; ring
      have hcoshB' : Real.cosh (dist o y) = R * Real.cosh s := by
        have e1 : dist x y - t₀ = -s := by rw [ht0']; ring
        have e : Real.cosh (dist x y - t₀) = Real.cosh s := by rw [e1, Real.cosh_neg]
        rw [hcoshB, e]
      have hcoshA' : Real.cosh (dist o x) = R * Real.cosh (dist x y + s) := by
        rw [hcoshA, ht0']
      have h1 : Real.exp (dist o y) ≤ 2 * Real.cosh (dist o y) := by
        have hsc := sinh_le_cosh (dist o y)
        rw [← Real.cosh_add_sinh (dist o y)]
        linarith [hsc]
      have hexp : Real.exp (dist o y + dist x y) ≤ 4 * Real.exp (dist o x) := by
        calc Real.exp (dist o y + dist x y)
            = Real.exp (dist o y) * Real.exp (dist x y) := by rw [Real.exp_add]
          _ ≤ 2 * Real.cosh (dist o y) * Real.exp (dist x y) :=
              mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
          _ = 2 * R * (Real.exp (dist x y) * Real.cosh s) := by rw [hcoshB']; ring
          _ ≤ 2 * R * (2 * Real.cosh (dist x y + s)) :=
              mul_le_mul_of_nonneg_left (exp_mul_cosh_le_two_cosh_add (dist x y) hs0)
                (mul_nonneg two_pos.le hRpos.le)
          _ = 4 * Real.cosh (dist o x) := by rw [hcoshA']; ring
          _ ≤ 4 * Real.exp (dist o x) :=
              mul_le_mul_of_nonneg_left (cosh_le_exp dist_nonneg) four_pos.le
      have hlog : dist o y + dist x y ≤ Real.log 4 + dist o x := by
        have h3 : Real.exp (Real.log 4 + dist o x) = 4 * Real.exp (dist o x) := by
          rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 4)]
        have h2 : Real.exp (dist o y + dist x y)
            ≤ Real.exp (Real.log 4 + dist o x) := by
          rw [h3]; exact hexp
        exact Real.exp_le_exp.mp h2
      rw [hPeq]
      linarith [hlog, hlog4]
    · refine ⟨t₀, ht0.le, htT.le, ?_⟩
      have hdist : dist o (geodFromTo x y hd t₀) = Real.arcosh R := by
        have h1 := hform t₀
        rw [sub_self, Real.cosh_zero, mul_one] at h1
        rw [← h1, Real.arcosh_cosh dist_nonneg]
      rw [hdist]
      have hcs := Real.cosh_sq_sub_sinh_sq t₀
      have hcsT := Real.cosh_sq_sub_sinh_sq (dist x y)
      have hRt0 : (R * Real.cosh t₀) ^ 2 = Real.cosh (dist o x) ^ 2 := by
        rw [← hcoshA]
      have h1 : Real.cosh (dist o y) = Real.cosh (dist x y) * (R * Real.cosh t₀)
          - Real.sinh (dist x y) * (R * Real.sinh t₀) := by
        rw [hcoshB, Real.cosh_sub]; ring
      have hSt0 : Real.sinh (dist x y) * (R * Real.sinh t₀)
          = Real.cosh (dist x y) * Real.cosh (dist o x) - Real.cosh (dist o y) := by
        rw [← hcoshA] at h1
        linarith [h1]
      have hrel : R ^ 2 * Real.sinh (dist x y) ^ 2
          = 2 * Real.cosh (dist o x) * Real.cosh (dist o y) * Real.cosh (dist x y)
            - Real.cosh (dist o x) ^ 2 - Real.cosh (dist o y) ^ 2 := by
        linear_combination Real.sinh (dist x y) ^ 2 * hRt0
          - (2 * (Real.cosh (dist x y) * Real.cosh (dist o x) - Real.cosh (dist o y))
            + (Real.sinh (dist x y) * (R * Real.sinh t₀)
              - (Real.cosh (dist x y) * Real.cosh (dist o x)
                - Real.cosh (dist o y)))) * hSt0
          - Real.cosh (dist o x) ^ 2 * hcsT - R ^ 2 * Real.sinh (dist x y) ^ 2 * hcs
      have hu : (0:ℝ) ≤ dist o x - gromovProduct o x y := by
        have h := dist_triangle o x y
        rw [hPeq]
        linarith [h]
      have hv : (0:ℝ) ≤ dist o y - gromovProduct o x y := by
        have h := dist_triangle o y x
        rw [dist_comm y x] at h
        rw [hPeq]
        linarith [h]
      have hTuv : dist x y
          = (dist o x - gromovProduct o x y) + (dist o y - gromovProduct o x y) := by
        rw [hPeq]; ring
      have hTuv0 : (0:ℝ)
          < (dist o x - gromovProduct o x y) + (dist o y - gromovProduct o x y) := by
        rw [← hTuv]; exact hT0
      have hRle : R ≤ Real.cosh (gromovProduct o x y + Real.log 2) := by
        apply interior_bound hR1 hu hv hP0 hTuv0
        have e1 : dist o x - gromovProduct o x y + gromovProduct o x y
            = dist o x := by ring
        have e2 : dist o y - gromovProduct o x y + gromovProduct o x y
            = dist o y := by ring
        rw [e1, e2, ← hTuv]
        exact hrel
      rw [← Real.arcosh_cosh (add_nonneg hP0 hlog2nn)]
      exact (Real.arcosh_le_arcosh hRpos (Real.cosh_pos _)).mpr hRle

theorem gromovProduct_ge_of_forall_dist_ge (o x y : HUpper n) (hd : x ≠ y) {M : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ dist x y → M ≤ dist o (geodFromTo x y hd t)) :
    M - Real.log 2 ≤ gromovProduct o x y := by
  obtain ⟨t, ht0, htT, ht⟩ := exists_dist_geodFromTo_le_gromovProduct_add o x y hd
  linarith [h t ht0 htT, ht]

end DifferentialGeometry.GeodesicProjection

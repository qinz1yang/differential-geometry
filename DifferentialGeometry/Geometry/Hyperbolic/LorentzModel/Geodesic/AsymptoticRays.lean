/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.GromovProduct

open DifferentialGeometry.ProjectiveOrthogonalGroup Filter

namespace DifferentialGeometry.AsymptoticRays

open DifferentialGeometry.Hyperbolic DifferentialGeometry.HyperbolicAction DifferentialGeometry.HyperbolicFaithful
open DifferentialGeometry.HyperbolicBoundary DifferentialGeometry.BoundaryTopology
open DifferentialGeometry.HyperbolicConvexity DifferentialGeometry.GromovBoundary

variable {n : ℕ}

theorem lorB_hUpper_boundary_neg (o : HUpper n) (ξ : BoundaryH n) :
    lorB o.val ξ.val < 0 := by
  have hξ : sdot ξ.val ξ.val = 1 := sdot_self_of_boundary ξ
  have ho : sdot o.val o.val = tc o.val ^ 2 - 1 := by
    have h1 := HUpper.tc_sq o
    linarith [h1]
  have hcs := abs_sdot_le o.val ξ.val
  rw [ho, hξ, Real.sqrt_one, mul_one] at hcs
  have htc : 0 < tc o.val := o.future
  have hlt : Real.sqrt (tc o.val ^ 2 - 1) < tc o.val := by
    rw [Real.sqrt_lt' htc]
    nlinarith [htc]
  have hlor : lorB o.val ξ.val = sdot o.val ξ.val - tc o.val := by
    rw [lorB, ξ.tc_eq]
    ring
  rw [hlor]
  have hle : sdot o.val ξ.val ≤ Real.sqrt (tc o.val ^ 2 - 1) :=
    le_trans (le_abs_self _) hcs
  linarith [hle, hlt]

noncomputable def dirTo (o : HUpper n) (ξ : BoundaryH n) : LorVec n :=
  (- lorB o.val ξ.val)⁻¹ • (ξ.val + lorB o.val ξ.val • o.val)

theorem lorB_dirTo_self (o : HUpper n) (ξ : BoundaryH n) :
    lorB (dirTo o ξ) (dirTo o ξ) = 1 := by
  have hL : lorB o.val ξ.val ≠ 0 := (lorB_hUpper_boundary_neg o ξ).ne
  change lorB ((- lorB o.val ξ.val)⁻¹ • (ξ.val + lorB o.val ξ.val • o.val))
      ((- lorB o.val ξ.val)⁻¹ • (ξ.val + lorB o.val ξ.val • o.val)) = 1
  rw [lorB_smul_left, lorB_smul_right]
  have hexp : lorB (ξ.val + lorB o.val ξ.val • o.val) (ξ.val + lorB o.val ξ.val • o.val)
      = lorB o.val ξ.val ^ 2 := by
    rw [lorB_add_left, lorB_add_right, lorB_add_right, lorB_smul_left, lorB_smul_right,
      lorB_smul_left, lorB_smul_right, ξ.is_null, o.is_unit, lorB_comm ξ.val o.val]
    ring
  rw [hexp]
  rw [show (- lorB o.val ξ.val)⁻¹ * ((- lorB o.val ξ.val)⁻¹ * lorB o.val ξ.val ^ 2)
      = ((- lorB o.val ξ.val)⁻¹ * lorB o.val ξ.val) ^ 2 from by ring]
  rw [inv_neg, neg_mul, inv_mul_cancel₀ hL]
  norm_num

theorem lorB_dirTo_left (o : HUpper n) (ξ : BoundaryH n) :
    lorB (dirTo o ξ) o.val = 0 := by
  change lorB ((- lorB o.val ξ.val)⁻¹ • (ξ.val + lorB o.val ξ.val • o.val)) o.val = 0
  rw [lorB_smul_left, lorB_add_left, lorB_smul_left, o.is_unit, lorB_comm ξ.val o.val]
  ring

noncomputable def rayTo (o : HUpper n) (ξ : BoundaryH n) (t : ℝ) : HUpper n where
  val := Real.cosh t • o.val + Real.sinh t • dirTo o ξ
  is_unit := by
    have huu : lorB (dirTo o ξ) (dirTo o ξ) = 1 := lorB_dirTo_self o ξ
    have huo : lorB (dirTo o ξ) o.val = 0 := lorB_dirTo_left o ξ
    have huo2 : lorB o.val (dirTo o ξ) = 0 := by rw [lorB_comm]; exact huo
    have hcs : Real.cosh t ^ 2 - Real.sinh t ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq t
    simp only [lorB_add_left, lorB_add_right, lorB_smul_left, lorB_smul_right]
    rw [o.is_unit, huu, huo, huo2]
    nlinarith [hcs]
  future := by
    have hB := abs_tc_lt_tc_of_orth_unit o (lorB_dirTo_self o ξ) (lorB_dirTo_left o ξ)
    have hA : 0 < tc o.val := o.future
    have hcosh : 0 < Real.cosh t := zero_lt_one.trans_le (Real.one_le_cosh t)
    have hsinc : |Real.sinh t| < Real.cosh t := by
      have h1 : Real.cosh t ^ 2 - Real.sinh t ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq t
      have h2 : Real.sinh t ^ 2 < Real.cosh t ^ 2 := by nlinarith [h1]
      have h3 := sq_lt_sq.mp h2
      rwa [abs_of_pos hcosh] at h3
    have hstep1 : - (|Real.sinh t| * |tc (dirTo o ξ)|)
        ≤ Real.sinh t * tc (dirTo o ξ) := by
      rw [← abs_mul]
      exact neg_abs_le _
    have hstep2 : |Real.sinh t| * |tc (dirTo o ξ)| < Real.cosh t * tc o.val := by
      rcases eq_or_lt_of_le (abs_nonneg (Real.sinh t)) with hs0 | hspos
      · rw [hs0.symm, zero_mul]
        exact mul_pos hcosh hA
      · rcases eq_or_lt_of_le (abs_nonneg (tc (dirTo o ξ))) with hu0 | hupos
        · rw [hu0.symm, mul_zero]
          exact mul_pos hcosh hA
        · exact mul_lt_mul hsinc hB.le hupos hcosh.le
    rw [tc_add, tc_smul, tc_smul]
    linarith [hstep1, hstep2, hA, hcosh]

theorem rayTo_zero (o : HUpper n) (ξ : BoundaryH n) : rayTo o ξ 0 = o := by
  apply HUpper.ext
  change Real.cosh 0 • o.val + Real.sinh 0 • dirTo o ξ = o.val
  rw [Real.cosh_zero, Real.sinh_zero, zero_smul, add_zero, one_smul]

theorem lorB_rayTo_rayTo (o : HUpper n) (ξ : BoundaryH n) (t s : ℝ) :
    lorB (rayTo o ξ t).val (rayTo o ξ s).val = - Real.cosh (t - s) := by
  have huu : lorB (dirTo o ξ) (dirTo o ξ) = 1 := lorB_dirTo_self o ξ
  have huo : lorB (dirTo o ξ) o.val = 0 := lorB_dirTo_left o ξ
  have huo2 : lorB o.val (dirTo o ξ) = 0 := by rw [lorB_comm]; exact huo
  change lorB (Real.cosh t • o.val + Real.sinh t • dirTo o ξ)
      (Real.cosh s • o.val + Real.sinh s • dirTo o ξ) = _
  simp only [lorB_add_left, lorB_add_right, lorB_smul_left, lorB_smul_right]
  rw [o.is_unit, huu, huo, huo2, Real.cosh_sub]
  ring

theorem dist_rayTo (o : HUpper n) (ξ : BoundaryH n) (t s : ℝ) :
    dist (rayTo o ξ t) (rayTo o ξ s) = |t - s| := by
  change HUpper.hdist _ _ = |t - s|
  unfold HUpper.hdist
  rw [lorB_rayTo_rayTo, neg_neg]
  rcases le_or_gt 0 (t - s) with hts | hts
  · rw [abs_of_nonneg hts]
    exact Real.arcosh_cosh hts
  · have h2 : (0 : ℝ) ≤ s - t := by linarith
    rw [abs_of_neg hts, ← Real.cosh_neg (t - s), neg_sub]
    exact Real.arcosh_cosh h2

theorem dist_rayTo_self (o : HUpper n) (ξ : BoundaryH n) (t : ℝ) :
    dist o (rayTo o ξ t) = |t| := by
  have h : dist (rayTo o ξ 0) (rayTo o ξ t) = |0 - t| := dist_rayTo o ξ 0 t
  rw [rayTo_zero, zero_sub, abs_neg] at h
  exact h

theorem smul_smul_inv_cancel {c d : ℝ} (hc : c ≠ 0) (v : LorVec n) :
    (d * c⁻¹) • (c • v) = d • v := by
  rw [smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]

theorem radial_rayTo (o : HUpper n) (ξ : BoundaryH n) (t : ℝ) :
    (tc (rayTo o ξ t).val)⁻¹ • (rayTo o ξ t).val
      = (tc o.val + (Real.sinh t / Real.cosh t) * tc (dirTo o ξ))⁻¹
        • (o.val + (Real.sinh t / Real.cosh t) • dirTo o ξ) := by
  have htc : tc (rayTo o ξ t).val
      = Real.cosh t * tc o.val + Real.sinh t * tc (dirTo o ξ) := by
    change tc (Real.cosh t • o.val + Real.sinh t • dirTo o ξ) = _
    rw [tc_add, tc_smul, tc_smul]
  have hc : (0:ℝ) < Real.cosh t := Real.cosh_pos t
  have h1 : Real.cosh t * tc o.val + Real.sinh t * tc (dirTo o ξ)
      = Real.cosh t * (tc o.val + (Real.sinh t / Real.cosh t) * tc (dirTo o ξ)) := by
    rw [mul_add]
    congr 1
    field_simp
  have h2 : Real.cosh t • o.val + Real.sinh t • dirTo o ξ
      = Real.cosh t • (o.val + (Real.sinh t / Real.cosh t) • dirTo o ξ) := by
    rw [smul_add, smul_smul]
    have hsc : Real.sinh t = Real.cosh t * (Real.sinh t / Real.cosh t) := by
      field_simp
    rw [← hsc]
  change (tc (rayTo o ξ t).val)⁻¹ • (Real.cosh t • o.val + Real.sinh t • dirTo o ξ) = _
  rw [htc, h1, h2, mul_inv_rev, smul_smul_inv_cancel hc.ne']

theorem tendsto_sinh_div_cosh_atTop :
    Tendsto (fun m : ℕ => Real.sinh (m : ℝ) / Real.cosh (m : ℝ)) atTop (nhds 1) := by
  have hexp : Filter.Tendsto (fun m : ℕ => Real.exp (-2 * (m : ℝ))) Filter.atTop
      (nhds 0) := by
    have h1 : ∀ m : ℕ, Real.exp (-2 * (m : ℝ)) = (Real.exp (-2)) ^ m := by
      intro m
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hr1 : Real.exp (-2) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_strictMono (by norm_num)
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-2)).le hr1
    exact h2.congr' (Filter.Eventually.of_forall fun m => (h1 m).symm)
  have hlim : Filter.Tendsto (fun m : ℕ => (1 - Real.exp (-2 * (m : ℝ))) /
      (1 + Real.exp (-2 * (m : ℝ)))) Filter.atTop (nhds ((1 - 0) / (1 + 0))) :=
    (tendsto_const_nhds.sub hexp).div (tendsto_const_nhds.add hexp) (by norm_num)
  have h3 : ∀ m : ℕ, Real.sinh (m : ℝ) / Real.cosh (m : ℝ)
      = (1 - Real.exp (-2 * (m : ℝ))) / (1 + Real.exp (-2 * (m : ℝ))) := by
    intro m
    have he : Real.exp (m : ℝ) ≠ 0 := (Real.exp_pos _).ne'
    have hee : Real.exp (m : ℝ) * Real.exp (m : ℝ) ≠ 0 := mul_ne_zero he he
    have hrr : Real.exp (-2 * (m : ℝ)) = (Real.exp (m : ℝ) * Real.exp (m : ℝ))⁻¹ := by
      rw [show (-2 : ℝ) * (m : ℝ) = -((m : ℝ) + (m : ℝ)) from by ring, Real.exp_neg,
        Real.exp_add]
    rw [Real.sinh_eq, Real.cosh_eq, hrr, Real.exp_neg]
    field_simp
  have h4 : ((1 : ℝ) - 0) / (1 + 0) = 1 := by norm_num
  rw [h4] at hlim
  exact hlim.congr' (Filter.Eventually.of_forall fun m => (h3 m).symm)

theorem tendsto_rayTo (o : HUpper n) (ξ : BoundaryH n) :
    ConvergesToBoundary (fun m : ℕ => rayTo o ξ (m : ℝ)) ξ := by
  have htan := tendsto_sinh_div_cosh_atTop
  have hL : lorB o.val ξ.val ≠ 0 := (lorB_hUpper_boundary_neg o ξ).ne
  have hB := abs_tc_lt_tc_of_orth_unit o (lorB_dirTo_self o ξ) (lorB_dirTo_left o ξ)
  have hDpos : 0 < tc o.val + tc (dirTo o ξ) := by
    have htc : 0 < tc o.val := o.future
    have hle := neg_abs_le (tc (dirTo o ξ))
    linarith [hB, htc, hle]
  have hid1 : o.val + dirTo o ξ = (- lorB o.val ξ.val)⁻¹ • ξ.val := by
    rw [dirTo, smul_add, smul_smul]
    have hsc : (- lorB o.val ξ.val)⁻¹ * lorB o.val ξ.val = -1 := by
      rw [inv_neg, neg_mul, inv_mul_cancel₀ hL]
    rw [hsc, neg_one_smul]
    have : o.val + ((- lorB o.val ξ.val)⁻¹ • ξ.val + -o.val)
        = (- lorB o.val ξ.val)⁻¹ • ξ.val := by
      rw [add_comm o.val ((- lorB o.val ξ.val)⁻¹ • ξ.val + -o.val), add_assoc,
        neg_add_cancel, add_zero]
    exact this
  have hid2 : tc o.val + tc (dirTo o ξ) = (- lorB o.val ξ.val)⁻¹ := by
    rw [← tc_add, hid1, tc_smul, ξ.tc_eq, mul_one]
  have hlimid : (tc o.val + tc (dirTo o ξ))⁻¹ • (o.val + dirTo o ξ) = ξ.val := by
    rw [hid2, hid1, smul_smul, inv_mul_cancel₀ (inv_ne_zero (neg_ne_zero.mpr hL)),
      one_smul]
  have hcoord : ∀ a : Fin n ⊕ Fin 1, Tendsto
      (fun m : ℕ => ((tc (rayTo o ξ (m:ℝ)).val)⁻¹ • (rayTo o ξ (m:ℝ)).val) a)
      atTop (nhds (ξ.val a)) := by
    intro a
    have heq : ∀ m : ℕ, ((tc (rayTo o ξ (m:ℝ)).val)⁻¹ • (rayTo o ξ (m:ℝ)).val) a
        = (tc o.val + (Real.sinh (m:ℝ) / Real.cosh (m:ℝ)) * tc (dirTo o ξ))⁻¹
          * (o.val a + (Real.sinh (m:ℝ) / Real.cosh (m:ℝ)) * dirTo o ξ a) := by
      intro m
      rw [radial_rayTo]
      simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have hlimD : Tendsto
        (fun m : ℕ => tc o.val + (Real.sinh (m:ℝ) / Real.cosh (m:ℝ)) * tc (dirTo o ξ))
        atTop (nhds (tc o.val + 1 * tc (dirTo o ξ))) :=
      tendsto_const_nhds.add (htan.mul tendsto_const_nhds)
    have hlimN : Tendsto
        (fun m : ℕ => o.val a + (Real.sinh (m:ℝ) / Real.cosh (m:ℝ)) * dirTo o ξ a)
        atTop (nhds (o.val a + 1 * dirTo o ξ a)) :=
      tendsto_const_nhds.add (htan.mul tendsto_const_nhds)
    have hlim := (hlimD.inv₀ (by rw [one_mul]; exact hDpos.ne')).mul hlimN
    have hval : (tc o.val + 1 * tc (dirTo o ξ))⁻¹ * (o.val a + 1 * dirTo o ξ a)
        = ξ.val a := by
      have h2 := congrFun hlimid a
      rw [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at h2
      rw [one_mul, one_mul]
      exact h2
    have hlim2 := hlim.congr' (Filter.Eventually.of_forall fun m => (heq m).symm)
    rwa [hval] at hlim2
  unfold ConvergesToBoundary
  exact tendsto_pi_nhds.mpr hcoord

theorem two_le_div_add_div {a b : ℝ} (ha : a < 0) (hb : b < 0) :
    2 ≤ a / b + b / a := by
  have hab : (0:ℝ) < a * b := mul_pos_of_neg_of_neg ha hb
  have h : a / b + b / a - 2 = (a - b) ^ 2 / (a * b) := by
    field_simp [ha.ne, hb.ne]
    ring
  have h2 : 0 ≤ (a - b) ^ 2 / (a * b) := div_nonneg (sq_nonneg _) hab.le
  linarith [h2]

theorem lorB_dirTo_dirTo (o₁ o₂ : HUpper n) (ξ : BoundaryH n) :
    lorB (dirTo o₁ ξ) (dirTo o₂ ξ)
      = lorB o₁.val ξ.val / lorB o₂.val ξ.val + lorB o₂.val ξ.val / lorB o₁.val ξ.val
        + lorB o₁.val o₂.val := by
  have hL1 : lorB o₁.val ξ.val ≠ 0 := (lorB_hUpper_boundary_neg o₁ ξ).ne
  have hL2 : lorB o₂.val ξ.val ≠ 0 := (lorB_hUpper_boundary_neg o₂ ξ).ne
  change lorB ((- lorB o₁.val ξ.val)⁻¹ • (ξ.val + lorB o₁.val ξ.val • o₁.val))
      ((- lorB o₂.val ξ.val)⁻¹ • (ξ.val + lorB o₂.val ξ.val • o₂.val)) = _
  simp only [lorB_smul_left, lorB_smul_right, lorB_add_left, lorB_add_right]
  rw [ξ.is_null, lorB_comm ξ.val o₂.val]
  field_simp [hL1, hL2]
  ring

theorem lorB_left_dirTo (o₁ o₂ : HUpper n) (ξ : BoundaryH n) :
    lorB o₁.val (dirTo o₂ ξ)
      = - lorB o₁.val ξ.val / lorB o₂.val ξ.val - lorB o₁.val o₂.val := by
  have hL2 : lorB o₂.val ξ.val ≠ 0 := (lorB_hUpper_boundary_neg o₂ ξ).ne
  change lorB o₁.val ((- lorB o₂.val ξ.val)⁻¹ • (ξ.val + lorB o₂.val ξ.val • o₂.val)) = _
  rw [lorB_smul_right, lorB_add_right, lorB_smul_right]
  field_simp [hL2]
  ring

theorem lorB_dirTo_right (o₁ o₂ : HUpper n) (ξ : BoundaryH n) :
    lorB (dirTo o₁ ξ) o₂.val
      = - lorB o₂.val ξ.val / lorB o₁.val ξ.val - lorB o₁.val o₂.val := by
  rw [lorB_comm (dirTo o₁ ξ) o₂.val, lorB_left_dirTo o₂ o₁ ξ, lorB_comm o₂.val o₁.val]

theorem cosh_sub_sinh (t : ℝ) : Real.cosh t - Real.sinh t = Real.exp (-t) := by
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

theorem cosh_dist_rayTo_rayTo (o₁ o₂ : HUpper n) (ξ : BoundaryH n) (t : ℝ) :
    Real.cosh (dist (rayTo o₁ ξ t) (rayTo o₂ ξ t))
      = (lorB o₁.val ξ.val / lorB o₂.val ξ.val + lorB o₂.val ξ.val / lorB o₁.val ξ.val) / 2
        - (lorB o₁.val o₂.val
            + (lorB o₁.val ξ.val / lorB o₂.val ξ.val + lorB o₂.val ξ.val / lorB o₁.val ξ.val) / 2)
          * (Real.cosh t - Real.sinh t) ^ 2 := by
  have hlor : lorB (rayTo o₁ ξ t).val (rayTo o₂ ξ t).val
      = lorB o₁.val o₂.val * (Real.cosh t) ^ 2
        - ((lorB o₁.val ξ.val / lorB o₂.val ξ.val + lorB o₂.val ξ.val / lorB o₁.val ξ.val)
            + 2 * lorB o₁.val o₂.val) * (Real.sinh t * Real.cosh t)
        + ((lorB o₁.val ξ.val / lorB o₂.val ξ.val + lorB o₂.val ξ.val / lorB o₁.val ξ.val)
            + lorB o₁.val o₂.val) * (Real.sinh t) ^ 2 := by
    change lorB (Real.cosh t • o₁.val + Real.sinh t • dirTo o₁ ξ)
        (Real.cosh t • o₂.val + Real.sinh t • dirTo o₂ ξ) = _
    simp only [lorB_add_left, lorB_add_right, lorB_smul_left, lorB_smul_right]
    rw [lorB_dirTo_dirTo, lorB_left_dirTo, lorB_dirTo_right]
    ring
  rw [cosh_dist, hlor]
  have h := Real.cosh_sq_sub_sinh_sq t
  linear_combination
    ((lorB o₁.val ξ.val / lorB o₂.val ξ.val + lorB o₂.val ξ.val / lorB o₁.val ξ.val) / 2) * h

theorem dist_rayTo_rayTo_le (o₁ o₂ : HUpper n) (ξ : BoundaryH n) {t : ℝ} (ht : 0 ≤ t) :
    dist (rayTo o₁ ξ t) (rayTo o₂ ξ t)
      ≤ Real.arcosh
        (max (- lorB o₁.val o₂.val)
          ((lorB o₁.val ξ.val / lorB o₂.val ξ.val + lorB o₂.val ξ.val / lorB o₁.val ξ.val) / 2)) := by
  set S := lorB o₁.val ξ.val / lorB o₂.val ξ.val + lorB o₂.val ξ.val / lorB o₁.val ξ.val
    with hS
  set B := lorB o₁.val o₂.val with hB
  have hS2 : 2 ≤ S :=
    two_le_div_add_div (lorB_hUpper_boundary_neg o₁ ξ) (lorB_hUpper_boundary_neg o₂ ξ)
  have hE : (Real.cosh t - Real.sinh t) ^ 2 = Real.exp (-(2 * t)) := by
    rw [cosh_sub_sinh, sq, ← Real.exp_add,
      show (-t + -t : ℝ) = -(2 * t) from by ring]
  have hE0 : (0:ℝ) < Real.exp (-(2 * t)) := Real.exp_pos _
  have hE1 : Real.exp (-(2 * t)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith [ht])
  have hcosh : Real.cosh (dist (rayTo o₁ ξ t) (rayTo o₂ ξ t)) = S / 2 - (B + S / 2) * Real.exp (-(2 * t)) := by
    rw [cosh_dist_rayTo_rayTo, hE]
  have hle : Real.cosh (dist (rayTo o₁ ξ t) (rayTo o₂ ξ t)) ≤ max (-B) (S / 2) := by
    rcases le_or_gt 0 (B + S / 2) with h | h
    · have hnn : 0 ≤ (B + S / 2) * Real.exp (-(2 * t)) := mul_nonneg h hE0.le
      have h1 : Real.cosh (dist (rayTo o₁ ξ t) (rayTo o₂ ξ t)) ≤ S / 2 := by linarith [hcosh, hnn]
      exact h1.trans (le_max_right _ _)
    · have hge : (B + S / 2) * Real.exp (-(2 * t)) ≥ (B + S / 2) * 1 :=
        mul_le_mul_of_nonpos_left hE1 h.le
      have h1 : Real.cosh (dist (rayTo o₁ ξ t) (rayTo o₂ ξ t)) ≤ -B := by linarith [hcosh, hge]
      exact h1.trans (le_max_left _ _)
  have hmax1 : 1 ≤ max (-B) (S / 2) := by
    have h1 : (1:ℝ) ≤ -B := by
      have h2 := cosh_dist o₁ o₂
      have h3 := Real.one_le_cosh (dist o₁ o₂)
      linarith [h2, h3]
    exact h1.trans (le_max_left _ _)
  have hcosh1 : 1 ≤ Real.cosh (dist (rayTo o₁ ξ t) (rayTo o₂ ξ t)) := Real.one_le_cosh _
  calc dist (rayTo o₁ ξ t) (rayTo o₂ ξ t)
      = Real.arcosh (Real.cosh (dist (rayTo o₁ ξ t) (rayTo o₂ ξ t))) :=
        (Real.arcosh_cosh dist_nonneg).symm
    _ ≤ Real.arcosh (max (-B) (S / 2)) :=
        (Real.arcosh_le_arcosh (by linarith [hcosh1]) (by linarith [hmax1])).mpr hle

end DifferentialGeometry.AsymptoticRays

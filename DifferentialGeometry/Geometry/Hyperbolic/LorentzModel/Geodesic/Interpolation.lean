/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Faithfulness

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.HyperbolicConvexity

open DifferentialGeometry.Hyperbolic
open DifferentialGeometry.HyperbolicAction
open DifferentialGeometry.HyperbolicFaithful
open Matrix

variable {n : ℕ}

theorem cosh_dist (a b : HUpper n) :
    Real.cosh (dist a b) = - lorB a.val b.val := by
  change Real.cosh (HUpper.hdist a b) = _
  unfold HUpper.hdist
  rw [Real.cosh_arcosh (HUpper.one_le_neg_lorB a b)]

noncomputable def dirVec (y y' : HUpper n) : LorVec n :=
  (Real.sinh (dist y y'))⁻¹ • (y'.val - Real.cosh (dist y y') • y.val)

theorem lorB_dirVec_left (y y' : HUpper n) : lorB (dirVec y y') y.val = 0 := by
  have hd : Real.cosh (dist y y') = - lorB y.val y'.val := cosh_dist y y'
  change lorB ((Real.sinh (dist y y'))⁻¹ • (y'.val - Real.cosh (dist y y') • y.val)) y.val = 0
  rw [lorB_smul_left, lorB_sub_left, lorB_smul_left, y.is_unit, lorB_comm y'.val y.val, hd]
  ring

theorem lorB_dirVec_self {y y' : HUpper n} (hd : y ≠ y') :
    lorB (dirVec y y') (dirVec y y') = 1 := by
  have hdpos : 0 < dist y y' := dist_pos.mpr hd
  have hsinh : Real.sinh (dist y y') ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hdpos)
  have h2 : Real.cosh (dist y y') ^ 2 - 1 = Real.sinh (dist y y') ^ 2 := by
    linarith [Real.cosh_sq_sub_sinh_sq (dist y y')]
  have hyy : lorB y.val y'.val = - Real.cosh (dist y y') := by
    rw [cosh_dist y y']; ring
  have hnorm : lorB (y'.val - Real.cosh (dist y y') • y.val)
      (y'.val - Real.cosh (dist y y') • y.val) = Real.sinh (dist y y') ^ 2 := by
    simp only [lorB_sub_left, lorB_sub_right, lorB_smul_left, lorB_smul_right]
    rw [y.is_unit, y'.is_unit, lorB_comm y'.val y.val, hyy, ← h2]
    ring
  change lorB ((Real.sinh (dist y y'))⁻¹ • (y'.val - Real.cosh (dist y y') • y.val))
      ((Real.sinh (dist y y'))⁻¹ • (y'.val - Real.cosh (dist y y') • y.val)) = 1
  rw [lorB_smul_left, lorB_smul_right, hnorm]
  have hsq : (Real.sinh (dist y y'))⁻¹ * ((Real.sinh (dist y y'))⁻¹ * Real.sinh (dist y y') ^ 2)
      = ((Real.sinh (dist y y'))⁻¹ * Real.sinh (dist y y')) ^ 2 := by ring
  rw [hsq, inv_mul_cancel₀ hsinh, one_pow]

theorem abs_tc_lt_tc_of_orth_unit (y : HUpper n) {u : LorVec n}
    (hu1 : lorB u u = 1) (hu0 : lorB u y.val = 0) :
    |tc u| < tc y.val := by
  have hsuu : sdot u u = 1 + tc u ^ 2 := by
    have h0 := hu1
    simp only [lorB] at h0
    have h4 : tc u ^ 2 = tc u * tc u := by ring
    linarith
  have hsyy : sdot y.val y.val = tc y.val ^ 2 - 1 := by
    have h1 := HUpper.tc_sq y
    linarith
  have hsuy : sdot u y.val = tc u * tc y.val := by
    have h0 := hu0
    simp only [lorB] at h0
    linarith
  have hcs := sdot_sq_le u y.val
  rw [hsuy, mul_pow, hsuu, hsyy] at hcs
  have hkey : tc u ^ 2 < tc y.val ^ 2 := by nlinarith [hcs, y.future, HUpper.tc_sq y]
  have habs : |tc u| < |tc y.val| := sq_lt_sq.mp hkey
  rwa [abs_of_pos y.future] at habs

theorem abs_tc_dirVec_lt {y y' : HUpper n} (hd : y ≠ y') :
    |tc (dirVec y y')| < tc y.val :=
  abs_tc_lt_tc_of_orth_unit y (lorB_dirVec_self hd) (lorB_dirVec_left y y')

noncomputable def geodFromTo (y y' : HUpper n) (hd : y ≠ y') (t : ℝ) : HUpper n where
  val := Real.cosh t • y.val + Real.sinh t • dirVec y y'
  is_unit := by
    have huu : lorB (dirVec y y') (dirVec y y') = 1 := lorB_dirVec_self hd
    have huy : lorB y.val (dirVec y y') = 0 := by
      rw [lorB_comm]; exact lorB_dirVec_left y y'
    have huy2 : lorB (dirVec y y') y.val = 0 := lorB_dirVec_left y y'
    have hcs : Real.cosh t ^ 2 - Real.sinh t ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq t
    simp only [lorB_add_left, lorB_add_right, lorB_smul_left, lorB_smul_right]
    rw [y.is_unit, huu, huy, huy2]
    nlinarith [hcs]
  future := by
    have hB := abs_tc_dirVec_lt hd
    have hA : 0 < tc y.val := y.future
    have hcosh : 0 < Real.cosh t := zero_lt_one.trans_le (Real.one_le_cosh t)
    have hsinc : |Real.sinh t| < Real.cosh t := by
      have h1 : Real.cosh t ^ 2 - Real.sinh t ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq t
      have h2 : Real.sinh t ^ 2 < Real.cosh t ^ 2 := by nlinarith [h1]
      have h3 := sq_lt_sq.mp h2
      rwa [abs_of_pos hcosh] at h3
    have hstep1 : - (|Real.sinh t| * |tc (dirVec y y')|)
        ≤ Real.sinh t * tc (dirVec y y') := by
      rw [← abs_mul]
      exact neg_abs_le _
    have hstep2 : |Real.sinh t| * |tc (dirVec y y')| < Real.cosh t * tc y.val := by
      rcases eq_or_lt_of_le (abs_nonneg (Real.sinh t)) with hs0 | hspos
      · rw [hs0.symm, zero_mul]
        exact mul_pos hcosh hA
      · rcases eq_or_lt_of_le (abs_nonneg (tc (dirVec y y'))) with hu0 | hupos
        · rw [hu0.symm, mul_zero]
          exact mul_pos hcosh hA
        · exact mul_lt_mul hsinc hB.le hupos hcosh.le
    rw [tc_add, tc_smul, tc_smul]
    linarith [hstep1, hstep2, hA, hcosh]

theorem geodFromTo_zero {y y' : HUpper n} (hd : y ≠ y') : geodFromTo y y' hd 0 = y := by
  apply HUpper.ext
  change Real.cosh 0 • y.val + Real.sinh 0 • dirVec y y' = y.val
  rw [Real.cosh_zero, Real.sinh_zero, zero_smul, add_zero, one_smul]

theorem geodFromTo_dist {y y' : HUpper n} (hd : y ≠ y') :
    geodFromTo y y' hd (dist y y') = y' := by
  have hdpos : 0 < dist y y' := dist_pos.mpr hd
  have hsinh : Real.sinh (dist y y') ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hdpos)
  apply HUpper.ext
  change Real.cosh (dist y y') • y.val
      + Real.sinh (dist y y') • ((Real.sinh (dist y y'))⁻¹
        • (y'.val - Real.cosh (dist y y') • y.val)) = y'.val
  rw [smul_smul, mul_inv_cancel₀ hsinh, one_smul]
  abel

theorem lorB_geodFromTo_geodFromTo {y y' : HUpper n} (hd : y ≠ y') (t s : ℝ) :
    lorB (geodFromTo y y' hd t).val (geodFromTo y y' hd s).val
      = - Real.cosh (t - s) := by
  have huu : lorB (dirVec y y') (dirVec y y') = 1 := lorB_dirVec_self hd
  have huy : lorB (dirVec y y') y.val = 0 := lorB_dirVec_left y y'
  have huy' : lorB y.val (dirVec y y') = 0 := by rw [lorB_comm]; exact huy
  change lorB (Real.cosh t • y.val + Real.sinh t • dirVec y y')
      (Real.cosh s • y.val + Real.sinh s • dirVec y y') = _
  simp only [lorB_add_left, lorB_add_right, lorB_smul_left, lorB_smul_right]
  rw [y.is_unit, huu, huy, huy', Real.cosh_sub]
  ring

theorem dist_geodFromTo {y y' : HUpper n} (hd : y ≠ y') (t s : ℝ) :
    dist (geodFromTo y y' hd t) (geodFromTo y y' hd s) = |t - s| := by
  change HUpper.hdist _ _ = |t - s|
  unfold HUpper.hdist
  rw [lorB_geodFromTo_geodFromTo hd, neg_neg]
  rcases le_or_gt 0 (t - s) with hts | hts
  · rw [abs_of_nonneg hts]
    exact Real.arcosh_cosh hts
  · have h2 : (0 : ℝ) ≤ s - t := by linarith
    rw [abs_of_neg hts, ← Real.cosh_neg (t - s), neg_sub]
    exact Real.arcosh_cosh h2

theorem isometry_geodFromTo {y y' : HUpper n} (hd : y ≠ y') :
    Isometry (geodFromTo y y' hd) := by
  intro t s
  rw [edist_dist, edist_dist, dist_geodFromTo hd, Real.dist_eq]

theorem lipschitzWith_geodFromTo {y y' : HUpper n} (hd : y ≠ y') :
    LipschitzWith 1 (geodFromTo y y' hd) := by
  intro t s
  rw [edist_dist, edist_dist, dist_geodFromTo hd, Real.dist_eq, ENNReal.coe_one, one_mul]

theorem continuous_geodFromTo {y y' : HUpper n} (hd : y ≠ y') :
    Continuous (geodFromTo y y' hd) :=
  (lipschitzWith_geodFromTo hd).continuous

theorem cosh_dist_geodFromTo {y y' : HUpper n} (hd : y ≠ y') (p : HUpper n) (t : ℝ) :
    Real.cosh (dist p (geodFromTo y y' hd t))
      = Real.cosh t * Real.cosh (dist p y)
        + Real.sinh t * ((Real.cosh (dist p y')
          - Real.cosh (dist y y') * Real.cosh (dist p y)) / Real.sinh (dist y y')) := by
  have hdpos : 0 < dist y y' := dist_pos.mpr hd
  have hsinh : Real.sinh (dist y y') ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hdpos)
  have hpu : lorB p.val (dirVec y y')
      = (Real.cosh (dist y y') * (- lorB p.val y.val) - (- lorB p.val y'.val))
        / Real.sinh (dist y y') := by
    change lorB p.val ((Real.sinh (dist y y'))⁻¹
        • (y'.val - Real.cosh (dist y y') • y.val)) = _
    rw [lorB_smul_right, lorB_sub_right, lorB_smul_right]
    rw [eq_div_iff hsinh, mul_comm, ← mul_assoc, mul_inv_cancel₀ hsinh, one_mul]
    rw [cosh_dist y y']
    ring
  rw [cosh_dist p (geodFromTo y y' hd t)]
  change - lorB p.val (Real.cosh t • y.val + Real.sinh t • dirVec y y') = _
  rw [lorB_add_right, lorB_smul_right, lorB_smul_right, hpu, cosh_dist p y, cosh_dist p y']
  ring

end DifferentialGeometry.HyperbolicConvexity

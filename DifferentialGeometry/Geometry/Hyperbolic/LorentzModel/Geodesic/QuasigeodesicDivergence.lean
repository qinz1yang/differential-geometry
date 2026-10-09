/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.MorseStability
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.ProjectionContraction
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Transitivity
import Mathlib.Analysis.Complex.ExponentialBounds

open DifferentialGeometry.ProjectiveOrthogonalGroup Filter

namespace DifferentialGeometry.MorseDivergence

open DifferentialGeometry.Hyperbolic DifferentialGeometry.HyperbolicFaithful DifferentialGeometry.HyperbolicBoundary
open DifferentialGeometry.BoundaryTopology DifferentialGeometry.HyperbolicConvexity DifferentialGeometry.GromovBoundary
open DifferentialGeometry.AsymptoticRays DifferentialGeometry.GeodesicProjection DifferentialGeometry.BoundaryExtension
open DifferentialGeometry.MorseStability DifferentialGeometry.HyperbolicAction DifferentialGeometry.HyperbolicTransitive
open DifferentialGeometry.ProjectionContraction

variable {n : ℕ}

noncomputable def eNorm (v : LorVec n) : ℝ := Real.sqrt (sdot v v)

theorem eNorm_nonneg (v : LorVec n) : 0 ≤ eNorm v := Real.sqrt_nonneg _

theorem eNorm_sq (v : LorVec n) : eNorm v ^ 2 = sdot v v :=
  Real.sq_sqrt (sdot_self_nonneg v)

theorem eNorm_zero : eNorm (0 : LorVec n) = 0 := by
  have h : sdot (0 : LorVec n) 0 = 0 := by
    change (∑ i : Fin n, (0 : LorVec n) (Sum.inl i) * (0 : LorVec n) (Sum.inl i)) = 0
    simp
  change Real.sqrt (sdot (0 : LorVec n) 0) = 0
  rw [h]
  exact Real.sqrt_zero

theorem sdot_le_eNorm_mul_eNorm (u v : LorVec n) : sdot u v ≤ eNorm u * eNorm v := by
  have hcs : (∑ i : Fin n, u (Sum.inl i) * v (Sum.inl i)) ^ 2
      ≤ (∑ i : Fin n, (u (Sum.inl i)) ^ 2) * (∑ i : Fin n, (v (Sum.inl i)) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hu : sdot u u = ∑ i : Fin n, (u (Sum.inl i)) ^ 2 := by
    change (∑ i, u (Sum.inl i) * u (Sum.inl i)) = _
    exact Finset.sum_congr rfl fun i _ => (pow_two _).symm
  have hv : sdot v v = ∑ i : Fin n, (v (Sum.inl i)) ^ 2 := by
    change (∑ i, v (Sum.inl i) * v (Sum.inl i)) = _
    exact Finset.sum_congr rfl fun i _ => (pow_two _).symm
  have hstep : (sdot u v) ^ 2 ≤ sdot u u * sdot v v := by
    have huv : sdot u v = ∑ i : Fin n, u (Sum.inl i) * v (Sum.inl i) := rfl
    rw [huv, hu, hv]
    exact hcs
  have h1 : sdot u v ≤ Real.sqrt (sdot u u * sdot v v) := by
    calc sdot u v ≤ |sdot u v| := le_abs_self _
      _ = Real.sqrt ((sdot u v) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (sdot u u * sdot v v) := Real.sqrt_le_sqrt hstep
  have h2 : Real.sqrt (sdot u u * sdot v v) = eNorm u * eNorm v :=
    Real.sqrt_mul (sdot_self_nonneg u) _
  rw [h2] at h1
  exact h1

theorem eNorm_add_le (u v : LorVec n) : eNorm (u + v) ≤ eNorm u + eNorm v := by
  have h3 : sdot u (u + v) = sdot u u + sdot u v := by
    rw [sdot_comm u (u + v), sdot_add_left, sdot_comm v u]
  have h4 : sdot v (u + v) = sdot u v + sdot v v := by
    rw [sdot_comm v (u + v), sdot_add_left]
  have h1 : sdot (u + v) (u + v) = sdot u u + 2 * sdot u v + sdot v v := by
    rw [sdot_add_left, h3, h4]
    ring
  have h2 : sdot (u + v) (u + v) ≤ (eNorm u + eNorm v) ^ 2 := by
    rw [h1]
    have hcs := sdot_le_eNorm_mul_eNorm u v
    have h3 : (eNorm u + eNorm v) ^ 2
        = eNorm u ^ 2 + 2 * (eNorm u * eNorm v) + eNorm v ^ 2 := by ring
    rw [h3, eNorm_sq u, eNorm_sq v]
    linarith [hcs]
  calc eNorm (u + v) = Real.sqrt (sdot (u + v) (u + v)) := rfl
    _ ≤ Real.sqrt ((eNorm u + eNorm v) ^ 2) := Real.sqrt_le_sqrt h2
    _ = eNorm u + eNorm v := Real.sqrt_sq (add_nonneg (eNorm_nonneg u) (eNorm_nonneg v))

theorem eNorm_sub_le (u v w : LorVec n) : eNorm (u - w) ≤ eNorm (u - v) + eNorm (v - w) := by
  have h : u - w = (u - v) + (v - w) := by abel
  rw [h]
  exact eNorm_add_le _ _

theorem eNorm_radial_sub_le_sum (H : ℕ) (p : ℕ → HUpper n) :
    eNorm (radial (p 0) - radial (p H))
      ≤ ∑ j ∈ Finset.range H, eNorm (radial (p j) - radial (p (j + 1))) := by
  induction H with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    rw [sub_self, eNorm_zero]
  | succ H ih =>
    have hsplit : radial (p 0) - radial (p (H + 1))
        = (radial (p 0) - radial (p H)) + (radial (p H) - radial (p (H + 1))) := by abel
    rw [hsplit]
    calc eNorm ((radial (p 0) - radial (p H)) + (radial (p H) - radial (p (H + 1))))
        ≤ eNorm (radial (p 0) - radial (p H)) + eNorm (radial (p H) - radial (p (H + 1))) :=
          eNorm_add_le _ _
      _ ≤ (∑ j ∈ Finset.range H, eNorm (radial (p j) - radial (p (j + 1))))
            + eNorm (radial (p H) - radial (p (H + 1))) :=
          add_le_add ih (le_refl _)
      _ = ∑ j ∈ Finset.range (H + 1), eNorm (radial (p j) - radial (p (j + 1))) :=
          (Finset.sum_range_succ _ _).symm

theorem eNorm_radial_sub_le (x y : HUpper n) {R : ℝ}
    (hx : R ≤ dist basepointH x) (hy : R ≤ dist basepointH y)
    (hp : R ≤ gromovProduct basepointH x y) :
    eNorm (radial x - radial y) ≤ 4 * Real.exp (-R) := by
  have h := sdot_radial_sub_radial_le hx hy hp
  have h1 : (4 * Real.exp (-R)) ^ 2 = 16 * Real.exp (-(2 * R)) := by
    rw [show (-(2 * R) : ℝ) = -R + -R from by ring, Real.exp_add]
    ring
  have h2 : Real.sqrt (16 * Real.exp (-(2 * R))) = 4 * Real.exp (-R) := by
    rw [← h1]
    exact Real.sqrt_sq (by positivity)
  calc eNorm (radial x - radial y) = Real.sqrt (sdot (radial x - radial y) (radial x - radial y)) :=
        rfl
    _ ≤ Real.sqrt (16 * Real.exp (-(2 * R))) := Real.sqrt_le_sqrt h
    _ = 4 * Real.exp (-R) := h2

theorem gromovProduct_po_smul (hn : 1 ≤ n) (g : PO n 1) (o x y : HUpper n) :
    letI := poMulAction hn
    gromovProduct (g • o) (g • x) (g • y) = gromovProduct o x y := by
  let := poMulAction hn
  unfold gromovProduct
  rw [po_dist_smul hn g o x, po_dist_smul hn g o y, po_dist_smul hn g x y]

theorem onSegment_po_smul (hn : 1 ≤ n) (g : PO n 1) (x y w : HUpper n)
    (h : OnSegment x y w) :
    letI := poMulAction hn
    OnSegment (g • x) (g • y) (g • w) := by
  let := poMulAction hn
  change dist (g • x) (g • w) + dist (g • w) (g • y) = dist (g • x) (g • y)
  rw [po_dist_smul hn g x w, po_dist_smul hn g w y, po_dist_smul hn g x y]
  exact h

theorem lorB_basepoint (v : LorVec n) : lorB v (basepointH (n := n)).val = - tc v := by
  have hb : (basepointH.val : LorVec n) = eTime := rfl
  change sdot v basepointH.val - tc v * tc basepointH.val = - tc v
  rw [hb, tc_eTime]
  have hs : sdot v (eTime : LorVec n) = 0 := by
    change (∑ i : Fin n, v (Sum.inl i) * (eTime : LorVec n) (Sum.inl i)) = 0
    exact Finset.sum_eq_zero fun i _ => by rw [eTime_apply_inl, mul_zero]
  rw [hs]
  ring

theorem eq_zero_of_lorB_self_zero_of_lorB_basepoint {v : LorVec n}
    (hvv : lorB v v = 0) (hv0 : lorB v (basepointH (n := n)).val = 0) : v = 0 := by
  have htc : tc v = 0 := by
    have h := lorB_basepoint v
    rw [h] at hv0
    linarith [hv0]
  have hsd : sdot v v = 0 := by
    have h : lorB v v = sdot v v - tc v * tc v := rfl
    rw [hvv, htc] at h
    have h2 : (0:ℝ) = sdot v v - 0 * 0 := h
    linarith [h2]
  funext a
  rcases a with i | k
  · have hsum : sdot v v = ∑ j : Fin n, (v (Sum.inl j)) ^ 2 := by
      change (∑ j, v (Sum.inl j) * v (Sum.inl j)) = _
      exact Finset.sum_congr rfl fun j _ => (pow_two _).symm
    have hle : (v (Sum.inl i)) ^ 2 ≤ ∑ j : Fin n, (v (Sum.inl j)) ^ 2 :=
      Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin n => (v (Sum.inl j)) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [← hsum, hsd] at hle
    have h0 : (v (Sum.inl i)) ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
    have h2 : v (Sum.inl i) * v (Sum.inl i) = 0 := by
      have h3 : (v (Sum.inl i)) ^ 2 = v (Sum.inl i) * v (Sum.inl i) := pow_two _
      rw [h3] at h0
      exact h0
    exact mul_self_eq_zero.mp h2
  · have hk : k = 0 := Subsingleton.elim k 0
    subst hk
    change v (Sum.inr 0) = 0
    exact htc

theorem val_eq_cosh_smul_add_sinh_smul (y : HUpper n) (hy : basepointH ≠ y) :
    (y : HUpper n).val = Real.cosh (dist basepointH y) • (basepointH (n := n)).val
      + Real.sinh (dist basepointH y) • dirVec basepointH y := by
  have h1 : geodFromTo basepointH y hy (dist basepointH y) = y := geodFromTo_dist hy
  have h2 := congrArg HUpper.val h1
  change y.val = _
  rw [← h2]
  rfl

theorem dirVec_neg_of_onSegment_basepoint {y z : HUpper n}
    (h : OnSegment y z basepointH) (hy : basepointH ≠ y) (hz : basepointH ≠ z) :
    dirVec basepointH z = - dirVec basepointH y := by
  set a := dist basepointH y with ha
  set b := dist basepointH z with hb
  have ha0 : 0 < a := dist_pos.mpr hy
  have hb0 : 0 < b := dist_pos.mpr hz
  have hyval := val_eq_cosh_smul_add_sinh_smul y hy
  have hzval := val_eq_cosh_smul_add_sinh_smul z hz
  have hUy : lorB (dirVec basepointH y) (basepointH (n := n)).val = 0 :=
    lorB_dirVec_left basepointH y
  have hVz : lorB (dirVec basepointH z) (basepointH (n := n)).val = 0 :=
    lorB_dirVec_left basepointH z
  have hUU : lorB (dirVec basepointH y) (dirVec basepointH y) = 1 := lorB_dirVec_self hy
  have hVV : lorB (dirVec basepointH z) (dirVec basepointH z) = 1 := lorB_dirVec_self hz
  have he0 : lorB (basepointH (n := n)).val (basepointH (n := n)).val = -1 := basepointH.is_unit
  have hye : lorB basepointH.val (dirVec basepointH y) = 0 := by
    rw [lorB_comm]; exact hUy
  have hze : lorB basepointH.val (dirVec basepointH z) = 0 := by
    rw [lorB_comm]; exact hVz
  have hyz : lorB y.val z.val = - Real.cosh (a + b) := by
    have hdist : dist y z = a + b := by
      have h2 : dist y basepointH + dist basepointH z = dist y z := h
      rw [dist_comm y basepointH] at h2
      rw [← h2]
    have h3 := cosh_dist y z
    rw [hdist] at h3
    linarith [h3]
  have hexp : lorB y.val z.val
      = - (Real.cosh a * Real.cosh b)
        + Real.sinh a * Real.sinh b * lorB (dirVec basepointH y) (dirVec basepointH z) := by
    rw [hyval, hzval]
    simp only [lorB_add_left, lorB_add_right, lorB_smul_left, lorB_smul_right]
    rw [he0, hUy, hze]
    ring
  rw [Real.cosh_add] at hyz
  rw [hexp] at hyz
  have hsina : Real.sinh a ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr ha0)
  have hsinb : Real.sinh b ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hb0)
  have hss : Real.sinh a * Real.sinh b ≠ 0 := mul_ne_zero hsina hsinb
  have hUV : lorB (dirVec basepointH y) (dirVec basepointH z) = -1 := by
    have hcan : Real.sinh a * Real.sinh b * lorB (dirVec basepointH y) (dirVec basepointH z)
        = Real.sinh a * Real.sinh b * (-1) := by linarith [hyz]
    have h := mul_left_cancel₀ hss hcan
    linarith [h]
  have hVU : lorB (dirVec basepointH z) (dirVec basepointH y) = -1 := by
    rw [lorB_comm]; exact hUV
  have hsum0 : dirVec basepointH y + dirVec basepointH z = 0 := by
    apply eq_zero_of_lorB_self_zero_of_lorB_basepoint
    · have h1 : lorB (dirVec basepointH y + dirVec basepointH z)
          (dirVec basepointH y + dirVec basepointH z)
          = lorB (dirVec basepointH y) (dirVec basepointH y)
            + lorB (dirVec basepointH y) (dirVec basepointH z)
            + lorB (dirVec basepointH z) (dirVec basepointH y)
            + lorB (dirVec basepointH z) (dirVec basepointH z) := by
        simp only [lorB_add_left, lorB_add_right]; ring
      rw [h1, hUU, hUV, hVU, hVV]
      norm_num
    · have h2 : lorB (dirVec basepointH y + dirVec basepointH z) basepointH.val
          = lorB (dirVec basepointH y) basepointH.val
            + lorB (dirVec basepointH z) basepointH.val := lorB_add_left _ _ _
      rw [h2, hUy, hVz]
      norm_num
  exact eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans hsum0)

theorem radial_eq_basepoint_add (y : HUpper n) (hy : basepointH ≠ y) :
    radial y = (basepointH (n := n)).val
      + (Real.sinh (dist basepointH y) / Real.cosh (dist basepointH y)) • dirVec basepointH y := by
  have hyval := val_eq_cosh_smul_add_sinh_smul y hy
  have htc : tc y.val = Real.cosh (dist basepointH y) := by
    have h := cosh_dist_basepoint y
    linarith [h]
  have hc0 : Real.cosh (dist basepointH y) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  change (tc y.val)⁻¹ • y.val = _
  rw [htc, hyval, smul_add, smul_smul, smul_smul]
  have h1 : (Real.cosh (dist basepointH y))⁻¹ * Real.cosh (dist basepointH y) = 1 :=
    inv_mul_cancel₀ hc0
  have h2 : (Real.cosh (dist basepointH y))⁻¹ * Real.sinh (dist basepointH y)
      = Real.sinh (dist basepointH y) / Real.cosh (dist basepointH y) := by
    rw [div_eq_mul_inv, mul_comm]
  rw [h1, h2, one_smul]

theorem three_quarters_le_sinh_div_cosh {v : ℝ} (hv : 1 ≤ v) :
    3 / 4 ≤ Real.sinh v / Real.cosh v := by
  have hs : Real.sinh v = (Real.exp v - Real.exp (-v)) / 2 := Real.sinh_eq v
  have hc : Real.cosh v = (Real.exp v + Real.exp (-v)) / 2 := Real.cosh_eq v
  rw [hs, hc, div_div_div_cancel_right₀ (by norm_num : (2:ℝ) ≠ 0)]
  have he2 : Real.exp (2 * v) ≥ 7 := by
    have h1 : Real.exp (2 * v) ≥ Real.exp 2 :=
      Real.exp_le_exp.mpr (by linarith [hv])
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [show (2:ℝ) = 1 + 1 from by norm_num, Real.exp_add]
      ring
    have h3 : Real.exp 1 ≥ 2.7182818283 := le_of_lt Real.exp_one_gt_d9
    have h4 : Real.exp 1 ^ 2 ≥ 2.7182818283 ^ 2 :=
      pow_le_pow_left₀ (by norm_num) h3 2
    have h5 : (2.7182818283 : ℝ) ^ 2 ≥ 7 := by norm_num
    linarith [h1, h2, h4, h5]
  have hev : Real.exp v * Real.exp (-v) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hev0 : (0:ℝ) < Real.exp v := Real.exp_pos v
  have henv0 : (0:ℝ) < Real.exp (-v) := Real.exp_pos _
  have hscale : (Real.exp v - Real.exp (-v)) / (Real.exp v + Real.exp (-v))
      = (Real.exp (2 * v) - 1) / (Real.exp (2 * v) + 1) := by
    have hm : Real.exp (2 * v) = Real.exp v * Real.exp v := by
      rw [show (2:ℝ) * v = v + v from by ring, Real.exp_add]
    rw [hm]
    rw [div_eq_div_iff (ne_of_gt (by positivity : (0:ℝ) < Real.exp v + Real.exp (-v)))
      (ne_of_gt (by positivity : (0:ℝ) < Real.exp v * Real.exp v + 1))]
    field_simp
    nlinarith [hev, hev0, henv0]
  rw [hscale]
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 4)
    (by positivity : (0:ℝ) < Real.exp (2 * v) + 1)]
  nlinarith [he2]

theorem three_halves_le_eNorm_radial_sub_of_onSegment {y z : HUpper n}
    (h : OnSegment y z basepointH) (hy : 1 ≤ dist basepointH y)
    (hz : 1 ≤ dist basepointH z) :
    3 / 2 ≤ eNorm (radial y - radial z) := by
  have hyne : basepointH ≠ y := by
    intro hbad
    rw [← hbad] at hy
    rw [dist_self] at hy
    linarith [hy]
  have hzne : basepointH ≠ z := by
    intro hbad
    rw [← hbad] at hz
    rw [dist_self] at hz
    linarith [hz]
  set a := dist basepointH y with ha
  set b := dist basepointH z with hb
  have hdir : dirVec basepointH z = - dirVec basepointH y :=
    dirVec_neg_of_onSegment_basepoint h hyne hzne
  have hry := radial_eq_basepoint_add y hyne
  have hrz := radial_eq_basepoint_add z hzne
  have hUU : sdot (dirVec basepointH y) (dirVec basepointH y) = 1 := by
    have h1 : lorB (dirVec basepointH y) (dirVec basepointH y) = 1 := lorB_dirVec_self hyne
    have h2 : lorB (dirVec basepointH y) basepointH.val = 0 := lorB_dirVec_left basepointH y
    have h3 : tc (dirVec basepointH y) = 0 := by
      have h4 := lorB_basepoint (dirVec basepointH y)
      rw [h2] at h4
      linarith [h4]
    have h5 : lorB (dirVec basepointH y) (dirVec basepointH y)
        = sdot (dirVec basepointH y) (dirVec basepointH y)
          - tc (dirVec basepointH y) * tc (dirVec basepointH y) := rfl
    rw [h3] at h5
    linarith [h1, h5]
  have hdiff : radial y - radial z
      = (Real.sinh a / Real.cosh a + Real.sinh b / Real.cosh b) • dirVec basepointH y := by
    rw [hry, hrz, hdir, smul_neg, ← sub_eq_add_neg]
    have e1 : (basepointH.val + (Real.sinh a / Real.cosh a) • dirVec basepointH y)
        - (basepointH.val - (Real.sinh b / Real.cosh b) • dirVec basepointH y)
        = (Real.sinh a / Real.cosh a) • dirVec basepointH y
          + (Real.sinh b / Real.cosh b) • dirVec basepointH y := by abel
    rw [e1, ← add_smul]
  have hsd : sdot (radial y - radial z) (radial y - radial z)
      = (Real.sinh a / Real.cosh a + Real.sinh b / Real.cosh b) ^ 2 := by
    rw [hdiff, sdot_smul_left, sdot_smul_right, hUU]
    ring
  have hta : 3 / 4 ≤ Real.sinh a / Real.cosh a := three_quarters_le_sinh_div_cosh hy
  have htb : 3 / 4 ≤ Real.sinh b / Real.cosh b := three_quarters_le_sinh_div_cosh hz
  have h9 : (9:ℝ) / 4 ≤ sdot (radial y - radial z) (radial y - radial z) := by
    rw [hsd]
    have h1 : (3:ℝ) / 2 ≤ Real.sinh a / Real.cosh a + Real.sinh b / Real.cosh b := by
      linarith [hta, htb]
    have h2 : ((3:ℝ) / 2) ^ 2 ≤ (Real.sinh a / Real.cosh a + Real.sinh b / Real.cosh b) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) h1 2
    have h3 : ((3:ℝ) / 2) ^ 2 = 9 / 4 := by norm_num
    linarith [h2, h3]
  have h4 : (3:ℝ) / 2 = Real.sqrt (9 / 4) := by
    have h5 : ((3:ℝ) / 2) ^ 2 = 9 / 4 := by norm_num
    rw [← h5]
    exact (Real.sqrt_sq (by norm_num)).symm
  rw [h4]
  change Real.sqrt (9 / 4) ≤ Real.sqrt (sdot (radial y - radial z) (radial y - radial z))
  exact Real.sqrt_le_sqrt h9

theorem eq_geodFromTo_of_onSegment {x y w : HUpper n} (hd : x ≠ y)
    (h : OnSegment x y w) : w = geodFromTo x y hd (dist x w) := by
  obtain ⟨R, t₀, hR1, hform⟩ := cosh_dist_geod_eq w x y hd
  have hab : dist x w + dist w y = dist x y := h
  have hend1 : Real.cosh (dist x w) = R * Real.cosh t₀ := by
    have h1 := hform 0
    rw [geodFromTo_zero hd, dist_comm w x, zero_sub, Real.cosh_neg] at h1
    exact h1
  have hend2 : Real.cosh (dist w y) = R * Real.cosh (dist x y - t₀) := by
    have h2 := hform (dist x y)
    rw [geodFromTo_dist hd] at h2
    exact h2
  have hge1 : |t₀| ≤ dist x w := by
    have h1 : Real.cosh |t₀| ≤ Real.cosh (dist x w) := by
      rw [Real.cosh_abs, hend1]
      calc Real.cosh t₀ = 1 * Real.cosh t₀ := by ring
        _ ≤ R * Real.cosh t₀ :=
          mul_le_mul_of_nonneg_right hR1 (Real.cosh_pos _).le
    have h3 := Real.cosh_le_cosh.mp h1
    rwa [abs_abs, abs_of_nonneg dist_nonneg] at h3
  have hge2 : |dist x y - t₀| ≤ dist w y := by
    have h1 : Real.cosh |dist x y - t₀| ≤ Real.cosh (dist w y) := by
      rw [Real.cosh_abs, hend2]
      calc Real.cosh (dist x y - t₀) = 1 * Real.cosh (dist x y - t₀) := by ring
        _ ≤ R * Real.cosh (dist x y - t₀) :=
          mul_le_mul_of_nonneg_right hR1 (Real.cosh_pos _).le
    have h3 := Real.cosh_le_cosh.mp h1
    rwa [abs_abs, abs_of_nonneg dist_nonneg] at h3
  have hsum : dist x y ≤ |t₀| + |dist x y - t₀| := by
    have h1 : |t₀ + (dist x y - t₀)| ≤ |t₀| + |dist x y - t₀| := abs_add_le _ _
    rw [add_sub_cancel] at h1
    rwa [abs_of_nonneg dist_nonneg] at h1
  have ht₀0 : 0 ≤ t₀ := by
    by_contra hc
    push Not at hc
    have h1 : |t₀| = -t₀ := abs_of_neg hc
    have h2 : |dist x y - t₀| = dist x y - t₀ :=
      abs_of_nonneg (by linarith [hc, dist_nonneg (x := x) (y := y)])
    nlinarith [hab, hge1, hge2, hsum, h1, h2, dist_nonneg (x := x) (y := w),
      dist_nonneg (x := w) (y := y)]
  have ht₀T : t₀ ≤ dist x y := by
    by_contra hc
    push Not at hc
    have h1 : |t₀| = t₀ := abs_of_pos (by linarith [hc, dist_nonneg (x := x) (y := y)])
    have h2 : |dist x y - t₀| = -(dist x y - t₀) := abs_of_neg (by linarith [hc])
    nlinarith [hab, hge1, hge2, hsum, h1, h2, dist_nonneg (x := x) (y := w),
      dist_nonneg (x := w) (y := y)]
  have hta : t₀ = dist x w := by
    have h1 : |t₀| = t₀ := abs_of_nonneg ht₀0
    have h2 : |dist x y - t₀| = dist x y - t₀ := abs_of_nonneg (by linarith [ht₀T])
    have h3 : dist x w = t₀ := by
      linarith [hab, hge1, hge2, h1, h2]
    rw [h3]
  have hR : R = 1 := by
    rw [hta] at hend1
    have h1 : Real.cosh (dist x w) = R * Real.cosh (dist x w) := hend1
    have h2 : R * Real.cosh (dist x w) = 1 * Real.cosh (dist x w) := by
      rw [← h1, one_mul]
    exact mul_right_cancel₀ (ne_of_gt (Real.cosh_pos _)) h2
  have hwt : w = geodFromTo x y hd t₀ := by
    have h1 := hform t₀
    rw [sub_self, Real.cosh_zero, mul_one, hR] at h1
    have hpos : 0 ≤ dist w (geodFromTo x y hd t₀) := dist_nonneg
    have h2 : dist w (geodFromTo x y hd t₀) = 0 := by
      calc dist w (geodFromTo x y hd t₀)
          = Real.arcosh (Real.cosh (dist w (geodFromTo x y hd t₀))) :=
            (Real.arcosh_cosh hpos).symm
        _ = Real.arcosh 1 := by rw [h1]
        _ = 0 := by simp [Real.arcosh]
    exact dist_eq_zero.mp (dist_comm w _ ▸ h2)
  exact hwt.trans (congrArg (geodFromTo x y hd) hta)

theorem onSegment_symm {x y w : HUpper n} (h : OnSegment x y w) : OnSegment y x w := by
  change dist y w + dist w x = dist y x
  rw [dist_comm y x, dist_comm y w, dist_comm w x, add_comm (dist w y) (dist x w)]
  exact h

noncomputable def paramNet (A B : ℝ) : Finset ℝ :=
  (Finset.Icc (Int.ceil A) (Int.floor B)).image (fun m : ℤ => (m : ℝ)) ∪ {A, B}

theorem left_mem_paramNet {A B : ℝ} : A ∈ paramNet A B := by
  change A ∈ _ ∪ {A, B}
  exact Finset.mem_union_right _ (Finset.mem_insert_self A {B})

theorem right_mem_paramNet {A B : ℝ} : B ∈ paramNet A B := by
  change B ∈ _ ∪ {A, B}
  exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self B))

theorem intCast_mem_paramNet {A B : ℝ} {m : ℤ}
    (hm : m ∈ Finset.Icc (Int.ceil A) (Int.floor B)) :
    (m : ℝ) ∈ paramNet A B :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)

theorem mem_paramNet_bound {A B : ℝ} (hAB : A ≤ B) {p : ℝ} (hp : p ∈ paramNet A B) :
    A ≤ p ∧ p ≤ B := by
  rcases Finset.mem_union.mp hp with h | h
  · rcases Finset.mem_image.mp h with ⟨m, hm, rfl⟩
    rw [Finset.mem_Icc] at hm
    constructor
    · have h1 : (A : ℝ) ≤ (Int.ceil A : ℝ) := Int.le_ceil A
      have h2 : ((Int.ceil A : ℤ) : ℝ) ≤ (m : ℝ) := Int.cast_le.mpr hm.1
      linarith [h1, h2]
    · have h1 : (m : ℝ) ≤ (Int.floor B : ℝ) := Int.cast_le.mpr hm.2
      have h2 : ((Int.floor B : ℤ) : ℝ) ≤ B := Int.floor_le B
      linarith [h1, h2]
  · rcases Finset.mem_insert.mp h with hpA | h
    · rw [hpA]
      exact ⟨le_refl A, hAB⟩
    · have hpB : p = B := Finset.mem_singleton.mp h
      rw [hpB]
      exact ⟨hAB, le_refl B⟩

theorem ceil_le_add_one (A : ℝ) : (Int.ceil A : ℝ) ≤ A + 1 := by
  have h6 : Int.ceil A ≤ Int.floor A + 1 := by
    rw [Int.ceil_le]
    have h7 := Int.lt_floor_add_one A
    have h8 : ((Int.floor A + 1 : ℤ) : ℝ) = (Int.floor A : ℝ) + 1 := by norm_cast
    rw [h8]
    linarith [h7]
  have h9 : (Int.ceil A : ℝ) ≤ ((Int.floor A + 1 : ℤ) : ℝ) := Int.cast_le.mpr h6
  rw [Int.cast_add, Int.cast_one] at h9
  have h10 : (Int.floor A : ℝ) ≤ A := Int.floor_le A
  linarith [h9, h10]

theorem exists_net_approx {A B : ℝ} {r : ℝ} (hrA : A ≤ r) (hrB : r ≤ B) :
    ∃ p ∈ paramNet A B, |r - p| ≤ 1 := by
  by_cases hm : Int.ceil A ≤ Int.floor r
  · refine ⟨(Int.floor r : ℝ), intCast_mem_paramNet ?_, ?_⟩
    · rw [Finset.mem_Icc]
      refine ⟨hm, ?_⟩
      rw [Int.le_floor]
      exact (Int.floor_le r).trans hrB
    · have h1 : (Int.floor r : ℝ) ≤ r := Int.floor_le r
      have h2 : r < (Int.floor r : ℝ) + 1 := Int.lt_floor_add_one r
      rw [abs_of_nonneg (by linarith [h1])]
      linarith [h1, h2]
  · push Not at hm
    refine ⟨A, left_mem_paramNet, ?_⟩
    have hfr : (Int.floor r : ℝ) ≤ (Int.ceil A : ℝ) - 1 := by
      have h2 : Int.floor r ≤ Int.ceil A - 1 := by omega
      have h3 : (Int.floor r : ℝ) ≤ ((Int.ceil A - 1 : ℤ) : ℝ) := Int.cast_le.mpr h2
      have h4 : ((Int.ceil A - 1 : ℤ) : ℝ) = (Int.ceil A : ℝ) - 1 := by norm_num
      rw [h4] at h3
      exact h3
    have h4 : r < (Int.floor r : ℝ) + 1 := Int.lt_floor_add_one r
    have h5 : (Int.ceil A : ℝ) ≤ A + 1 := ceil_le_add_one A
    rw [abs_of_nonneg (by linarith [hrA])]
    linarith [h4, hfr, h5, hrA]

noncomputable def morseDist (K C : ℝ) : ℝ :=
  3 * (K + C) / 2 + 36 * K + 54 * (36 * K * (K + C) + (8 * K + 4 * K * C + 4)) + 8

theorem morseDist_nonneg {K C : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C) : 0 ≤ morseDist K C := by
  have hK0 : (0:ℝ) ≤ K := zero_le_one.trans hK
  have hKC : (0:ℝ) ≤ K + C := by linarith [hK0, hC]
  have h1 : (0:ℝ) ≤ K * (K + C) := mul_nonneg hK0 hKC
  have h2 : (0:ℝ) ≤ K * C := mul_nonneg hK0 hC
  unfold morseDist
  linarith [h1, h2, hK0, hKC, hC]

theorem morseDetour_bound {K C : ℝ} {Φ : HUpper n → HUpper n}
    (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ) (hn : 1 ≤ n)
    {q : ℝ → HUpper n} (hq : ∀ s t : ℝ, dist (q s) (q t) = |s - t|)
    {A B T τ₁ D : ℝ} (hAB : A ≤ B)
    (hT : T = dist (Φ (q A)) (Φ (q B)))
    (hne : Φ (q A) ≠ Φ (q B))
    (hτ₁ : τ₁ ∈ Set.Icc 0 T)
    (hnet : ∀ p ∈ paramNet A B,
      D ≤ dist (geodFromTo (Φ (q A)) (Φ (q B)) hne τ₁) (Φ (q p)))
    (hseg : ∀ τ ∈ Set.Icc 0 T, ∃ p ∈ paramNet A B,
      dist (geodFromTo (Φ (q A)) (Φ (q B)) hne τ) (Φ (q p)) ≤ D + 1) :
    D ≤ morseDist K C - 1 := by
  classical
  have hK : (1:ℝ) ≤ K := hΦ.hK
  have hK0 : (0:ℝ) < K := one_pos.trans_le hK
  have hC0 : (0:ℝ) ≤ C := hΦ.hC
  set L := K + C with hLdef
  have hL0 : (0:ℝ) ≤ L := by linarith [hLdef, hK, hC0]
  set E4 := 8 * K + 4 * K * C + 4 with hE4def
  have hE4pos : (0:ℝ) < E4 := by
    have h1 : (0:ℝ) ≤ K * C := mul_nonneg hK0.le hC0
    linarith [hE4def, hK, h1]
  set B4 := 36 * K * L + E4 with hB4def
  have hB4pos : (0:ℝ) < B4 := by
    have h1 : (0:ℝ) ≤ 36 * K * L := mul_nonneg (by linarith [hK]) hL0
    linarith [hB4def, h1, hE4pos]
  have hMD : morseDist K C = 3 * L / 2 + 36 * K + 54 * B4 + 8 := by
    rw [hB4def, hE4def, hLdef]
    unfold morseDist
    ring
  by_contra hbig
  push Not at hbig
  have hDbig : 3 * L / 2 + 36 * K + 54 * B4 + 7 < D := by linarith [hbig, hMD]
  set w₁ := geodFromTo (Φ (q A)) (Φ (q B)) hne τ₁ with hw₁def
  have hdA : dist w₁ (Φ (q A)) = τ₁ := by
    have h1 : dist (geodFromTo (Φ (q A)) (Φ (q B)) hne 0)
        (geodFromTo (Φ (q A)) (Φ (q B)) hne τ₁) = |0 - τ₁| :=
      dist_geodFromTo hne 0 τ₁
    rw [geodFromTo_zero hne, zero_sub, abs_neg, abs_of_nonneg hτ₁.1] at h1
    rw [dist_comm] at h1
    exact h1
  have hdB : dist w₁ (Φ (q B)) = T - τ₁ := by
    have h1 : dist (geodFromTo (Φ (q A)) (Φ (q B)) hne τ₁)
        (geodFromTo (Φ (q A)) (Φ (q B)) hne T) = |τ₁ - T| := by
      have h2 := dist_geodFromTo hne τ₁ (dist (Φ (q A)) (Φ (q B)))
      rw [← hT] at h2
      exact h2
    have h3 : geodFromTo (Φ (q A)) (Φ (q B)) hne T = Φ (q B) := by
      rw [hT]
      exact geodFromTo_dist hne
    rw [h3, abs_of_nonpos (by linarith [hτ₁.2] : τ₁ - T ≤ 0)] at h1
    have h4 : dist w₁ (Φ (q B)) = -(τ₁ - T) := h1
    linarith [h4]
  have hDτA : D ≤ τ₁ := by
    have h1 := hnet A left_mem_paramNet
    linarith [h1, hdA]
  have hDτB : D ≤ T - τ₁ := by
    have h1 := hnet B right_mem_paramNet
    linarith [h1, hdB]
  set τy := max (τ₁ - 2 * D) 0 with hτydef
  set τz := min (τ₁ + 2 * D) T with hτzdef
  have hτy0 : 0 ≤ τy := le_max_right _ _
  have hT0 : 0 ≤ T := hτ₁.1.trans hτ₁.2
  have hτyT : τy ≤ T := max_le (by linarith [hτ₁.2, hDbig]) hT0
  have hτz0 : 0 ≤ τz := le_min (by linarith [hτ₁.1, hDbig]) hT0
  have hτzT : τz ≤ T := min_le_right _ _
  have hτy1 : τy ≤ τ₁ := max_le (by linarith [hDbig]) hτ₁.1
  have hτ1z : τ₁ ≤ τz := le_min (by linarith [hDbig]) hτ₁.2
  set y := geodFromTo (Φ (q A)) (Φ (q B)) hne τy with hydef
  set z := geodFromTo (Φ (q A)) (Φ (q B)) hne τz with hzdef
  have hdw₁y : dist w₁ y = τ₁ - τy := by
    have h1 := dist_geodFromTo hne τ₁ τy
    rw [abs_of_nonneg (by linarith [hτy1] : 0 ≤ τ₁ - τy)] at h1
    exact h1
  have hdw₁z : dist w₁ z = τz - τ₁ := by
    have h1 := dist_geodFromTo hne τ₁ τz
    rw [abs_of_nonpos (by linarith [hτ1z] : τ₁ - τz ≤ 0)] at h1
    have h2 : dist w₁ z = -(τ₁ - τz) := h1
    linarith [h2]
  have hdDw₁y : D ≤ dist w₁ y := by
    have h1 : τ₁ - τy = min (2 * D) τ₁ := by
      rw [hτydef, ← min_sub_sub_left]
      have h2 : τ₁ - (τ₁ - 2 * D) = 2 * D := by ring
      rw [h2, sub_zero]
    have h3 : D ≤ min (2 * D) τ₁ := le_min (by linarith [hDbig]) hDτA
    linarith [hdw₁y, h1, h3]
  have hdDw₁z : D ≤ dist w₁ z := by
    have h1 : τz - τ₁ = min (2 * D) (T - τ₁) := by
      rw [hτzdef, ← min_sub_sub_right]
      have h2 : τ₁ + 2 * D - τ₁ = 2 * D := by ring
      rw [h2]
    have h3 : D ≤ min (2 * D) (T - τ₁) := le_min (by linarith [hDbig]) hDτB
    linarith [hdw₁z, h1, h3]
  have hOnSegyz : OnSegment y z w₁ := by
    have h1 : dist y z = τz - τy := by
      have h2 := dist_geodFromTo hne τy τz
      rw [abs_of_nonpos (by linarith [hτy1, hτ1z] : τy - τz ≤ 0)] at h2
      have h3 : dist y z = -(τy - τz) := h2
      linarith [h3]
    change dist y w₁ + dist w₁ z = dist y z
    have h4 : dist y w₁ = dist w₁ y := dist_comm y w₁
    linarith [hdw₁y, hdw₁z, h1, h4]
  have hdyz : dist y z ≤ 4 * D := by
    have h1 : dist y z = τz - τy := by
      have h2 := dist_geodFromTo hne τy τz
      rw [abs_of_nonpos (by linarith [hτy1, hτ1z] : τy - τz ≤ 0)] at h2
      have h3 : dist y z = -(τy - τz) := h2
      linarith [h3]
    have h3 : τz ≤ τ₁ + 2 * D := min_le_left _ _
    have h4 : τ₁ - 2 * D ≤ τy := le_max_left _ _
    linarith [h1, h3, h4]
  obtain ⟨ry, hryP, hryd0⟩ := hseg τy ⟨hτy0, hτyT⟩
  have hryd : dist y (Φ (q ry)) ≤ D + 1 := hryd0
  obtain ⟨rz, hrzP, hrzd0⟩ := hseg τz ⟨hτz0, hτzT⟩
  have hrzd : dist z (Φ (q rz)) ≤ D + 1 := hrzd0
  have hd'z' : dist (Φ (q ry)) (Φ (q rz)) ≤ 6 * D + 2 := by
    have h1 := dist_triangle (Φ (q ry)) y (Φ (q rz))
    have h2 := dist_triangle y z (Φ (q rz))
    have hc1 : dist (Φ (q ry)) y = dist y (Φ (q ry)) :=
      dist_comm _ _
    linarith [h1, h2, hryd, hrzd, hdyz, hc1]
  have hrr : |ry - rz| ≤ K * (6 * D + 2 + C) := by
    have h1 := hΦ.lower (q ry) (q rz)
    rw [hq _ _] at h1
    have h2 : K⁻¹ * |ry - rz| ≤ 6 * D + 2 + C := by linarith [h1, hd'z']
    have h3 : K * (K⁻¹ * |ry - rz|) ≤ K * (6 * D + 2 + C) :=
      mul_le_mul_of_nonneg_left h2 hK0.le
    rw [← mul_assoc, mul_inv_cancel₀ hK0.ne', one_mul] at h3
    exact h3
  set H := ⌊|ry - rz|⌋₊ + 1 with hHdef
  have hH0 : (0:ℝ) < (H : ℝ) := by
    have h1 : (1:ℝ) ≤ (H : ℝ) := by
      rw [hHdef, Nat.cast_add, Nat.cast_one]
      have h2 : (0:ℝ) ≤ (⌊|ry - rz|⌋₊ : ℕ) := Nat.cast_nonneg _
      linarith [h2]
    linarith [h1]
  have hHne : (H : ℝ) ≠ 0 := ne_of_gt hH0
  set a : ℕ → ℝ := fun j => ry + (j : ℝ) / (H : ℝ) * (rz - ry) with hadef
  have ha0 : a 0 = ry := by
    change ry + ((0 : ℕ) : ℝ) / (H : ℝ) * (rz - ry) = ry
    rw [Nat.cast_zero, zero_div, zero_mul, add_zero]
  have haH : a H = rz := by
    change ry + (H : ℝ) / (H : ℝ) * (rz - ry) = rz
    rw [div_self hHne, one_mul, add_sub_cancel]
  have hhop : ∀ j : ℕ, |a (j + 1) - a j| ≤ 1 := by
    intro j
    have h1 : a (j + 1) - a j = (1 / (H : ℝ)) * (rz - ry) := by
      change ry + ↑(j + 1) / ↑H * (rz - ry) - (ry + ↑j / ↑H * (rz - ry)) = _
      have e1 : (↑(j + 1) : ℝ) = (j : ℝ) + 1 := by norm_cast
      rw [e1, add_div]
      ring
    rw [h1, abs_mul]
    have h3 : |(1 : ℝ) / (H : ℝ)| = 1 / (H : ℝ) := abs_of_pos (by positivity)
    rw [h3]
    have h4 : |ry - rz| < (⌊|ry - rz|⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [abs_sub_comm ry rz] at h4
    have h5 : |rz - ry| < (H : ℝ) := by
      rw [hHdef, Nat.cast_add, Nat.cast_one, abs_sub_comm ry rz]
      exact h4
    rw [one_div, mul_comm, ← div_eq_mul_inv, div_le_one hH0]
    linarith [h5]
  have ha_mem : ∀ j : ℕ, j ≤ H → A ≤ a j ∧ a j ≤ B := by
    intro j hj
    have hryB := mem_paramNet_bound hAB hryP
    have hrzB := mem_paramNet_bound hAB hrzP
    have hθ0 : (0:ℝ) ≤ (j : ℝ) / (H : ℝ) := by positivity
    have hθ1 : (j : ℝ) / (H : ℝ) ≤ 1 := by
      rw [div_le_one hH0]
      exact Nat.cast_le.mpr hj
    rcases le_total ry rz with hrr' | hrr'
    · have hb1 : A ≤ a j := by
        have h2 : (0:ℝ) ≤ (j : ℝ) / (H : ℝ) * (rz - ry) := mul_nonneg hθ0 (by linarith [hrr'])
        have h3 : a j = ry + (j : ℝ) / (H : ℝ) * (rz - ry) := rfl
        linarith [h2, h3, hryB.1]
      have hb2 : a j ≤ B := by
        have h2 : (j : ℝ) / (H : ℝ) * (rz - ry) ≤ 1 * (rz - ry) :=
          mul_le_mul_of_nonneg_right hθ1 (by linarith [hrr'])
        have h3 : a j = ry + (j : ℝ) / (H : ℝ) * (rz - ry) := rfl
        linarith [h2, h3, hrzB.2]
      exact ⟨hb1, hb2⟩
    · have hb1 : A ≤ a j := by
        have h2 : 1 * (rz - ry) ≤ (j : ℝ) / (H : ℝ) * (rz - ry) :=
          mul_le_mul_of_nonpos_right hθ1 (by linarith [hrr'])
        have h3 : a j = ry + (j : ℝ) / (H : ℝ) * (rz - ry) := rfl
        linarith [h2, h3, hrzB.1]
      have hb2 : a j ≤ B := by
        have h2 : (j : ℝ) / (H : ℝ) * (rz - ry) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hθ0 (by linarith [hrr'])
        have h3 : a j = ry + (j : ℝ) / (H : ℝ) * (rz - ry) := rfl
        linarith [h2, h3, hryB.2]
      exact ⟨hb1, hb2⟩
  have hchain_far : ∀ j : ℕ, j ≤ H → D - L ≤ dist w₁ (Φ (q (a j))) := by
    intro j hj
    obtain ⟨pj, hpjP, hpjd⟩ := exists_net_approx (ha_mem j hj).1 (ha_mem j hj).2
    have h1 := hnet pj hpjP
    have h2 := hΦ.upper (q pj) (q (a j))
    rw [hq _ _] at h2
    have h3 : |pj - a j| = |a j - pj| := abs_sub_comm _ _
    rw [h3] at h2
    have h4 : dist (Φ (q pj)) (Φ (q (a j))) ≤ L := by
      have h5 : K * |a j - pj| + C ≤ K * 1 + C := by
        have h6 : K * |a j - pj| ≤ K * 1 :=
          mul_le_mul_of_nonneg_left hpjd hK0.le
        linarith [h6]
      linarith [h2, h5, hLdef]
    have h7 := dist_triangle w₁ (Φ (q (a j))) (Φ (q pj))
    have hc1 : dist (Φ (q (a j))) (Φ (q pj))
        = dist (Φ (q pj)) (Φ (q (a j))) := dist_comm _ _
    linarith [h7, h1, h4, hc1]
  have hhopd : ∀ j : ℕ, dist (Φ (q (a j))) (Φ (q (a (j + 1)))) ≤ L := by
    intro j
    have h1 := hΦ.upper (q (a j)) (q (a (j + 1)))
    rw [hq _ _] at h1
    have h2 : K * |a j - a (j + 1)| + C ≤ K * 1 + C := by
      have h3 : |a j - a (j + 1)| = |a (j + 1) - a j| := abs_sub_comm _ _
      have h4 : K * |a j - a (j + 1)| ≤ K * 1 := by
        rw [h3]
        exact mul_le_mul_of_nonneg_left (hhop j) hK0.le
      linarith [h4]
    linarith [h1, h2, hLdef]
  obtain ⟨g, hg⟩ := exists_po_smul_eq hn w₁ basepointH
  let := poMulAction hn
  have hg' : g • w₁ = basepointH := hg
  set p : ℕ → HUpper n := fun j => g • (Φ (q (a j))) with hpdef
  have hdistp : ∀ j : ℕ, dist basepointH (p j) = dist w₁ (Φ (q (a j))) := by
    intro j
    change dist basepointH (g • (Φ (q (a j)))) = _
    rw [← hg']
    exact po_dist_smul hn g w₁ (Φ (q (a j)))
  have hGPp : ∀ j k : ℕ, gromovProduct basepointH (p j) (p k)
      = gromovProduct w₁ (Φ (q (a j))) (Φ (q (a k))) := by
    intro j k
    have h1 := gromovProduct_po_smul hn g w₁ (Φ (q (a j))) (Φ (q (a k)))
    rw [hg'] at h1
    exact h1
  set R' := D - 3 * L / 2 with hR'def
  have hper : ∀ j : ℕ, j < H → eNorm (radial (p j) - radial (p (j + 1))) ≤ 4 * Real.exp (-R') := by
    intro j hj
    have hj' : j ≤ H := le_of_lt hj
    have hj1 : j + 1 ≤ H := hj
    apply eNorm_radial_sub_le
    · rw [hdistp]
      have h1 := hchain_far j hj'
      linarith [h1, hL0, hR'def]
    · rw [hdistp]
      have h1 := hchain_far (j + 1) hj1
      linarith [h1, hL0, hR'def]
    · rw [hGPp]
      have h1 := hchain_far j hj'
      have h2 := hchain_far (j + 1) hj1
      have h3 := hhopd j
      change R' ≤ (dist w₁ (Φ (q (a j))) + dist w₁ (Φ (q (a (j + 1))))
        - dist (Φ (q (a j))) (Φ (q (a (j + 1))))) / 2
      linarith [h1, h2, h3, hR'def, hL0]
  set qy := g • y with hqydef
  set qz := g • z with hqzdef
  have hOnSegQ : OnSegment qy qz basepointH := by
    have h1 := onSegment_po_smul hn g y z w₁ hOnSegyz
    rw [hg'] at h1
    exact h1
  have hdistqy : dist basepointH qy = dist w₁ y := by
    change dist basepointH (g • y) = _
    rw [← hg']
    exact po_dist_smul hn g w₁ y
  have hdistqz : dist basepointH qz = dist w₁ z := by
    change dist basepointH (g • z) = _
    rw [← hg']
    exact po_dist_smul hn g w₁ z
  have hlemB : 3 / 2 ≤ eNorm (radial qy - radial qz) := by
    apply three_halves_le_eNorm_radial_sub_of_onSegment hOnSegQ
    · rw [hdistqy]; linarith [hdDw₁y, hDbig]
    · rw [hdistqz]; linarith [hdDw₁z, hDbig]
  have hendy : eNorm (radial qy - radial (p 0)) ≤ 4 * Real.exp (-((D - 1) / 2)) := by
    apply eNorm_radial_sub_le
    · rw [hdistqy]; linarith [hdDw₁y, hDbig]
    · rw [hdistp, ha0]
      have h1 := hnet ry hryP
      linarith [h1, hDbig]
    · have h1 : gromovProduct basepointH qy (p 0) = gromovProduct w₁ y (Φ (q (a 0))) := by
        have h2 := gromovProduct_po_smul hn g w₁ y (Φ (q (a 0)))
        rw [hg'] at h2
        exact h2
      rw [h1, ha0]
      have h2 := hnet ry hryP
      change (D - 1) / 2 ≤ (dist w₁ y + dist w₁ (Φ (q ry))
        - dist y (Φ (q ry))) / 2
      linarith [hdDw₁y, h2, hryd, hDbig]
  have hendz : eNorm (radial (p H) - radial qz) ≤ 4 * Real.exp (-((D - 1) / 2)) := by
    apply eNorm_radial_sub_le
    · rw [hdistp, haH]
      have h1 := hnet rz hrzP
      linarith [h1, hDbig]
    · rw [hdistqz]; linarith [hdDw₁z, hDbig]
    · have h1 : gromovProduct basepointH (p H) qz = gromovProduct w₁ (Φ (q (a H))) z := by
        have h2 := gromovProduct_po_smul hn g w₁ (Φ (q (a H))) z
        rw [hg'] at h2
        exact h2
      rw [h1, haH]
      have h2 := hnet rz hrzP
      change (D - 1) / 2 ≤ (dist w₁ (Φ (q rz)) + dist w₁ z
        - dist (Φ (q rz)) z) / 2
      have hc1 : dist (Φ (q rz)) z = dist z (Φ (q rz)) := dist_comm _ _
      linarith [hdDw₁z, h2, hrzd, hDbig, hc1]
  have hsumle : ∑ j ∈ Finset.range H, eNorm (radial (p j) - radial (p (j + 1)))
      ≤ H * (4 * Real.exp (-R')) := by
    calc ∑ j ∈ Finset.range H, eNorm (radial (p j) - radial (p (j + 1)))
        ≤ ∑ _ ∈ Finset.range H, (4 * Real.exp (-R')) :=
          Finset.sum_le_sum fun j hj => hper j (Finset.mem_range.mp hj)
      _ = H * (4 * Real.exp (-R')) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hassm : eNorm (radial qy - radial qz)
      ≤ 2 * (4 * Real.exp (-((D - 1) / 2))) + H * (4 * Real.exp (-R')) := by
    have hs1 := eNorm_sub_le (radial qy) (radial (p 0)) (radial qz)
    have hs2 := eNorm_sub_le (radial (p 0)) (radial (p H)) (radial qz)
    have hs3 := eNorm_radial_sub_le_sum H p
    linarith [hs1, hs2, hs3, hsumle, hendy, hendz]
  have h8 : 8 * Real.exp (-((D - 1) / 2)) < 1 / 2 := by
    have hx3 : (3:ℝ) ≤ (D - 1) / 2 := by linarith [hDbig]
    have hex : Real.exp 3 ≤ Real.exp ((D - 1) / 2) := Real.exp_le_exp.mpr hx3
    have he3 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [show (3:ℝ) = 1 + 1 + 1 from by norm_num, Real.exp_add, Real.exp_add]
      ring
    have he1 : (2.7182818283:ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_d9
    have he13 : (2.7182818283:ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he1 3
    have h16 : (16:ℝ) < Real.exp ((D - 1) / 2) := by
      have h17 : (16:ℝ) < (2.7182818283:ℝ) ^ 3 := by norm_num
      linarith [hex, he3, he13, h17]
    have hinv : Real.exp (-((D - 1) / 2)) < (16:ℝ)⁻¹ := by
      rw [Real.exp_neg]
      exact (inv_lt_inv₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 16)).mpr h16
    have h16' : (8:ℝ) * (16:ℝ)⁻¹ = 1 / 2 := by norm_num
    calc 8 * Real.exp (-((D - 1) / 2)) < 8 * (16:ℝ)⁻¹ :=
          mul_lt_mul_of_pos_left hinv (by norm_num : (0:ℝ) < 8)
      _ = 1 / 2 := h16'
  have hbig1 : (1:ℝ) < H * (4 * Real.exp (-R')) := by linarith [hlemB, hassm, h8]
  have hR'4 : Real.exp R' < 4 * H := by
    have h1 : (1:ℝ) < 4 * H * (Real.exp R')⁻¹ := by
      have h2 : Real.exp (-R') = (Real.exp R')⁻¹ := Real.exp_neg R'
      rw [h2] at hbig1
      have h3 : H * (4 * (Real.exp R')⁻¹) = 4 * H * (Real.exp R')⁻¹ := by ring
      rw [h3] at hbig1
      exact hbig1
    have h3 : Real.exp R' * 1 < Real.exp R' * (4 * H * (Real.exp R')⁻¹) :=
      mul_lt_mul_of_pos_left h1 (Real.exp_pos R')
    have h4 : Real.exp R' * (4 * H * (Real.exp R')⁻¹) = 4 * H := by
      have hne : Real.exp R' ≠ 0 := (Real.exp_pos R').ne'
      field_simp
    rw [mul_one, h4] at h3
    exact h3
  have hHbound : (H:ℝ) ≤ K * (6 * D + 2 + C) + 1 := by
    have h1 : (H:ℝ) ≤ |ry - rz| + 1 := by
      rw [hHdef, Nat.cast_add, Nat.cast_one]
      have h2 : ((⌊|ry - rz|⌋₊ : ℕ) : ℝ) ≤ |ry - rz| := Nat.floor_le (abs_nonneg _)
      linarith [h2]
    linarith [h1, hrr]
  have hexpD : Real.exp R' < 24 * K * D + E4 := by
    have h1 : 4 * (H:ℝ) ≤ 4 * (K * (6 * D + 2 + C) + 1) :=
      mul_le_mul_of_nonneg_left hHbound (by norm_num)
    have h2 : 4 * (K * (6 * D + 2 + C) + 1) = 24 * K * D + E4 := by rw [hE4def]; ring
    linarith [hR'4, h1, h2]
  have hu : 36 * K + 54 * B4 + 7 < R' := by linarith [hDbig, hR'def]
  have hu0 : (0:ℝ) < R' := by linarith [hu, hK, hB4pos]
  have hexpu : Real.exp R' < 24 * K * R' + B4 := by
    have hconv : 24 * K * D + E4 = 24 * K * R' + B4 := by
      rw [hR'def, hB4def]
      ring
    linarith [hexpD, hconv]
  have hcube : R' ^ 3 / 27 ≤ Real.exp R' := by
    have h1 : R' / 3 + 1 ≤ Real.exp (R' / 3) := Real.add_one_le_exp (R' / 3)
    have h2 : (R' / 3) ^ 3 ≤ (R' / 3 + 1) ^ 3 :=
      pow_le_pow_left₀ (by linarith [hu0]) (by linarith) 3
    have h3 : (R' / 3 + 1) ^ 3 ≤ (Real.exp (R' / 3)) ^ 3 :=
      pow_le_pow_left₀ (by linarith [hu0]) h1 3
    have h4 : Real.exp R' = (Real.exp (R' / 3)) ^ 3 := by
      convert Real.exp_nat_mul (R' / 3) 3 using 1 ; congr 1 ; ring
    have h5 : R' ^ 3 / 27 = (R' / 3) ^ 3 := by ring
    rw [h5, h4]
    exact h2.trans h3
  have hfin : R' ^ 3 < 648 * K * R' + 27 * B4 := by
    have h1 : R' ^ 3 / 27 < 24 * K * R' + B4 := lt_of_le_of_lt hcube hexpu
    rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 27)] at h1
    linarith [h1]
  have hfin2 : 648 * K * R' + 27 * B4 < R' ^ 3 := by
    have hu36 : 36 * K < R' := by linarith [hu, hB4pos]
    have huB : 54 * B4 < R' := by linarith [hu, hK]
    have hu1 : (1:ℝ) < R' := by linarith [hu, hK, hB4pos]
    have hKsq : 1296 * K ≤ (36 * K) * (36 * K) := by
      have h1 : (1:ℝ) * K ≤ K * K := mul_le_mul_of_nonneg_right hK hK0.le
      have h2 : (36 * K) * (36 * K) = 1296 * (K * K) := by ring
      rw [h2]
      linarith [h1]
    have hu2 : 1296 * K < R' * R' := by
      have hs1 : (36 * K) * (36 * K) < (36 * K) * R' :=
        mul_lt_mul_of_pos_left hu36 (by linarith [hK])
      have hs2 : (36 * K) * R' < R' * R' := mul_lt_mul_of_pos_right hu36 hu0
      linarith [hKsq, hs1, hs2]
    have hu3a : 648 * K * R' < R' ^ 3 / 2 := by
      have h1 : R' * (1296 * K) < R' * (R' * R') := mul_lt_mul_of_pos_left hu2 hu0
      have h2 : R' * (R' * R') = R' ^ 3 := by ring
      rw [h2] at h1
      linarith [h1]
    have hu3b : 27 * B4 < R' ^ 3 / 2 := by
      have h1 : (1:ℝ) * 1 < R' * R' := by
        have hs1 : (1:ℝ) * 1 < 1 * R' := mul_lt_mul_of_pos_left hu1 one_pos
        have hs2 : (1:ℝ) * R' < R' * R' := mul_lt_mul_of_pos_right hu1 hu0
        linarith [hs1, hs2]
      have hu2' : (1:ℝ) < R' ^ 2 := by
        have h2 : R' * R' = R' ^ 2 := (pow_two R').symm
        rw [← h2]
        linarith [h1]
      have h3 : R' * 1 < R' * R' ^ 2 := mul_lt_mul_of_pos_left hu2' hu0
      have h4 : R' * R' ^ 2 = R' ^ 3 := by ring
      rw [mul_one, h4] at h3
      linarith [huB, h3, hB4pos]
    have hsum : R' ^ 3 / 2 + R' ^ 3 / 2 = R' ^ 3 := by ring
    linarith [hu3a, hu3b, hsum]
  linarith [hfin, hfin2]

theorem eight_le_morseDist {K C : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C) : 8 ≤ morseDist K C := by
  have hK0 : (0:ℝ) ≤ K := zero_le_one.trans hK
  have hKC : (0:ℝ) ≤ K + C := by linarith [hK0, hC]
  have h1 : (0:ℝ) ≤ K * (K + C) := mul_nonneg hK0 hKC
  have h2 : (0:ℝ) ≤ K * C := mul_nonneg hK0 hC
  unfold morseDist
  linarith [h1, h2, hK0, hKC, hC, hK]

theorem exists_netPoint_le_morseDist {K C : ℝ} {Φ : HUpper n → HUpper n}
    (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ) (hn : 1 ≤ n)
    {q : ℝ → HUpper n} (hq : ∀ s t : ℝ, dist (q s) (q t) = |s - t|)
    {A B : ℝ} (hAB : A ≤ B) {w : HUpper n}
    (hw : OnSegment (Φ (q A)) (Φ (q B)) w) :
    ∃ r : ℝ, r ∈ paramNet A B ∧ dist w (Φ (q r)) ≤ morseDist K C := by
  classical
  have hK : (1:ℝ) ≤ K := hΦ.hK
  have hC0 : (0:ℝ) ≤ C := hΦ.hC
  have hMD0 := morseDist_nonneg hK hC0
  set xA := Φ (q A) with hxAdef
  set xB := Φ (q B) with hxBdef
  by_cases hxAB : xA = xB
  · have h1 : dist xA w + dist w xB = 0 := by
      have h2 : dist xA w + dist w xB = dist xA xB := hw
      rw [hxAB] at h2 ⊢
      rw [dist_self] at h2
      exact h2
    have h3 : dist xA w = 0 := by
      have h4 := dist_nonneg (x := xA) (y := w)
      have h5 := dist_nonneg (x := w) (y := xB)
      linarith [h1, h4, h5]
    have hwxA : w = xA := (dist_eq_zero.mp h3).symm
    refine ⟨A, left_mem_paramNet, ?_⟩
    have h6 : dist w (Φ (q A)) = 0 := by
      have h7 : dist w xA = 0 := dist_eq_zero.mpr hwxA
      have h8 : dist xA (Φ (q A)) = 0 := by
        have h9 : xA = Φ (q A) := hxAdef
        rw [h9]
        exact dist_self _
      have h10 : dist w (Φ (q A)) ≤ dist w xA + dist xA (Φ (q A)) :=
        dist_triangle _ _ _
      linarith [h7, h8, h10, dist_nonneg (x := w) (y := Φ (q A))]
    rw [h6]
    exact hMD0
  · set T := dist xA xB with hTdef
    have hT0 : 0 ≤ T := dist_nonneg
    have hmin : ∀ u : HUpper n, ∃ p₀ ∈ paramNet A B,
        ∀ p ∈ paramNet A B, dist u (Φ (q p₀)) ≤ dist u (Φ (q p)) :=
      fun u => Finset.exists_min_image _ _ ⟨A, left_mem_paramNet⟩
    set npar : HUpper n → ℝ := fun u => Classical.choose (hmin u) with hnpardef
    have hnpar_mem : ∀ u, npar u ∈ paramNet A B := fun u => (Classical.choose_spec (hmin u)).1
    have hnpar_min : ∀ u, ∀ p ∈ paramNet A B, dist u (Φ (q (npar u)))
        ≤ dist u (Φ (q p)) := fun u => (Classical.choose_spec (hmin u)).2
    set dS : HUpper n → ℝ := fun u => dist u (Φ (q (npar u))) with hdSdef
    set Sset : Set ℝ := (fun τ => dS (geodFromTo xA xB hxAB τ)) '' Set.Icc 0 T with hSsetdef
    have hSne : Sset.Nonempty := ⟨dS (geodFromTo xA xB hxAB 0), ⟨0, ⟨le_refl 0, hT0⟩, rfl⟩⟩
    have hSbdd : BddAbove Sset := by
      refine ⟨T, ?_⟩
      intro v hv
      rcases hv with ⟨τ, hτ, rfl⟩
      have h1 : dS (geodFromTo xA xB hxAB τ) ≤ dist (geodFromTo xA xB hxAB τ) (Φ (q A)) :=
        hnpar_min _ A left_mem_paramNet
      have h2 : dist (geodFromTo xA xB hxAB τ) (Φ (q A)) = τ := by
        have h3 : dist (geodFromTo xA xB hxAB 0) (geodFromTo xA xB hxAB τ) = |0 - τ| :=
          dist_geodFromTo hxAB 0 τ
        rw [geodFromTo_zero hxAB, zero_sub, abs_neg, abs_of_nonneg hτ.1] at h3
        rw [dist_comm] at h3
        exact h3
      linarith [h1, h2, hτ.2]
    have hsup : sSup Sset ≤ morseDist K C := by
      by_contra hcontra
      push Not at hcontra
      have hlt : sSup Sset - 1 < sSup Sset := by linarith
      obtain ⟨v, hv, hD1v⟩ := exists_lt_of_lt_csSup hSne hlt
      rcases hv with ⟨τ₁, hτ₁, hveq⟩
      set w₁ := geodFromTo xA xB hxAB τ₁ with hw₁def
      set D := dS w₁ with hDdef
      have hvD : v = D := hveq.symm
      have hDgt : morseDist K C - 1 < D := by linarith [hD1v, hvD, hcontra]
      have hD7 : 7 ≤ D := by
        have h1 := eight_le_morseDist hK hC0
        linarith [h1, hDgt]
      have hnet : ∀ p ∈ paramNet A B, D ≤ dist w₁ (Φ (q p)) := by
        intro p hp
        have h1 := hnpar_min w₁ p hp
        have h2 : dS w₁ = dist w₁ (Φ (q (npar w₁))) := rfl
        linarith [h1, h2, hDdef]
      have hseg' : ∀ τ ∈ Set.Icc 0 T, ∃ p ∈ paramNet A B,
          dist (geodFromTo xA xB hxAB τ) (Φ (q p)) ≤ D + 1 := by
        intro τ hτ
        refine ⟨npar (geodFromTo xA xB hxAB τ), hnpar_mem _, ?_⟩
        have h1 : dS (geodFromTo xA xB hxAB τ) ≤ sSup Sset := le_csSup hSbdd ⟨τ, hτ, rfl⟩
        have h3 : sSup Sset < D + 1 := by linarith [hD1v, hvD]
        have h4 : dS (geodFromTo xA xB hxAB τ)
            = dist (geodFromTo xA xB hxAB τ) (Φ (q (npar (geodFromTo xA xB hxAB τ)))) :=
          rfl
        linarith [h1, h3, h4]
      have hT' : T = dist (Φ (q A)) (Φ (q B)) := hTdef
      have hne' : Φ (q A) ≠ Φ (q B) := hxAB
      have hnet' : ∀ p ∈ paramNet A B,
          D ≤ dist (geodFromTo (Φ (q A)) (Φ (q B)) hne' τ₁) (Φ (q p)) :=
        hnet
      have hseg'' : ∀ τ ∈ Set.Icc 0 T, ∃ p ∈ paramNet A B,
          dist (geodFromTo (Φ (q A)) (Φ (q B)) hne' τ) (Φ (q p))
            ≤ D + 1 := hseg'
      have hbound := morseDetour_bound hΦ hn hq hAB hT' hne' hτ₁ hnet' hseg''
      linarith [hbound, hDgt]
    have hwgeod : w = geodFromTo xA xB hxAB (dist xA w) := eq_geodFromTo_of_onSegment hxAB hw
    have hτw : dist xA w ∈ Set.Icc 0 T := by
      refine ⟨dist_nonneg, ?_⟩
      have h1 : dist xA w + dist w xB = dist xA xB := hw
      have h2 : dist xA xB = T := hTdef.symm
      have h3 := dist_nonneg (x := w) (y := xB)
      linarith [h1, h2, h3]
    have hdw : dS w ≤ sSup Sset := by
      have h1 : dS (geodFromTo xA xB hxAB (dist xA w)) ∈ Sset := ⟨dist xA w, hτw, rfl⟩
      rw [← hwgeod] at h1
      exact le_csSup hSbdd h1
    refine ⟨npar w, hnpar_mem w, ?_⟩
    have h4 : dS w = dist w (Φ (q (npar w))) := rfl
    linarith [hdw, hsup, h4]

theorem exists_parameter_le_morseDist {K C : ℝ} {Φ : HUpper n → HUpper n}
    (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ) (hn : 1 ≤ n)
    {q : ℝ → HUpper n} (hq : ∀ s t : ℝ, dist (q s) (q t) = |s - t|)
    {s t : ℝ} {w : HUpper n}
    (hw : OnSegment (Φ (q s)) (Φ (q t)) w) :
    ∃ r : ℝ, r ∈ paramNet (min s t) (max s t)
      ∧ dist w (Φ (q r)) ≤ morseDist K C := by
  rcases le_total s t with hst | hst
  · rw [min_eq_left hst, max_eq_right hst]
    exact exists_netPoint_le_morseDist hΦ hn hq hst hw
  · rw [min_eq_right hst, max_eq_left hst]
    exact exists_netPoint_le_morseDist hΦ hn hq hst (onSegment_symm hw)

theorem onSegment_tendsto_of_isPseudoIsometry {K C : ℝ} {Φ : HUpper n → HUpper n}
    (hΦ : PseudoIsometry.IsPseudoIsometry K C Φ) (hn : 1 ≤ n)
    (o : HUpper n) (ξ : BoundaryH n) (M : ℝ) :
    ∃ N : ℕ, ∀ s ≥ N, ∀ t ≥ N, ∀ w : HUpper n,
      OnSegment (Φ (rayTo o ξ (s : ℝ))) (Φ (rayTo o ξ (t : ℝ))) w → M ≤ dist (Φ o) w := by
  have hK : (1:ℝ) ≤ K := hΦ.hK
  have hK0 : (0:ℝ) < K := one_pos.trans_le hK
  have hC0 : (0:ℝ) ≤ C := hΦ.hC
  set N0 := ⌈K * (M + morseDist K C + C)⌉₊ with hN0def
  refine ⟨N0 + 1, fun s hsN t htN w hw => ?_⟩
  by_contra hlt
  push Not at hlt
  have hs0 : (0:ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have ht0 : (0:ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  obtain ⟨r, hrP, hrd⟩ : ∃ r : ℝ, r ∈ paramNet (min (s:ℝ) (t:ℝ)) (max (s:ℝ) (t:ℝ))
      ∧ dist w (Φ (rayTo o ξ r)) ≤ morseDist K C := by
    rcases le_total (s:ℝ) (t:ℝ) with hst | hst
    · have e1 : min (s:ℝ) (t:ℝ) = s := min_eq_left hst
      have e2 : max (s:ℝ) (t:ℝ) = t := max_eq_right hst
      rw [e1, e2]
      exact exists_netPoint_le_morseDist hΦ hn (dist_rayTo o ξ) hst hw
    · have e1 : min (s:ℝ) (t:ℝ) = t := min_eq_right hst
      have e2 : max (s:ℝ) (t:ℝ) = s := max_eq_left hst
      rw [e1, e2]
      exact exists_netPoint_le_morseDist hΦ hn (dist_rayTo o ξ) hst (onSegment_symm hw)
  have hrb := mem_paramNet_bound min_le_max hrP
  have hmin0 : (0:ℝ) ≤ min (s:ℝ) (t:ℝ) := le_min hs0 ht0
  have hr0 : (0:ℝ) ≤ r := by linarith [hrb.1, hmin0]
  have h1 : dist (Φ o) (Φ (rayTo o ξ r)) < M + morseDist K C := by
    have h2 := dist_triangle (Φ o) w (Φ (rayTo o ξ r))
    linarith [h2, hrd, hlt]
  have h3 : K⁻¹ * r - C ≤ dist (Φ o) (Φ (rayTo o ξ r)) := by
    have h4 := hΦ.lower o (rayTo o ξ r)
    have h5 : dist o (rayTo o ξ r) = r := by
      have h6 : dist (rayTo o ξ 0) (rayTo o ξ r) = |0 - r| := dist_rayTo o ξ 0 r
      rw [rayTo_zero, zero_sub, abs_neg, abs_of_nonneg hr0] at h6
      exact h6
    rw [h5] at h4
    exact h4
  have h6 : r < K * (M + morseDist K C + C) := by
    have h7 : K⁻¹ * r < M + morseDist K C + C := by linarith [h1, h3]
    have h8 : K * (K⁻¹ * r) < K * (M + morseDist K C + C) := mul_lt_mul_of_pos_left h7 hK0
    rw [← mul_assoc, mul_inv_cancel₀ hK0.ne', one_mul] at h8
    exact h8
  have hN : K * (M + morseDist K C + C) < (N0 + 1 : ℕ) := by
    rw [Nat.cast_add, Nat.cast_one]
    have h9 : K * (M + morseDist K C + C) ≤ (⌈K * (M + morseDist K C + C)⌉₊ : ℝ) :=
      Nat.le_ceil _
    rw [hN0def]
    linarith [h9]
  have h8 : ((N0 + 1 : ℕ) : ℝ) ≤ r := by
    have h10 : ((N0 + 1 : ℕ) : ℝ) ≤ (s : ℝ) := by
      have h11 : N0 + 1 ≤ s := hsN
      exact Nat.cast_le.mpr h11
    have h11 : ((N0 + 1 : ℕ) : ℝ) ≤ (t : ℝ) := by
      have h12 : N0 + 1 ≤ t := htN
      exact Nat.cast_le.mpr h12
    have h9 : ((N0 + 1 : ℕ) : ℝ) ≤ min (s:ℝ) (t:ℝ) := le_min h10 h11
    linarith [h9, hrb.1]
  linarith [h6, hN, h8]

end DifferentialGeometry.MorseDivergence

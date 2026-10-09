/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Homeomorphism
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Busemann.Basic

noncomputable section

open Filter
open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.BoundaryVisual

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary
open BoundaryTopology HyperbolicGeometry HyperbolicTransitive
open HyperbolicConvexity GromovBoundary AsymptoticRays BoundaryHomeomorph Busemann

variable {n : ℕ}

def height (o : HUpper n) (a : BoundaryH n) : ℝ := -lorB o.val a.val

theorem height_pos (o : HUpper n) (a : BoundaryH n) : 0 < height o a :=
  neg_lorB_upper_boundary_pos o a

@[simp] theorem height_basepoint (a : BoundaryH n) : height basepointH a = 1 := by
  simp [height, lorB_basepointH_boundary]

def ratio (o : HUpper n) (a b : BoundaryH n) : ℝ :=
  bratioB a b / (height o a * height o b)

@[simp] theorem ratio_basepoint (a b : BoundaryH n) : ratio basepointH a b = bratioB a b := by
  simp [ratio]

theorem bratioB_comm (a b : BoundaryH n) : bratioB a b = bratioB b a := by
  exact congrArg Neg.neg (lorB_comm a.val b.val)

@[simp] theorem bratioB_self (a : BoundaryH n) : bratioB a a = 0 := by
  simp [bratioB, a.is_null]

theorem bratioB_pos {a b : BoundaryH n} (hab : a ≠ b) : 0 < bratioB a b :=
  lt_of_le_of_ne (bratioB_nonneg a b) (fun h => hab (boundary_eq_of_bratioB_eq_zero h.symm))

theorem continuous_bratioB_right (b : BoundaryH n) : Continuous (fun a => bratioB a b) :=
  (continuous_lorB_pair.comp (isEmbedding_val.continuous.prodMk continuous_const)).neg

def chordDist (a b : BoundaryH n) : ℝ := dist (spatial a) (spatial b)

theorem chordDist_nonneg (a b : BoundaryH n) : 0 ≤ chordDist a b := dist_nonneg

theorem chordDist_sq (a b : BoundaryH n) : chordDist a b ^ 2 = 2 * bratioB a b := by
  calc
    chordDist a b ^ 2 = ∑ i : Fin n, (a.val (Sum.inl i) - b.val (Sum.inl i)) ^ 2 := by
      simp only [chordDist, dist_eq_norm, EuclideanSpace.norm_sq_eq, PiLp.sub_apply,
        spatial_apply, Real.norm_eq_abs, sq_abs]
    _ = sdot (a.val - b.val) (a.val - b.val) := by
      simp only [sdot, Pi.sub_apply, pow_two]
    _ = 2 * bratioB a b := sdot_sub_self_eq_two_bratioB a b

def antipode (a : BoundaryH n) : BoundaryH n :=
  fromSphere ⟨-spatial a, by simp [norm_spatial]⟩

theorem sdot_antipode (a b : BoundaryH n) :
    sdot b.val (antipode a).val = -sdot b.val a.val := by
  change (∑ i : Fin n, b.val (Sum.inl i) * -a.val (Sum.inl i)) =
    -(∑ i : Fin n, b.val (Sum.inl i) * a.val (Sum.inl i))
  simp only [mul_neg, Finset.sum_neg_distrib]

theorem bratioB_antipode (a b : BoundaryH n) :
    bratioB b (antipode a) = 2 - bratioB b a := by
  simp only [bratioB, lorB, sdot_antipode, b.tc_eq, a.tc_eq, (antipode a).tc_eq]
  ring

@[simp] theorem bratioB_self_antipode (a : BoundaryH n) : bratioB a (antipode a) = 2 := by
  rw [bratioB_antipode, bratioB_self, sub_zero]

theorem ne_antipode (a : BoundaryH n) : a ≠ antipode a := by
  intro h
  have he := bratioB_self_antipode a
  rw [← h, bratioB_self] at he
  norm_num at he

theorem ratio_nonneg (o : HUpper n) (a b : BoundaryH n) : 0 ≤ ratio o a b :=
  div_nonneg (bratioB_nonneg a b) (mul_pos (height_pos o a) (height_pos o b)).le

theorem ratio_pos (o : HUpper n) {a b : BoundaryH n} (hab : a ≠ b) : 0 < ratio o a b :=
  div_pos (bratioB_pos hab) (mul_pos (height_pos o a) (height_pos o b))

theorem ratio_comm (o : HUpper n) (a b : BoundaryH n) : ratio o a b = ratio o b a := by
  rw [ratio, ratio, bratioB_comm a b, mul_comm (height o a)]

def interiorRatio (o x y : HUpper n) : ℝ :=
  Real.cosh (dist x y) / (Real.cosh (dist o x) * Real.cosh (dist o y))

theorem interiorRatio_nonneg (o x y : HUpper n) : 0 ≤ interiorRatio o x y :=
  div_nonneg (Real.cosh_pos _).le (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)).le

@[simp] theorem interiorRatio_basepoint (x y : HUpper n) :
    interiorRatio basepointH x y = bratio x y := by
  rw [interiorRatio, cosh_dist_basepoint, cosh_dist_basepoint]
  rfl

theorem interiorRatio_smul (hn : 1 ≤ n) (g : PO n 1) (o x y : HUpper n) :
    interiorRatio ((poMulAction hn).smul g o)
      ((poMulAction hn).smul g x) ((poMulAction hn).smul g y) = interiorRatio o x y := by
  have hd (u v : HUpper n) :
      dist ((poMulAction hn).smul g u) ((poMulAction hn).smul g v) = dist u v :=
    po_dist_smul hn g u v
  unfold interiorRatio
  rw [hd x y, hd o x, hd o y]

theorem gromovProduct_smul (hn : 1 ≤ n) (g : PO n 1) (o x y : HUpper n) :
    gromovProduct ((poMulAction hn).smul g o)
      ((poMulAction hn).smul g x) ((poMulAction hn).smul g y) = gromovProduct o x y := by
  have hd (u v : HUpper n) :
      dist ((poMulAction hn).smul g u) ((poMulAction hn).smul g v) = dist u v :=
    po_dist_smul hn g u v
  unfold gromovProduct
  rw [hd o x, hd o y, hd x y]

theorem interiorRatio_le (hn : 1 ≤ n) (o x y : HUpper n) :
    interiorRatio o x y ≤ 4 * Real.exp (-(2 * gromovProduct o x y)) := by
  let := poMulAction hn
  obtain ⟨g, hg⟩ := exists_po_smul_eq hn o basepointH
  have h := bratio_le (g • x) (g • y)
  change bratio ((poMulAction hn).smul g x) ((poMulAction hn).smul g y) ≤
    4 * Real.exp (-(2 * gromovProduct basepointH
      ((poMulAction hn).smul g x) ((poMulAction hn).smul g y))) at h
  rw [← interiorRatio_basepoint, ← hg, interiorRatio_smul hn g o x y,
    gromovProduct_smul hn g o x y] at h
  exact h

theorem half_exp_le_interiorRatio (hn : 1 ≤ n) (o x y : HUpper n) :
    Real.exp (-(2 * gromovProduct o x y)) / 2 ≤ interiorRatio o x y := by
  let := poMulAction hn
  obtain ⟨g, hg⟩ := exists_po_smul_eq hn o basepointH
  have h := half_exp_le_bratio (g • x) (g • y)
  change Real.exp (-(2 * gromovProduct basepointH
      ((poMulAction hn).smul g x) ((poMulAction hn).smul g y))) / 2 ≤
    bratio ((poMulAction hn).smul g x) ((poMulAction hn).smul g y) at h
  rw [← interiorRatio_basepoint, ← hg, interiorRatio_smul hn g o x y,
    gromovProduct_smul hn g o x y] at h
  exact h

theorem interiorRatio_eq_radial (o x y : HUpper n) :
    interiorRatio o x y =
      -lorB (radial x) (radial y) /
        ((-lorB o.val (radial x)) * (-lorB o.val (radial y))) := by
  have hx : lorB o.val x.val ≠ 0 := by
    have := HUpper.one_le_neg_lorB o x
    linarith
  have hy : lorB o.val y.val ≠ 0 := by
    have := HUpper.one_le_neg_lorB o y
    linarith
  simp only [interiorRatio, cosh_dist, radial, lorB_smul_left, lorB_smul_right]
  field_simp [x.future.ne', y.future.ne', hx, hy]

theorem tendsto_interiorRatio (o : HUpper n) {x y : ℕ → HUpper n}
    {a b : BoundaryH n} (hx : ConvergesToBoundary x a) (hy : ConvergesToBoundary y b) :
    Tendsto (fun k => interiorRatio o (x k) (y k)) atTop (nhds (ratio o a b)) := by
  have hxy : Tendsto (fun k => (radial (x k), radial (y k))) atTop (nhds (a.val, b.val)) := by
    rw [nhds_prod_eq]
    exact hx.prodMk hy
  have hox : Tendsto (fun k => (o.val, radial (x k))) atTop (nhds (o.val, a.val)) := by
    rw [nhds_prod_eq]
    exact tendsto_const_nhds.prodMk hx
  have hoy : Tendsto (fun k => (o.val, radial (y k))) atTop (nhds (o.val, b.val)) := by
    rw [nhds_prod_eq]
    exact tendsto_const_nhds.prodMk hy
  have hnum := ((continuous_lorB_pair.tendsto _).comp hxy).neg
  have hdenx := ((continuous_lorB_pair.tendsto _).comp hox).neg
  have hdeny := ((continuous_lorB_pair.tendsto _).comp hoy).neg
  have h := hnum.div (hdenx.mul hdeny) (mul_pos (height_pos o a) (height_pos o b)).ne'
  change Tendsto (fun k => -lorB (radial (x k)) (radial (y k)) /
    ((-lorB o.val (radial (x k))) * (-lorB o.val (radial (y k)))))
    atTop (nhds (ratio o a b)) at h
  simpa only [interiorRatio_eq_radial] using h

theorem ratio_smul (hn : 1 ≤ n) (g : PO n 1) (o : HUpper n) (a b : BoundaryH n) :
    ratio ((poMulAction hn).smul g o)
      ((poBoundaryMulAction hn).smul g a) ((poBoundaryMulAction hn).smul g b) = ratio o a b := by
  have ha := tendsto_rayTo (basepointH : HUpper n) a
  have hb := tendsto_rayTo (basepointH : HUpper n) b
  have h₁ := tendsto_interiorRatio ((poMulAction hn).smul g o)
    (convergesToBoundary_smul hn g ha) (convergesToBoundary_smul hn g hb)
  simp only [interiorRatio_smul] at h₁
  exact tendsto_nhds_unique h₁ (tendsto_interiorRatio o ha hb)

theorem bratioB_le_two (a b : BoundaryH n) : bratioB a b ≤ 2 := by
  have h := abs_sdot_le a.val b.val
  rw [sdot_self_of_boundary a, sdot_self_of_boundary b, Real.sqrt_one, mul_one] at h
  simp only [bratioB, lorB, a.tc_eq, b.tc_eq]
  linarith [(abs_le.mp h).1]

theorem ratio_le_two (hn : 1 ≤ n) (o : HUpper n) (a b : BoundaryH n) :
    ratio o a b ≤ 2 := by
  obtain ⟨g, hg⟩ := exists_po_smul_eq hn o basepointH
  rw [← ratio_smul hn g, hg, ratio_basepoint]
  exact bratioB_le_two _ _

theorem bratioB_triangle (a b c : BoundaryH n) :
    bratioB a c ≤ 2 * (bratioB a b + bratioB b c) := by
  have h := sdot_self_nonneg ((a.val - b.val) + (c.val - b.val))
  simp only [sdot_add_left, sdot_add_right, sdot_sub_left, sdot_sub_right,
    sdot_self_of_boundary, sdot_comm b.val a.val, sdot_comm c.val a.val,
    sdot_comm c.val b.val] at h
  simp only [bratioB, lorB, a.tc_eq, b.tc_eq, c.tc_eq]
  linarith

theorem ratio_triangle (hn : 1 ≤ n) (o : HUpper n) (a b c : BoundaryH n) :
    ratio o a c ≤ 2 * (ratio o a b + ratio o b c) := by
  obtain ⟨g, hg⟩ := exists_po_smul_eq hn o basepointH
  have h := bratioB_triangle ((poBoundaryMulAction hn).smul g a)
    ((poBoundaryMulAction hn).smul g b) ((poBoundaryMulAction hn).smul g c)
  simp only [← ratio_basepoint, ← hg, ratio_smul] at h
  exact h

theorem ratio_eq_exp (o : HUpper n) (a b : BoundaryH n) :
    ratio o a b = bratioB a b * Real.exp (-(busemann a o + busemann b o)) := by
  rw [Real.exp_neg, Real.exp_add]
  simp only [busemann, Real.exp_log (neg_lorB_upper_boundary_pos o _)]
  rfl

theorem ratio_change_basepoint (o p : HUpper n) (a b : BoundaryH n) :
    ratio o a b ≤ Real.exp (2 * dist o p) * ratio p a b := by
  have ha := (abs_le.mp (busemann_lipschitz a o p)).1
  have hb := (abs_le.mp (busemann_lipschitz b o p)).1
  have he : Real.exp (-(busemann a o + busemann b o)) ≤
      Real.exp (2 * dist o p) * Real.exp (-(busemann a p + busemann b p)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [ratio_eq_exp, ratio_eq_exp]
  calc bratioB a b * Real.exp (-(busemann a o + busemann b o))
      ≤ bratioB a b * (Real.exp (2 * dist o p) *
          Real.exp (-(busemann a p + busemann b p))) :=
        mul_le_mul_of_nonneg_left he (bratioB_nonneg a b)
    _ = _ := by ring

def crossRatioSq (a b c d : BoundaryH n) : ℝ :=
  bratioB a b * bratioB c d / (bratioB a c * bratioB b d)

theorem crossRatioSq_nonneg (a b c d : BoundaryH n) : 0 ≤ crossRatioSq a b c d :=
  div_nonneg (mul_nonneg (bratioB_nonneg a b) (bratioB_nonneg c d))
    (mul_nonneg (bratioB_nonneg a c) (bratioB_nonneg b d))

theorem crossRatioSq_eq_chordDist (a b c d : BoundaryH n)
    (hac : a ≠ c) (hbd : b ≠ d) :
    crossRatioSq a b c d =
      (chordDist a b * chordDist c d / (chordDist a c * chordDist b d)) ^ 2 := by
  rw [div_pow, mul_pow, mul_pow, chordDist_sq, chordDist_sq, chordDist_sq, chordDist_sq]
  unfold crossRatioSq
  field_simp [(bratioB_pos hac).ne', (bratioB_pos hbd).ne']

theorem crossRatioSq_eq_ratio (o : HUpper n) (a b c d : BoundaryH n)
    (hac : a ≠ c) (hbd : b ≠ d) :
    crossRatioSq a b c d = ratio o a b * ratio o c d / (ratio o a c * ratio o b d) := by
  simp only [crossRatioSq, ratio]
  field_simp [(height_pos o a).ne', (height_pos o b).ne',
    (height_pos o c).ne', (height_pos o d).ne', (bratioB_pos hac).ne',
    (bratioB_pos hbd).ne']

def tripleCenter (a b c : BoundaryH n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : HUpper n :=
  { val := (Real.sqrt (2 * bratioB a b * bratioB a c * bratioB b c))⁻¹ •
      (bratioB b c • a.val + bratioB a c • b.val)
    is_unit := by
      have hu := bratioB_pos hab
      have hv := bratioB_pos hac
      have hw := bratioB_pos hbc
      have hD : Real.sqrt (2 * bratioB a b * bratioB a c * bratioB b c) ≠ 0 :=
        (Real.sqrt_pos.mpr (by positivity)).ne'
      have hD2 := Real.sq_sqrt (by positivity : 0 ≤ 2 * bratioB a b * bratioB a c * bratioB b c)
      have hab' : lorB a.val b.val = -bratioB a b := by simp [bratioB]
      simp only [lorB_smul_left, lorB_smul_right, lorB_add_left, lorB_add_right,
        a.is_null, b.is_null, lorB_comm b.val a.val, hab']
      field_simp
      nlinarith [hD2]
    future := by
      have hu := bratioB_pos hab
      have hv := bratioB_pos hac
      have hw := bratioB_pos hbc
      simp only [tc_smul, tc_add, a.tc_eq, b.tc_eq, mul_one]
      positivity }

theorem tripleCenter_val (a b c : BoundaryH n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (tripleCenter a b c hab hac hbc).val =
      (Real.sqrt (2 * bratioB a b * bratioB a c * bratioB b c))⁻¹ •
        (bratioB b c • a.val + bratioB a c • b.val) := rfl

theorem exists_triple_center (a b c : BoundaryH n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ o : HUpper n, ratio o a b = 2 ∧ ratio o a c = 1 ∧ ratio o b c = 1 := by
  let u := bratioB a b
  let v := bratioB a c
  let w := bratioB b c
  have hu : 0 < u := bratioB_pos hab
  have hv : 0 < v := bratioB_pos hac
  have hw : 0 < w := bratioB_pos hbc
  let D := Real.sqrt (2 * u * v * w)
  have hD : 0 < D := Real.sqrt_pos.mpr (by positivity)
  have hD2 : D ^ 2 = 2 * u * v * w := Real.sq_sqrt (by positivity)
  have hab' : lorB a.val b.val = -u := by simp [u, bratioB]
  have hac' : lorB a.val c.val = -v := by simp [v, bratioB]
  have hbc' : lorB b.val c.val = -w := by simp [w, bratioB]
  let o : HUpper n := tripleCenter a b c hab hac hbc
  have hoa : height o a = D⁻¹ * (v * u) := by
    change -lorB (D⁻¹ • (w • a.val + v • b.val)) a.val = _
    rw [lorB_smul_left, lorB_add_left, lorB_smul_left, lorB_smul_left,
      a.is_null, lorB_comm b.val a.val, hab']
    ring
  have hob : height o b = D⁻¹ * (w * u) := by
    change -lorB (D⁻¹ • (w • a.val + v • b.val)) b.val = _
    rw [lorB_smul_left, lorB_add_left, lorB_smul_left, lorB_smul_left, b.is_null, hab']
    ring
  have hoc : height o c = D⁻¹ * (2 * v * w) := by
    change -lorB (D⁻¹ • (w • a.val + v • b.val)) c.val = _
    rw [lorB_smul_left, lorB_add_left, lorB_smul_left, lorB_smul_left, hac', hbc']
    ring
  refine ⟨o, ?_, ?_, ?_⟩
  · rw [ratio, hoa, hob]
    change u / (D⁻¹ * (v * u) * (D⁻¹ * (w * u))) = 2
    field_simp
    nlinarith [hD2]
  · rw [ratio, hoa, hoc]
    change v / (D⁻¹ * (v * u) * (D⁻¹ * (2 * v * w))) = 1
    field_simp
    nlinarith [hD2]
  · rw [ratio, hob, hoc]
    change w / (D⁻¹ * (w * u) * (D⁻¹ * (2 * v * w))) = 1
    field_simp
    nlinarith [hD2]

end DifferentialGeometry.BoundaryVisual

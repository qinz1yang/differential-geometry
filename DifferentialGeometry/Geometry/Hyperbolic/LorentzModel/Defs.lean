/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import Batteries.Data.BitVec.Lemmas
import DifferentialGeometry.Geometry.LieGroup.ProjectiveOrthogonal.Defs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Tactic.Ext

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.Hyperbolic

variable {n : ℕ}

abbrev LorVec (n : ℕ) : Type := Fin n ⊕ Fin 1 → ℝ

def sdot (x y : LorVec n) : ℝ := ∑ i : Fin n, x (Sum.inl i) * y (Sum.inl i)

def tc (x : LorVec n) : ℝ := x (Sum.inr 0)

def lorB (x y : LorVec n) : ℝ := sdot x y - tc x * tc y

theorem sdot_comm (x y : LorVec n) : sdot x y = sdot y x := by
  simp [sdot, mul_comm]

theorem sdot_self_nonneg (x : LorVec n) : 0 ≤ sdot x x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x (Sum.inl i))

theorem sdot_add_left (x y z : LorVec n) : sdot (x + y) z = sdot x z + sdot y z := by
  simp [sdot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem sdot_smul_left (c : ℝ) (x y : LorVec n) : sdot (c • x) y = c * sdot x y := by
  simp only [sdot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sdot_neg_left (x y : LorVec n) : sdot (-x) y = -sdot x y := by
  simp [sdot, Pi.neg_apply, Finset.sum_neg_distrib, neg_mul]

theorem sdot_sub_left (x y z : LorVec n) : sdot (x - y) z = sdot x z - sdot y z := by
  rw [sub_eq_add_neg, sdot_add_left, sdot_neg_left, sub_eq_add_neg]

theorem sdot_sub_right (x y z : LorVec n) : sdot x (y - z) = sdot x y - sdot x z := by
  rw [sdot_comm, sdot_sub_left, sdot_comm y x, sdot_comm z x, sub_eq_add_neg]

theorem sdot_add_right (x y z : LorVec n) : sdot x (y + z) = sdot x y + sdot x z := by
  rw [sdot_comm, sdot_add_left, sdot_comm y x, sdot_comm z x]

theorem sdot_smul_right (c : ℝ) (x y : LorVec n) : sdot x (c • y) = c * sdot x y := by
  rw [sdot_comm, sdot_smul_left, sdot_comm y x]

theorem tc_add (x y : LorVec n) : tc (x + y) = tc x + tc y := rfl

theorem tc_smul (c : ℝ) (x : LorVec n) : tc (c • x) = c * tc x := rfl

theorem tc_neg (x : LorVec n) : tc (-x) = -tc x := rfl

theorem lorB_comm (x y : LorVec n) : lorB x y = lorB y x := by
  simp [lorB, sdot_comm, tc, mul_comm]

theorem lorB_add_left (x y z : LorVec n) : lorB (x + y) z = lorB x z + lorB y z := by
  simp [lorB, sdot_add_left, tc_add]; ring

theorem lorB_smul_left (c : ℝ) (x y : LorVec n) : lorB (c • x) y = c * lorB x y := by
  simp [lorB, sdot_smul_left, tc_smul]; ring

theorem lorB_add_right (x y z : LorVec n) : lorB x (y + z) = lorB x y + lorB x z := by
  rw [lorB_comm, lorB_add_left, lorB_comm y x, lorB_comm z x]

theorem lorB_smul_right (c : ℝ) (x y : LorVec n) : lorB x (c • y) = c * lorB x y := by
  rw [lorB_comm, lorB_smul_left, lorB_comm y x]

theorem lorB_neg_left (x y : LorVec n) : lorB (-x) y = -lorB x y := by
  simp only [lorB, sdot_neg_left, tc_neg]; ring

theorem lorB_neg_right (x y : LorVec n) : lorB x (-y) = -lorB x y := by
  rw [lorB_comm, lorB_neg_left, lorB_comm y x]

theorem lorB_sub_left (x y z : LorVec n) : lorB (x - y) z = lorB x z - lorB y z := by
  rw [sub_eq_add_neg, lorB_add_left, lorB_neg_left, sub_eq_add_neg]

theorem lorB_sub_right (x y z : LorVec n) : lorB x (y - z) = lorB x y - lorB x z := by
  rw [lorB_comm, lorB_sub_left, lorB_comm y x, lorB_comm z x, sub_eq_add_neg]

theorem sdot_sq_le (x y : LorVec n) : sdot x y ^ 2 ≤ sdot x x * sdot y y := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
    (fun i => x (Sum.inl i)) (fun i => y (Sum.inl i))
  have e : (∑ i : Fin n, x (Sum.inl i) ^ 2) = sdot x x := by
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_two]
  have e' : (∑ i : Fin n, y (Sum.inl i) ^ 2) = sdot y y := by
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_two]
  rw [e, e'] at h
  exact h

theorem abs_sdot_le (x y : LorVec n) :
    |sdot x y| ≤ Real.sqrt (sdot x x) * Real.sqrt (sdot y y) := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sdot_self_nonneg x)]
  exact Real.sqrt_le_sqrt (sdot_sq_le x y)

theorem lorB_self_nonneg_of_orth {y : LorVec n} (hy : lorB y y = -1) {v : LorVec n}
    (hv : lorB v y = 0) : 0 ≤ lorB v v := by
  have hty : tc y ≠ 0 := by
    intro h
    have h0 := hy
    simp only [lorB, h, mul_zero, sub_zero] at h0
    have := sdot_self_nonneg y
    linarith
  have htv : tc v * tc y = sdot v y := by
    have h0 := hv
    simp only [lorB, sub_eq_zero] at h0
    linarith
  have hyy : sdot y y = tc y * tc y - 1 := by
    have h0 := hy
    simp only [lorB] at h0
    linarith
  have hcs := sdot_sq_le v y
  have hpos : (0:ℝ) < tc y * tc y := mul_self_pos.mpr hty
  have key : (sdot v y) ^ 2 ≤ sdot v v * (tc y * tc y) := by
    calc (sdot v y)^2 ≤ sdot v v * sdot y y := hcs
      _ = sdot v v * (tc y * tc y) - sdot v v := by rw [hyy]; ring
      _ ≤ sdot v v * (tc y * tc y) := by nlinarith [sdot_self_nonneg v]
  have hmul : (tc v * tc v) * (tc y * tc y) ≤ sdot v v * (tc y * tc y) := by
    have htv2 : (tc v * tc v) * (tc y * tc y) = (sdot v y) ^ 2 := by
      have h2 : (tc v * tc y)^2 = (sdot v y)^2 := by rw [← htv]
      rw [← h2]; ring
    rw [htv2]; exact key
  have hfinal : tc v * tc v ≤ sdot v v := le_of_mul_le_mul_right hmul hpos
  have h2 : lorB v v = sdot v v - tc v * tc v := rfl
  rw [h2]
  linarith [hfinal]

theorem lorB_add_smul_self (u v : LorVec n) (t : ℝ) :
    lorB (u + t • v) (u + t • v) = lorB u u + 2 * t * lorB u v + t ^ 2 * lorB v v := by
  have hcomm : lorB v u = lorB u v := lorB_comm v u
  simp only [lorB_add_left, lorB_add_right, lorB_smul_left, lorB_smul_right]
  rw [hcomm]
  ring

theorem lorB_sub_smul_self (u v : LorVec n) (t : ℝ) :
    lorB (u - t • v) (u - t • v) = lorB u u - 2 * t * lorB u v + t ^ 2 * lorB v v := by
  have h : u - t • v = u + (-t) • v := by rw [neg_smul, sub_eq_add_neg]
  rw [h, lorB_add_smul_self]
  ring

theorem lorB_sq_le_of_orth {y : LorVec n} (hy : lorB y y = -1) {u v : LorVec n}
    (hu : lorB u y = 0) (hv : lorB v y = 0) :
    lorB u v ^ 2 ≤ lorB u u * lorB v v := by
  have hA : 0 ≤ lorB u u := lorB_self_nonneg_of_orth hy hu
  have hC : 0 ≤ lorB v v := lorB_self_nonneg_of_orth hy hv
  set A := lorB u u with hAd
  set B := lorB u v with hBd
  set C := lorB v v with hCd
  have hquad : ∀ t : ℝ, 0 ≤ A + 2 * t * B + t ^ 2 * C := fun t => by
    have horth : lorB (u + t • v) y = 0 := by
      rw [lorB_add_left, lorB_smul_left, hu, hv, mul_zero, add_zero]
    have h0 := lorB_self_nonneg_of_orth hy horth
    rw [lorB_add_smul_self] at h0
    exact h0
  by_cases hCz : C = 0
  · have hB0 : B = 0 := by
      by_contra hB0
      have h1 := hquad (-(A + 1) / (2 * B))
      rw [hCz] at h1
      simp only [mul_zero, add_zero] at h1
      have h2 : 2 * (-(A + 1) / (2 * B)) * B = -(A + 1) := by
        field_simp
      rw [h2] at h1
      nlinarith [h1]
    rw [hB0, hCz]; simp
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCz)
    have h1 := hquad (-B / C)
    have e : A + 2 * (-B / C) * B + (-B / C) ^ 2 * C = A - B^2 / C := by
      field_simp
      ring
    rw [e] at h1
    have h2 : (A - B^2 / C) * C ≥ 0 := mul_nonneg h1 (le_of_lt hCpos)
    have h3 : (A - B^2 / C) * C = A * C - B^2 := by
      field_simp
    rw [h3] at h2
    linarith

theorem two_sqrt_mul_le_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt (a * b) ≤ a + b := by
  have hs : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha b
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb, hs]

theorem one_add_sqrt_mul_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 + Real.sqrt (a * b) ≤ Real.sqrt ((1 + a) * (1 + b)) := by
  have hx : (0:ℝ) ≤ 1 + Real.sqrt (a * b) := by positivity
  have hy : (0:ℝ) ≤ (1 + a) * (1 + b) := by positivity
  rw [Real.le_sqrt hx hy]
  have h := two_sqrt_mul_le_add a b ha hb
  have hs : (Real.sqrt (a * b))^2 = a * b := Real.sq_sqrt (by positivity)
  nlinarith [h, hs, Real.sqrt_nonneg (a * b)]

@[ext]
structure HUpper (n : ℕ) where
  val : LorVec n
  is_unit : lorB val val = -1
  future : 0 < tc val

namespace HUpper

theorem tc_sq (x : HUpper n) : tc x.val ^ 2 = 1 + sdot x.val x.val := by
  have h := x.is_unit
  simp only [lorB] at h
  have hs : tc x.val * tc x.val = 1 + sdot x.val x.val := by linarith
  rw [pow_two]
  exact hs

theorem one_le_tc (x : HUpper n) : 1 ≤ tc x.val := by
  have h1 := tc_sq x
  have h2 : 0 < tc x.val := x.future
  nlinarith [sdot_self_nonneg x.val, h1, h2]

theorem one_le_neg_lorB (x y : HUpper n) : 1 ≤ - lorB x.val y.val := by
  set sx := sdot x.val x.val with hsxd
  set sy := sdot y.val y.val with hsyd
  have hsx : 0 ≤ sx := sdot_self_nonneg _
  have hsy : 0 ≤ sy := sdot_self_nonneg _
  have htx : 0 < tc x.val := x.future
  have hty : 0 < tc y.val := y.future
  have hx2 : tc x.val ^ 2 = 1 + sx := tc_sq x
  have hy2 : tc y.val ^ 2 = 1 + sy := tc_sq y
  have hprod : tc x.val * tc y.val = Real.sqrt ((1 + sx) * (1 + sy)) := by
    have hpos : 0 ≤ tc x.val * tc y.val := by positivity
    have hsq : (tc x.val * tc y.val) ^ 2 = (1 + sx) * (1 + sy) := by
      rw [mul_pow, hx2, hy2]
    rw [← hsq]
    exact (Real.sqrt_sq hpos).symm
  have hsd : sdot x.val y.val ≤ Real.sqrt (sx * sy) := by
    have h := abs_sdot_le x.val y.val
    rw [← Real.sqrt_mul hsx] at h
    exact (le_abs_self _).trans h
  have hmain : 1 + Real.sqrt (sx * sy) ≤ tc x.val * tc y.val := by
    rw [hprod]
    exact one_add_sqrt_mul_le sx sy hsx hsy
  have heq : - lorB x.val y.val = tc x.val * tc y.val - sdot x.val y.val := by
    simp only [lorB]; ring
  rw [heq]
  linarith [hmain, hsd]

theorem inl_eq_zero_of_sdot_self_eq_zero {w : LorVec n} (h : sdot w w = 0) (i : Fin n) :
    w (Sum.inl i) = 0 := by
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ w (Sum.inl j) * w (Sum.inl j) :=
    fun j _ => mul_self_nonneg _
  have hsum : ∑ j : Fin n, w (Sum.inl j) * w (Sum.inl j) = 0 := h
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at hsum
  have hi := hsum i (Finset.mem_univ i)
  have hi2 : w (Sum.inl i) ^ 2 = 0 := by rw [pow_two]; exact hi
  exact sq_eq_zero_iff.mp hi2

theorem eq_of_neg_lorB_eq_one {x y : HUpper n} (h : -lorB x.val y.val = 1) : x = y := by
  set sx := sdot x.val x.val with hsxd
  set sy := sdot y.val y.val with hsyd
  have hsx : 0 ≤ sx := sdot_self_nonneg _
  have hsy : 0 ≤ sy := sdot_self_nonneg _
  have htx : 0 < tc x.val := x.future
  have hty : 0 < tc y.val := y.future
  have hx2 : tc x.val ^ 2 = 1 + sx := tc_sq x
  have hy2 : tc y.val ^ 2 = 1 + sy := tc_sq y
  have hprod : tc x.val * tc y.val = Real.sqrt ((1 + sx) * (1 + sy)) := by
    have hpos : 0 ≤ tc x.val * tc y.val := by positivity
    have hsq : (tc x.val * tc y.val) ^ 2 = (1 + sx) * (1 + sy) := by
      rw [mul_pow, hx2, hy2]
    rw [← hsq]
    exact (Real.sqrt_sq hpos).symm
  have heq : tc x.val * tc y.val - sdot x.val y.val = 1 := by
    have h0 := h
    simp only [lorB] at h0
    linarith
  have hsd : sdot x.val y.val ≤ Real.sqrt (sx * sy) := by
    have hh := abs_sdot_le x.val y.val
    rw [← Real.sqrt_mul hsx] at hh
    exact (le_abs_self _).trans hh
  have hmain : 1 + Real.sqrt (sx * sy) ≤ tc x.val * tc y.val := by
    rw [hprod]
    exact one_add_sqrt_mul_le sx sy hsx hsy
  have hsd_eq : sdot x.val y.val = Real.sqrt (sx * sy) := by linarith
  have htc_eq : tc x.val * tc y.val = 1 + Real.sqrt (sx * sy) := by linarith
  have hsx_sy : sx = sy := by
    have hstep : sx + sy = 2 * Real.sqrt (sx * sy) := by
      have hsq : (tc x.val * tc y.val) ^ 2 = (1 + Real.sqrt (sx * sy)) ^ 2 := by
        rw [htc_eq]
      have hsq2 : (tc x.val * tc y.val) ^ 2 = (1 + sx) * (1 + sy) := by
        rw [mul_pow, hx2, hy2]
      have hsrs : (Real.sqrt (sx * sy)) ^ 2 = sx * sy := Real.sq_sqrt (by positivity)
      nlinarith [hsq, hsq2, hsrs, Real.sqrt_nonneg (sx * sy)]
    have hs : Real.sqrt (sx * sy) = Real.sqrt sx * Real.sqrt sy := Real.sqrt_mul hsx sy
    have hdiff : (Real.sqrt sx - Real.sqrt sy) ^ 2 = 0 := by
      have e : (Real.sqrt sx - Real.sqrt sy) ^ 2
          = sx + sy - 2 * (Real.sqrt sx * Real.sqrt sy) := by
        rw [sub_sq, Real.sq_sqrt hsx, Real.sq_sqrt hsy]; ring
      rw [e, ← hs]
      linarith [hstep]
    have h00 : Real.sqrt sx - Real.sqrt sy = 0 := sq_eq_zero_iff.mp hdiff
    have h01 : Real.sqrt sx = Real.sqrt sy := sub_eq_zero.mp h00
    have h02 : (Real.sqrt sx) ^ 2 = (Real.sqrt sy) ^ 2 := by rw [h01]
    rw [Real.sq_sqrt hsx, Real.sq_sqrt hsy] at h02
    exact h02
  have hxy : sdot x.val y.val = sx := by
    rw [hsd_eq, ← hsx_sy]
    exact Real.sqrt_mul_self hsx
  have hspat : sdot (x.val - y.val) (x.val - y.val) = 0 := by
    have hyx : sdot y.val x.val = sx := by rw [sdot_comm]; exact hxy
    have hyy2 : sdot y.val y.val = sx := by rw [← hsyd]; exact hsx_sy.symm
    rw [sdot_sub_left, sdot_sub_right, sdot_sub_right]
    rw [show sdot x.val x.val = sx from rfl, hxy, hyx, hyy2]
    ring
  have hcoord : ∀ i : Fin n, x.val (Sum.inl i) = y.val (Sum.inl i) := by
    intro i
    have hi := inl_eq_zero_of_sdot_self_eq_zero hspat i
    have : x.val (Sum.inl i) - y.val (Sum.inl i) = 0 := by
      have := hi
      simpa [Pi.sub_apply] using this
    linarith
  have htc : tc x.val = tc y.val := by
    have hsq : tc x.val ^ 2 = tc y.val ^ 2 := by rw [hx2, hy2, hsx_sy]
    have hnonnegx : 0 ≤ tc x.val := le_of_lt htx
    have hnonnegy : 0 ≤ tc y.val := le_of_lt hty
    have := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
    rcases this with h' | h'
    · exact h'
    · linarith
  apply HUpper.ext
  funext a
  rcases a with a | a
  · exact hcoord a
  · have : a = 0 := Subsingleton.elim a 0
    subst this
    exact htc

noncomputable def hdist (x y : HUpper n) : ℝ := Real.arcosh (- lorB x.val y.val)

theorem hdist_triangle (x y z : HUpper n) :
    hdist x z ≤ hdist x y + hdist y z := by
  have hyy : lorB y.val y.val = -1 := y.is_unit
  have hxx : lorB x.val x.val = -1 := x.is_unit
  have hzz : lorB z.val z.val = -1 := z.is_unit
  set a := - lorB x.val y.val with had
  set b := - lorB y.val z.val with hbd
  set c := - lorB x.val z.val with hcd
  have ha : 1 ≤ a := one_le_neg_lorB x y
  have hb : 1 ≤ b := one_le_neg_lorB y z
  have hc : 1 ≤ c := one_le_neg_lorB x z
  set xp : LorVec n := x.val - a • y.val with hxpd
  set zp : LorVec n := z.val - b • y.val with hzpd
  have hxy : lorB x.val y.val = -a := by rw [had]; ring
  have hyz : lorB y.val z.val = -b := by rw [hbd]; ring
  have hxp_orth : lorB xp y.val = 0 := by
    rw [hxpd, lorB_sub_left, lorB_smul_left, hyy, hxy]; ring
  have hzp_orth : lorB zp y.val = 0 := by
    rw [hzpd, lorB_sub_left, lorB_smul_left, hyy, lorB_comm z.val y.val, hyz]; ring
  have hxp_sq : lorB xp xp = a ^ 2 - 1 := by
    rw [hxpd, lorB_sub_smul_self, hxx, hxy, hyy]; ring
  have hzp_sq : lorB zp zp = b ^ 2 - 1 := by
    rw [hzpd, lorB_sub_smul_self, hzz, lorB_comm z.val y.val, hyz, hyy]; ring
  have hx_eq : x.val = xp + a • y.val := by rw [hxpd]; abel
  have hz_eq : z.val = zp + b • y.val := by rw [hzpd]; abel
  have hxz2 : lorB x.val z.val = lorB xp zp - a * b := by
    rw [hx_eq, hz_eq]
    simp only [lorB_add_left, lorB_add_right, lorB_smul_left, lorB_smul_right]
    rw [hxp_orth, show lorB y.val zp = 0 from by rw [lorB_comm y.val zp]; exact hzp_orth, hyy]
    ring
  have hc_eq : c = a * b - lorB xp zp := by rw [hcd, hxz2]; ring
  have hcs : lorB xp zp ^ 2 ≤ (a^2 - 1) * (b^2 - 1) := by
    have h := lorB_sq_le_of_orth hyy hxp_orth hzp_orth
    rw [hxp_sq, hzp_sq] at h
    exact h
  have hub : c ≤ a * b + Real.sqrt ((a^2 - 1) * (b^2 - 1)) := by
    have h1 : - lorB xp zp ≤ |lorB xp zp| := neg_le_abs _
    have h2 : |lorB xp zp| ≤ Real.sqrt ((a^2-1)*(b^2-1)) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hcs
    rw [hc_eq]
    linarith [h1, h2]
  have ha1 : (0:ℝ) ≤ a^2 - 1 := by nlinarith [ha]
  have hcosh : Real.cosh (Real.arcosh a + Real.arcosh b)
      = a * b + Real.sqrt ((a^2 - 1) * (b^2 - 1)) := by
    rw [Real.cosh_add, Real.cosh_arcosh ha, Real.cosh_arcosh hb,
      Real.sinh_arcosh ha, Real.sinh_arcosh hb, ← Real.sqrt_mul ha1]
  have hc0 : 0 ≤ Real.arcosh c := Real.arcosh_nonneg hc
  have harg : 0 ≤ Real.arcosh a + Real.arcosh b :=
    add_nonneg (Real.arcosh_nonneg ha) (Real.arcosh_nonneg hb)
  have hfinal : Real.arcosh c ≤ Real.arcosh a + Real.arcosh b := by
    rw [← Real.cosh_strictMonoOn.le_iff_le hc0 harg, Real.cosh_arcosh hc, hcosh]
    exact hub
  exact hfinal

noncomputable instance : MetricSpace (HUpper n) where
  dist x y := hdist x y
  dist_self x := by
    have h : lorB x.val x.val = -1 := x.is_unit
    simp [hdist, h]
  dist_comm x y := by simp [hdist, lorB_comm]
  dist_triangle x y z := hdist_triangle x y z
  eq_of_dist_eq_zero {x y} h := by
    have h1 : 1 ≤ - lorB x.val y.val := one_le_neg_lorB x y
    have h2 : - lorB x.val y.val = 1 := by
      have h0 : Real.arcosh (- lorB x.val y.val) = 0 := h
      exact (Real.arcosh_eq_zero_iff h1).mp h0
    exact eq_of_neg_lorB_eq_one h2

end HUpper

end DifferentialGeometry.Hyperbolic

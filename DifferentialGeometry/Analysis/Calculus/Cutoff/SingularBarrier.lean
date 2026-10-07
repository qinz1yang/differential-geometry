import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis.SingularBarrier

/-! A fixed scalar barrier, flat through `1 / 20` and singular at `1 / 10`.
The cutoff is chosen independently of every geometric parameter. -/

private theorem hasDerivAt_max_pow (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (max y 0) ^ n)
      ((n : ℝ) * (max x 0) ^ (n - 1)) x := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n - 1 ≠ 0 := by omega
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have he : (fun y : ℝ => (max y 0) ^ n) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      change y < 0 at hy
      simp only [max_eq_right hy.le, zero_pow hn0]
    simpa only [max_eq_right hx.le, zero_pow hn1, mul_zero] using
      (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he
  · have hL : HasDerivWithinAt (fun y : ℝ => (max y 0) ^ n) 0 (Iic 0) 0 := by
      apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
      · intro y hy
        change y ≤ 0 at hy
        simp only [max_eq_right hy, zero_pow hn0]
      · simp only [max_self, zero_pow hn0]
    have hR : HasDerivWithinAt (fun y : ℝ => (max y 0) ^ n) 0 (Ici 0) 0 := by
      have hp : HasDerivAt (fun y : ℝ => y ^ n) 0 0 := by
        simpa only [id_eq, zero_pow hn1, mul_zero, zero_mul] using
          (hasDerivAt_id (0 : ℝ)).fun_pow n
      apply hp.hasDerivWithinAt.congr
      · intro y hy
        change 0 ≤ y at hy
        rw [max_eq_left hy]
      · simp only [max_self]
    have h := hL.union hR
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at h
    simpa only [max_self, zero_pow hn1, mul_zero] using h
  · have he : (fun y : ℝ => (max y 0) ^ n) =ᶠ[𝓝 x] fun y => y ^ n := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      change 0 < y at hy
      rw [max_eq_left hy.le]
    simpa only [max_eq_left hx.le, id_eq, mul_one] using
      ((hasDerivAt_id x).fun_pow n).congr_of_eventuallyEq he

private theorem contDiff_max_fourth :
    ContDiff ℝ 2 (fun x : ℝ => (max x 0) ^ 4) := by
  have h4 : deriv (fun x : ℝ => (max x 0) ^ 4) =
      fun x => 4 * (max x 0) ^ 3 := by
    funext x
    simpa using (hasDerivAt_max_pow 4 (by norm_num) x).deriv
  have h3 : deriv (fun x : ℝ => (max x 0) ^ 3) =
      fun x => 3 * (max x 0) ^ 2 := by
    funext x
    simpa using (hasDerivAt_max_pow 3 (by norm_num) x).deriv
  change ContDiff ℝ (1 + 1) (fun x : ℝ => (max x 0) ^ 4)
  refine contDiff_succ_iff_deriv.mpr ⟨fun x =>
    (hasDerivAt_max_pow 4 (by norm_num) x).differentiableAt, by simp, ?_⟩
  rw [h4]
  apply contDiff_const.mul
  refine contDiff_one_iff_deriv.mpr ⟨fun x =>
    (hasDerivAt_max_pow 3 (by norm_num) x).differentiableAt, ?_⟩
  rw [h3]
  exact continuous_const.mul ((continuous_id.max continuous_const).pow 2)

private def part (u : ℝ) : ℝ := max (20 * u - 1) 0

private def denominator (u : ℝ) : ℝ := 1 - part u ^ 4

/-- The universal scalar cutoff; its asserted domain is `u < 1 / 10`. -/
def value (u : ℝ) : ℝ := (denominator u ^ 4)⁻¹

/-- A uniform differential-barrier constant depending only on the drift bound. -/
def bound (D : ℝ) : ℝ := 76800 + 640 * D + D ^ 2

private theorem part_mem {u : ℝ} (hu : u < 1 / 10) : part u ∈ Ico 0 1 := by
  refine ⟨le_max_right _ _, max_lt (by linarith) (by norm_num)⟩

private theorem denominator_pos {u : ℝ} (hu : u < 1 / 10) : 0 < denominator u := by
  exact sub_pos.mpr (pow_lt_one₀ (part_mem hu).1 (part_mem hu).2 (by decide))

private theorem denominator_le_one (u : ℝ) : denominator u ≤ 1 := by
  have hp : 0 ≤ part u := le_max_right _ _
  dsimp only [denominator]
  exact sub_le_self _ (pow_nonneg hp _)

private theorem contDiff_denominator : ContDiff ℝ 2 denominator := by
  exact contDiff_const.sub (contDiff_max_fourth.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const))

/-- The barrier is twice continuously differentiable on its entire open domain,
including the junction where it leaves its constant plateau. -/
theorem contDiffOn : ContDiffOn ℝ 2 value (Iio (1 / 10)) := by
  exact (contDiff_denominator.pow 4).contDiffOn.inv fun u hu =>
    (pow_pos (denominator_pos hu) 4).ne'

theorem one_le {u : ℝ} (hu : u < 1 / 10) : 1 ≤ value u := by
  exact (one_le_inv₀ (pow_pos (denominator_pos hu) 4)).mpr
    (pow_le_one₀ (denominator_pos hu).le (denominator_le_one u))

theorem pos {u : ℝ} (hu : u < 1 / 10) : 0 < value u :=
  lt_of_lt_of_le zero_lt_one (one_le hu)

/-- The barrier is nondecreasing, with the same fixed plateau and pole. -/
theorem monotoneOn : MonotoneOn value (Iio (1 / 10)) := by
  intro a ha b hb hab
  have hp : part a ≤ part b := max_le_max (by linarith) le_rfl
  have hd : denominator b ≤ denominator a :=
    sub_le_sub_left (pow_le_pow_left₀ (part_mem ha).1 hp 4) 1
  exact (inv_le_inv₀ (pow_pos (denominator_pos ha) 4)
    (pow_pos (denominator_pos hb) 4)).mpr
      (pow_le_pow_left₀ (denominator_pos hb).le hd 4)

private theorem part_eq_zero {u : ℝ} (hu : u ≤ 1 / 20) : part u = 0 := by
  exact max_eq_right (by linarith)

theorem one_of_le {u : ℝ} (hu : u ≤ 1 / 20) : value u = 1 := by
  simp only [value, denominator, part_eq_zero hu]
  norm_num

private theorem hasDerivAt_part_cube (u : ℝ) :
    HasDerivAt (fun v => part v ^ 3) (60 * part u ^ 2) u := by
  have hlin : HasDerivAt (fun v : ℝ => 20 * v - 1) 20 u :=
    (hasDerivAt_const_mul (x := u) (20 : ℝ)).sub_const 1
  have h : HasDerivAt (fun v : ℝ => (max (20 * v - 1) 0) ^ 3)
      (3 * (max (20 * u - 1) 0) ^ 2 * 20) u := by
    simpa only [Function.comp_def, Nat.cast_ofNat, Nat.reduceSub] using
      (hasDerivAt_max_pow 3 (by norm_num) (20 * u - 1)).comp u hlin
  exact h.congr_deriv (by dsimp only [part]; ring)

private theorem hasDerivAt_denominator (u : ℝ) :
    HasDerivAt denominator (-80 * part u ^ 3) u := by
  have hlin : HasDerivAt (fun v : ℝ => 20 * v - 1) 20 u :=
    (hasDerivAt_const_mul (x := u) (20 : ℝ)).sub_const 1
  have h : HasDerivAt (fun v : ℝ => (max (20 * v - 1) 0) ^ 4)
      (4 * (max (20 * u - 1) 0) ^ 3 * 20) u := by
    simpa only [Function.comp_def, Nat.cast_ofNat, Nat.reduceSub] using
      (hasDerivAt_max_pow 4 (by norm_num) (20 * u - 1)).comp u hlin
  exact HasDerivAt.congr_deriv (HasDerivAt.const_sub (1 : ℝ) h)
    (by dsimp only [part]; ring)

private theorem hasDerivAt_value {u : ℝ} (hu : u < 1 / 10) :
    HasDerivAt value (320 * part u ^ 3 / denominator u ^ 5) u := by
  have hq := denominator_pos hu
  apply (((hasDerivAt_denominator u).fun_pow 4).inv
    (pow_ne_zero 4 hq.ne')).congr_deriv
  change -(4 * denominator u ^ 3 * (-80 * part u ^ 3)) / (denominator u ^ 4) ^ 2 =
    320 * part u ^ 3 / denominator u ^ 5
  field_simp [hq.ne']
  ring

private theorem deriv_value {u : ℝ} (hu : u < 1 / 10) :
    deriv value u = 320 * part u ^ 3 / denominator u ^ 5 :=
  (hasDerivAt_value hu).deriv

private theorem hasDerivAt_deriv_value {u : ℝ} (hu : u < 1 / 10) :
    HasDerivAt (deriv value)
      (6400 * part u ^ 2 * (3 + 17 * part u ^ 4) / denominator u ^ 6) u := by
  have hq := denominator_pos hu
  have h := ((hasDerivAt_part_cube u).const_mul 320).div
    ((hasDerivAt_denominator u).fun_pow 5) (pow_ne_zero 5 hq.ne')
  have he : deriv value =ᶠ[𝓝 u] fun v => 320 * part v ^ 3 / denominator v ^ 5 := by
    filter_upwards [Iio_mem_nhds hu] with v hv
    exact deriv_value hv
  apply (h.congr_deriv ?_).congr_of_eventuallyEq he
  change (320 * (60 * part u ^ 2) * denominator u ^ 5 -
      320 * part u ^ 3 * (5 * denominator u ^ 4 * (-80 * part u ^ 3))) /
      (denominator u ^ 5) ^ 2 =
    6400 * part u ^ 2 * (3 + 17 * part u ^ 4) / denominator u ^ 6
  field_simp [hq.ne']
  dsimp only [denominator]
  ring

private theorem deriv2_value {u : ℝ} (hu : u < 1 / 10) :
    deriv (deriv value) u =
      6400 * part u ^ 2 * (3 + 17 * part u ^ 4) / denominator u ^ 6 :=
  (hasDerivAt_deriv_value hu).deriv

theorem deriv_nonneg {u : ℝ} (hu : u < 1 / 10) : 0 ≤ deriv value u := by
  rw [deriv_value hu]
  exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg (part_mem hu).1 3))
    (pow_pos (denominator_pos hu) 5).le

theorem deriv_pos {u : ℝ} (hlo : 1 / 20 < u) (hu : u < 1 / 10) :
    0 < deriv value u := by
  have hp : 0 < part u := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  rw [deriv_value hu]
  exact div_pos (mul_pos (by norm_num) (pow_pos hp 3)) (pow_pos (denominator_pos hu) 5)

theorem deriv_zero_of_le {u : ℝ} (hu : u ≤ 1 / 20) : deriv value u = 0 := by
  rw [deriv_value (by linarith), part_eq_zero hu]
  norm_num

theorem deriv2_zero_of_le {u : ℝ} (hu : u ≤ 1 / 20) : deriv (deriv value) u = 0 := by
  rw [deriv2_value (by linarith), part_eq_zero hu]
  norm_num

/-- This is a scalar identity only; at the junction it does not assert smooth
composition with an arbitrary nonsmooth spatial distance function. -/
theorem deriv2_zero_of_deriv_zero {u : ℝ} (hu : u < 1 / 10)
    (hzero : deriv value u = 0) : deriv (deriv value) u = 0 := by
  apply deriv2_zero_of_le
  by_contra hlo
  exact (ne_of_gt (deriv_pos (lt_of_not_ge hlo) hu)) hzero

/-- Approaching the pole from below forces the barrier to infinity. -/
theorem tendsto_at_pole : Tendsto value (𝓝[<] (1 / 10)) atTop := by
  have hz : denominator (1 / 10) ^ 4 = 0 := by
    norm_num [denominator, part]
  have hc : Continuous (fun u : ℝ => denominator u ^ 4) :=
    (contDiff_denominator.pow 4).continuous
  have ht : Tendsto (fun u : ℝ => denominator u ^ 4) (𝓝[<] (1 / 10)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [hz] using (hc.tendsto (1 / 10)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact pow_pos (denominator_pos hu) 4
  exact tendsto_inv_nhdsGT_zero.comp ht

theorem bound_nonneg {D : ℝ} (hD : 0 ≤ D) : 0 ≤ bound D := by
  exact add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hD)) (sq_nonneg D)

/-- The scalar polynomial used by the reciprocal singular cutoff is nonnegative
for every drift coefficient `D ≥ 0` and every `x ∈ [0, 1]`. -/
private theorem polynomial_nonneg (D x : ℝ) (hD : 0 ≤ D)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ 19200 * x ^ 2 * (5 * x ^ 4 - 1)
      - 320 * D * x ^ 3 * (1 - x ^ 4)
      + (76800 + 640 * D + D ^ 2) * (1 - x ^ 4) ^ 2 := by
  let q : ℝ := 1 - x ^ 4
  change 0 ≤ 19200 * x ^ 2 * (5 * x ^ 4 - 1)
    - 320 * D * x ^ 3 * q + (76800 + 640 * D + D ^ 2) * q ^ 2
  by_cases hsmall : x ^ 4 ≤ (1 / 2 : ℝ)
  · have hq : (1 / 2 : ℝ) ≤ q := by
      dsimp [q]
      linarith only [hsmall]
    have hq0 : 0 ≤ q := by linarith only [hq]
    have hx_sq : 0 ≤ 1 - x ^ 2 := by
      calc
        0 ≤ (1 - x) * (1 + x) :=
          mul_nonneg (sub_nonneg.mpr hx1) (by linarith only [hx0])
        _ = 1 - x ^ 2 := by ring
    have hx_sq_le : x ^ 2 ≤ 1 := by linarith only [hx_sq]
    have hx_cube_le : x ^ 3 ≤ 1 := by
      calc
        x ^ 3 = x ^ 2 * x := by ring
        _ ≤ 1 * x := mul_le_mul_of_nonneg_right hx_sq_le hx0
        _ ≤ 1 := by simpa using hx1
    have hq_sub : 0 ≤ 2 * q - 1 := by linarith only [hq]
    have hq_add : 0 ≤ 2 * q + 1 := by linarith only [hq]
    have hq_cube : 0 ≤ 2 * q - x ^ 3 := by
      linarith only [hq, hx_cube_le]
    calc
      0 ≤ 96000 * x ^ 6 + 19200 * (1 - x ^ 2)
          + 19200 * (2 * q - 1) * (2 * q + 1)
          + 320 * D * q * (2 * q - x ^ 3) + D ^ 2 * q ^ 2 := by
        positivity
      _ = 19200 * x ^ 2 * (5 * x ^ 4 - 1)
          - 320 * D * x ^ 3 * q + (76800 + 640 * D + D ^ 2) * q ^ 2 := by
        ring
  · have hx_fourth : (1 / 2 : ℝ) < x ^ 4 := lt_of_not_ge hsmall
    have hhigh : 0 ≤ 2 * x ^ 4 - 1 := by linarith only [hx_fourth]
    calc
      0 ≤ (240 * x ^ 3 - (2 / 3 : ℝ) * D * q) ^ 2
          + 19200 * x ^ 2 * (2 * x ^ 4 - 1)
          + (76800 + 640 * D + (5 / 9 : ℝ) * D ^ 2) * q ^ 2 := by
        positivity
      _ = 19200 * x ^ 2 * (5 * x ^ 4 - 1)
          - 320 * D * x ^ 3 * q + (76800 + 640 * D + D ^ 2) * q ^ 2 := by
        ring


/-- The universal cutoff absorbs every nonnegative drift with a constant chosen
only from that drift. No flow, point, time, or accuracy parameter enters it. -/
theorem differential_bound {D u : ℝ} (hD : 0 ≤ D) (hu : u < 1 / 10) :
    D * deriv value u - bound D * value u ≤
      2 * (deriv value u) ^ 2 / value u - deriv (deriv value) u := by
  have hq := denominator_pos hu
  have hp := polynomial_nonneg D (part u) hD (part_mem hu).1 (part_mem hu).2.le
  have he :
      2 * (deriv value u) ^ 2 / value u - deriv (deriv value) u
        - D * deriv value u + bound D * value u =
      (19200 * part u ^ 2 * (5 * part u ^ 4 - 1)
        - 320 * D * part u ^ 3 * denominator u + bound D * denominator u ^ 2)
        / denominator u ^ 6 := by
    rw [deriv_value hu, deriv2_value hu]
    dsimp only [value]
    field_simp [hq.ne']
    dsimp only [denominator]
    ring
  have hn : 0 ≤ 2 * (deriv value u) ^ 2 / value u - deriv (deriv value) u
      - D * deriv value u + bound D * value u := by
    rw [he]
    exact div_nonneg hp (pow_pos hq 6).le
  linarith only [hn]

/-- The existential interface keeps the cutoff fixed before the drift parameter. -/
theorem exists_constant (D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u < (1 / 10 : ℝ),
      D * deriv value u - C * value u ≤
        2 * (deriv value u) ^ 2 / value u - deriv (deriv value) u :=
  ⟨bound D, bound_nonneg hD, fun _ hu => differential_bound hD hu⟩

end DifferentialGeometry.Analysis.SingularBarrier

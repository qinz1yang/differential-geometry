import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# FC39 producer, packet P0 (gate 1): the S³ circle kind, the adapted slack functions

Part B of the circle kind of the S³ inhabitant, one-variable layer. In the base coordinates
`(ψ, r)` of `sphereCircleBundle` (`ψ = ‖stereo_N θ‖`, `r = ‖y‖`) the four faces of `C₁ = [1, 4]²`
carry the slack functions ADAPTED to the actual rows (lead decision 02:45, the labelled contracts
force them on every corner neighbourhood):

* axis `ψ` (`false`): side `false` (south handle, `ψ = 1`) `ψ² − 1 = ‖w‖² − 1` (edge height minus
  level), side `true` (north handle, `ψ = 4`) `16 / ψ² − 1`;
* axis `r` (`true`): side `false` (`r = 1`, the new slim end) `q₀ + 3/5`, side `true` (`r = 4`, the
  face of `Z₊`) `3/5 − q₀`, with `q₀ = (r² − 4) / (r² + 4)` (`circHeight`).

The defining function of a face is `−slack`. The corner coordinate `circCornerInv a σ s` is the
value of the axis `a` coordinate with slack `s / 16`: `√(1 + s/16)`, `4 / √(1 + s/16)`,
`Q(s/16 − 3/5)`, `Q(3/5 − s/16)` with `Q(q) = 2 √((1 + q)/(1 − q))` the inverse of `q₀`.
Derivatives, signs, zeros, the two inverse identities, the bounds `(1/2, 8)` and the corner values.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped ContDiff

namespace GC.GraphManifold.Assembly.FC39P0

/-- The height `q₀ = (r² − 4) / (r² + 4)` of the stereographic chart as a function of the radius. -/
def circHeight (t : ℝ) : ℝ :=
  (t ^ 2 - 4) / (t ^ 2 + 4)

/-- The slack of the axis `a` (`false` = `ψ`, `true` = `r`) at the side `σ` (`false` = value `1`,
`true` = value `4`). -/
def circSlack : Bool → Bool → ℝ → ℝ
  | false, false, t => t ^ 2 - 1
  | false, true, t => 16 / t ^ 2 - 1
  | true, false, t => circHeight t + 3 / 5
  | true, true, t => 3 / 5 - circHeight t

/-- The derivative of the slack. -/
def circSlackDeriv : Bool → Bool → ℝ → ℝ
  | false, false, t => 2 * t
  | false, true, t => -(32 / t ^ 3)
  | true, false, t => 16 * t / (t ^ 2 + 4) ^ 2
  | true, true, t => -(16 * t / (t ^ 2 + 4) ^ 2)

/-- The value of a side: `1` (`false`) or `4` (`true`). -/
def circEndVal : Bool → ℝ
  | false => 1
  | true => 4

/-- The inverse `Q(q) = 2 √((1 + q) / (1 − q))` of the height. -/
def circQ (q : ℝ) : ℝ :=
  2 * √((1 + q) / (1 - q))

/-- The corner coordinate: the axis `a` coordinate with slack `s / 16`. -/
def circCornerInv : Bool → Bool → ℝ → ℝ
  | false, false, s => √(1 + 1 / 16 * s)
  | false, true, s => 4 / √(1 + 1 / 16 * s)
  | true, false, s => circQ (1 / 16 * s - 3 / 5)
  | true, true, s => circQ (3 / 5 - 1 / 16 * s)

/-! ## The height -/

theorem circHeight_add {t : ℝ} : circHeight t + 3 / 5 = 8 * (t ^ 2 - 1) / (5 * (t ^ 2 + 4)) := by
  have h : t ^ 2 + 4 ≠ 0 := by positivity
  rw [circHeight]
  field_simp
  ring

theorem circHeight_sub {t : ℝ} : 3 / 5 - circHeight t = 2 * (16 - t ^ 2) / (5 * (t ^ 2 + 4)) := by
  have h : t ^ 2 + 4 ≠ 0 := by positivity
  rw [circHeight]
  field_simp
  ring

theorem hasDerivAt_circHeight (t : ℝ) :
    HasDerivAt circHeight (16 * t / (t ^ 2 + 4) ^ 2) t := by
  have h : t ^ 2 + 4 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 - 4) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).sub_const 4
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 + 4) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const 4
  refine (h1.div h2 h).congr_deriv ?_
  field_simp
  ring

theorem contDiff_circHeight : ContDiff ℝ ∞ circHeight := by
  unfold circHeight
  exact ((contDiff_id.pow 2).sub contDiff_const).div ((contDiff_id.pow 2).add contDiff_const)
    fun t => by positivity

/-! ## The inverse `Q` of the height -/

theorem circQ_sq {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) : circQ q ^ 2 = 4 * ((1 + q) / (1 - q)) := by
  have h1 : 0 < 1 - q := by linarith [hq.2]
  have hz : 0 ≤ (1 + q) / (1 - q) := div_nonneg (by linarith [hq.1]) h1.le
  rw [circQ, mul_pow, Real.sq_sqrt hz]
  norm_num

theorem circQ_pos {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) : 0 < circQ q := by
  have h1 : 0 < 1 - q := by linarith [hq.2]
  have hz : 0 < (1 + q) / (1 - q) := div_pos (by linarith [hq.1]) h1
  rw [circQ]
  have := Real.sqrt_pos.2 hz
  positivity

theorem circHeight_circQ {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) : circHeight (circQ q) = q := by
  have h1 : 1 - q ≠ 0 := by linarith [hq.2]
  rw [circHeight, circQ_sq hq]
  have h2 : 4 * ((1 + q) / (1 - q)) + 4 = 8 / (1 - q) := by
    field_simp
    ring
  rw [h2]
  field_simp
  ring

theorem circQ_circHeight {t : ℝ} (ht : 0 < t) : circQ (circHeight t) = t := by
  have h : t ^ 2 + 4 ≠ 0 := by positivity
  have hz : (1 + circHeight t) / (1 - circHeight t) = (t / 2) ^ 2 := by
    rw [circHeight]
    field_simp
    ring
  rw [circQ, hz, Real.sqrt_sq (by positivity)]
  ring

theorem circQ_mem_wide {q : ℝ} (h1 : -15 / 17 < q) (h2 : q < 15 / 17) :
    circQ q ∈ Ioo (1 / 2 : ℝ) 8 := by
  have hq1 : 0 < 1 - q := by linarith
  have hz1 : 1 / 16 < (1 + q) / (1 - q) := by
    rw [lt_div_iff₀ hq1]
    linarith
  have hz2 : (1 + q) / (1 - q) < 16 := by
    rw [div_lt_iff₀ hq1]
    linarith
  have hs1 : 1 / 4 < √((1 + q) / (1 - q)) := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith
  have hs2 : √((1 + q) / (1 - q)) < 4 := by
    rw [Real.sqrt_lt' (by norm_num)]
    linarith
  rw [circQ]
  constructor <;> linarith

theorem contDiffAt_circQ {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) : ContDiffAt ℝ ∞ circQ q := by
  have h1 : 1 - q ≠ 0 := by linarith [hq.2]
  have hz : (1 + q) / (1 - q) ≠ 0 := div_ne_zero (by linarith [hq.1]) h1
  unfold circQ
  exact contDiffAt_const.mul
    (((contDiffAt_const.add contDiffAt_id).div (contDiffAt_const.sub contDiffAt_id) h1).sqrt hz)

/-! ## The slacks: derivatives, smoothness, signs -/

theorem hasDerivAt_circSlack (a σ : Bool) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (circSlack a σ) (circSlackDeriv a σ t) t := by
  have ht2 : t ^ 2 ≠ 0 := by positivity
  cases a <;> cases σ
  · change HasDerivAt (fun t : ℝ => t ^ 2 - 1) (2 * t) t
    exact ((hasDerivAt_pow 2 t).sub_const 1).congr_deriv (by norm_num)
  · refine ((hasDerivAt_const t (16 : ℝ)).div (hasDerivAt_pow 2 t) ht2).sub_const 1
      |>.congr_deriv ?_
    simp only [circSlackDeriv]
    field_simp
    ring
  · exact (hasDerivAt_circHeight t).add_const _
  · exact ((hasDerivAt_circHeight t).const_sub _).congr_deriv rfl

theorem circSlackDeriv_ne_zero (a σ : Bool) {t : ℝ} (ht : 0 < t) : circSlackDeriv a σ t ≠ 0 := by
  cases a <;> cases σ <;> simp only [circSlackDeriv] <;>
    first
    | positivity
    | exact neg_ne_zero.2 (by positivity)

theorem contDiffAt_circSlack (a σ : Bool) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ ∞ (circSlack a σ) t := by
  have ht2 : t ^ 2 ≠ 0 := by positivity
  cases a <;> cases σ
  · exact ((contDiff_id.pow 2).sub contDiff_const).contDiffAt
  · have hp : ContDiffAt ℝ ∞ (fun t : ℝ => t ^ 2) t := (contDiff_id.pow 2).contDiffAt
    exact (contDiffAt_const.div hp ht2).sub contDiffAt_const
  · exact (contDiff_circHeight.add contDiff_const).contDiffAt
  · exact (contDiff_const.sub contDiff_circHeight).contDiffAt

theorem circSlack_eq_zero_iff (a : Bool) {σ : Bool} {t : ℝ} (ht : 0 < t) :
    circSlack a σ t = 0 ↔ t = circEndVal σ := by
  cases a <;> cases σ <;> simp only [circSlack, circEndVal]
  · constructor
    · intro h
      nlinarith
    · rintro rfl
      norm_num
  · rw [sub_eq_zero, div_eq_one_iff_eq (by positivity)]
    constructor
    · intro h
      nlinarith
    · rintro rfl
      norm_num
  · rw [circHeight_add, div_eq_zero_iff]
    have h : 5 * (t ^ 2 + 4) ≠ 0 := by positivity
    simp only [h, or_false]
    constructor
    · intro h
      nlinarith
    · rintro rfl
      norm_num
  · rw [circHeight_sub, div_eq_zero_iff]
    have h : 5 * (t ^ 2 + 4) ≠ 0 := by positivity
    simp only [h, or_false]
    constructor
    · intro h
      nlinarith
    · rintro rfl
      norm_num

theorem circSlack_false_nonneg_iff (a : Bool) {t : ℝ} (ht : 0 < t) :
    0 ≤ circSlack a false t ↔ 1 ≤ t := by
  cases a <;> simp only [circSlack]
  · constructor <;> intro h <;> nlinarith
  · rw [circHeight_add, le_div_iff₀ (by positivity), zero_mul]
    constructor <;> intro h <;> nlinarith

theorem circSlack_true_nonneg_iff (a : Bool) {t : ℝ} (ht : 0 < t) :
    0 ≤ circSlack a true t ↔ t ≤ 4 := by
  cases a <;> simp only [circSlack]
  · rw [sub_nonneg, le_div_iff₀ (by positivity), one_mul]
    constructor <;> intro h <;> nlinarith
  · rw [circHeight_sub, le_div_iff₀ (by positivity), zero_mul]
    constructor <;> intro h <;> nlinarith

/-- The two slacks of one axis cannot both be small (the two sides are far apart). -/
theorem circSlack_other_gt (a σ : Bool) {t : ℝ} (ht : 0 < t) (h : |circSlack a σ t| < 1 / 8) :
    1 < circSlack a (!σ) t := by
  have hl := (abs_lt.1 h).1
  have hu := (abs_lt.1 h).2
  have ht2 : 0 < t ^ 2 := by positivity
  cases a <;> cases σ <;> simp only [circSlack, Bool.not_false, Bool.not_true] at hl hu ⊢
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ ht2]
    nlinarith
  · have h16 : 16 / t ^ 2 < 9 / 8 := by linarith
    rw [div_lt_iff₀ ht2] at h16
    nlinarith
  · linarith
  · linarith

/-! ## The corner coordinate -/

theorem one_add_pos_of_abs {s : ℝ} (hs : |s| < 2) : 0 < 1 + 1 / 16 * s := by
  have := (abs_lt.1 hs).1
  linarith

theorem circCornerInv_pos (a σ : Bool) {s : ℝ} (hs : |s| < 2) : 0 < circCornerInv a σ s := by
  have hu := one_add_pos_of_abs hs
  have hl := (abs_lt.1 hs).1
  have hh := (abs_lt.1 hs).2
  have hsq := Real.sqrt_pos.2 hu
  cases a <;> cases σ <;> simp only [circCornerInv]
  · exact hsq
  · positivity
  · exact circQ_pos ⟨by linarith, by linarith⟩
  · exact circQ_pos ⟨by linarith, by linarith⟩

/-- **The corner coordinate has slack `s / 16`.** -/
theorem circSlack_circCornerInv (a σ : Bool) {s : ℝ} (hs : |s| < 2) :
    circSlack a σ (circCornerInv a σ s) = 1 / 16 * s := by
  have hu := one_add_pos_of_abs hs
  have hl := (abs_lt.1 hs).1
  have hh := (abs_lt.1 hs).2
  cases a <;> cases σ <;> simp only [circSlack, circCornerInv]
  · rw [Real.sq_sqrt hu.le]
    ring
  · have hsq := Real.sqrt_pos.2 hu
    rw [div_pow, Real.sq_sqrt hu.le]
    field_simp
    ring
  · rw [circHeight_circQ ⟨by linarith, by linarith⟩]
    ring
  · rw [circHeight_circQ ⟨by linarith, by linarith⟩]
    ring

/-- **The slack determines the coordinate** (for a positive coordinate). -/
theorem circCornerInv_circSlack (a σ : Bool) {t : ℝ} (ht : 0 < t) :
    circCornerInv a σ (16 * circSlack a σ t) = t := by
  cases a <;> cases σ <;> simp only [circSlack, circCornerInv]
  · rw [show 1 + 1 / 16 * (16 * (t ^ 2 - 1)) = t ^ 2 by ring, Real.sqrt_sq ht.le]
  · have h4 : 1 + 1 / 16 * (16 * (16 / t ^ 2 - 1)) = (4 / t) ^ 2 := by
      field_simp
      ring
    rw [h4, Real.sqrt_sq (by positivity)]
    field_simp
  · rw [show 1 / 16 * (16 * (circHeight t + 3 / 5)) - 3 / 5 = circHeight t by ring,
      circQ_circHeight ht]
  · rw [show 3 / 5 - 1 / 16 * (16 * (3 / 5 - circHeight t)) = circHeight t by ring,
      circQ_circHeight ht]

/-- The corner coordinate stays in the wide interval `(1/2, 8)` of the base. -/
theorem circCornerInv_mem_wide (a σ : Bool) {s : ℝ} (hs : |s| < 2) :
    circCornerInv a σ s ∈ Ioo (1 / 2 : ℝ) 8 := by
  have hu := one_add_pos_of_abs hs
  have hl := (abs_lt.1 hs).1
  have hh := (abs_lt.1 hs).2
  have hs1 : 1 / 2 < √(1 + 1 / 16 * s) := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith
  have hs2 : √(1 + 1 / 16 * s) < 8 := by
    rw [Real.sqrt_lt' (by norm_num)]
    linarith
  have hsq := Real.sqrt_pos.2 hu
  cases a <;> cases σ <;> simp only [circCornerInv]
  · exact ⟨hs1, hs2⟩
  · constructor
    · rw [lt_div_iff₀ hsq]
      linarith
    · rw [div_lt_iff₀ hsq]
      linarith
  · exact circQ_mem_wide (by linarith) (by linarith)
  · exact circQ_mem_wide (by linarith) (by linarith)

/-- The corner coordinate at `0` is the side value. -/
theorem circCornerInv_zero (a σ : Bool) : circCornerInv a σ 0 = circEndVal σ := by
  have h0 : |(0 : ℝ)| < 2 := by norm_num
  have h := circSlack_circCornerInv a σ h0
  rw [mul_zero] at h
  exact (circSlack_eq_zero_iff a (circCornerInv_pos a σ h0)).1 h

theorem contDiffAt_circCornerInv (a σ : Bool) {s : ℝ} (hs : |s| < 2) :
    ContDiffAt ℝ ∞ (circCornerInv a σ) s := by
  have hu := one_add_pos_of_abs hs
  have hl := (abs_lt.1 hs).1
  have hh := (abs_lt.1 hs).2
  have hlin : ContDiffAt ℝ ∞ (fun s : ℝ => 1 + 1 / 16 * s) s :=
    contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)
  have hsq : ContDiffAt ℝ ∞ (fun s : ℝ => √(1 + 1 / 16 * s)) s := hlin.sqrt hu.ne'
  cases a <;> cases σ
  · exact hsq
  · exact contDiffAt_const.div hsq (Real.sqrt_pos.2 hu).ne'
  · exact (contDiffAt_circQ ⟨by linarith, by linarith⟩).comp s
      ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const)
  · exact (contDiffAt_circQ ⟨by linarith, by linarith⟩).comp s
      (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id))

end GC.GraphManifold.Assembly.FC39P0

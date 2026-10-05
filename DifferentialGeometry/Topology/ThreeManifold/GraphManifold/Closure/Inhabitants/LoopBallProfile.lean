import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopShellRound

/-!
The original ball radial defining profile is smooth, equals the true full rim scalar,
and becomes constant strictly inside the original ball chart radius.
-/

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace GC.GraphManifold.Assembly

private def ballProfileCutoff (r : ℝ) : ℝ := Real.smoothTransition (32 * (19 / 16 - r))

def loopBallProfile (r : ℝ) : ℝ := -1 + ballProfileCutoff r * (17 - 16 * r)

private theorem ballProfileCutoff_small {r : ℝ} (hr : r ≤ 37 / 32) : ballProfileCutoff r = 1 := by
  exact Real.smoothTransition.one_of_one_le (by linarith)

private theorem ballProfileCutoff_large {r : ℝ} (hr : 19 / 16 ≤ r) : ballProfileCutoff r = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

theorem loopBallProfile_small {r : ℝ} (hr : r ≤ 37 / 32) :
    loopBallProfile r = 16 * (1 - r) := by
  rw [loopBallProfile, ballProfileCutoff_small hr]
  ring

theorem loopBallProfile_zero {r : ℝ} : loopBallProfile r = 0 ↔ r = 1 := by
  constructor
  · intro h
    by_cases hr : r ≤ 37 / 32
    · rw [loopBallProfile_small hr] at h
      linarith
    · have hc0 := Real.smoothTransition.nonneg (32 * (19 / 16 - r))
      have hneg : 17 - 16 * r < 0 := by linarith
      have hm := mul_nonpos_of_nonneg_of_nonpos hc0 hneg.le
      dsimp [loopBallProfile, ballProfileCutoff] at h
      linarith
  · rintro rfl
    rw [loopBallProfile_small (by norm_num)]
    norm_num

theorem loopBallProfile_large {r : ℝ} (hr : 19 / 16 ≤ r) :
    loopBallProfile r = -1 := by
  rw [loopBallProfile, ballProfileCutoff_large hr]
  ring


theorem loopBallProfile_smooth : ContDiff ℝ ∞ loopBallProfile := by
  have hc : ContDiff ℝ ∞ ballProfileCutoff :=
    (Real.smoothTransition.contDiff (n := ⊤)).comp
      (contDiff_const.mul (contDiff_const.sub contDiff_id))
  exact contDiff_const.add (hc.mul (contDiff_const.sub (contDiff_const.mul contDiff_id)))


theorem loopBallProfile_nonpos {r : ℝ} : loopBallProfile r ≤ 0 ↔ 1 ≤ r := by
  by_cases hr : r ≤ 37 / 32
  · rw [loopBallProfile_small hr]
    constructor <;> intro h <;> linarith
  · have hc := Real.smoothTransition.nonneg (32 * (19 / 16 - r))
    have hm := mul_nonpos_of_nonneg_of_nonpos hc (by linarith : 17 - 16 * r ≤ 0)
    constructor
    · intro _
      linarith
    · intro _
      dsimp [loopBallProfile, ballProfileCutoff]
      linarith


theorem loopBallProfile_pos {r : ℝ} : 0 < loopBallProfile r ↔ r < 1 := by
  exact lt_iff_lt_of_le_iff_le loopBallProfile_nonpos


theorem loopBallProfile_rim {y : ℝ} (hy : |y| < 2) :
    loopBallProfile (1 + (1 / 16) * y) = -y := by
  have hb := (abs_lt.mp hy).2
  rw [loopBallProfile_small (by linarith)]
  ring
end GC.GraphManifold.Assembly

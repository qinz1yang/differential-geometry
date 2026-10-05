import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopHandleRimInverse

/-!
The original handle radial and time cutoffs are smooth inside its actual wide chart.
The defining profile equals the mandated first corner coordinate and has controlled zero scope.
-/

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace GC.GraphManifold.Assembly

private def handleProfileRadial (s : ℝ) : ℝ := Real.smoothTransition (8 * (5 / 4 - s))

private def handleProfileTime (t : ℝ) : ℝ :=
  Real.smoothTransition (16 * (t + 3 / 16)) * Real.smoothTransition (16 * (19 / 16 - t))

private theorem handleProfileRadial_small {s : ℝ} (hs : s ≤ 9 / 8) :
    handleProfileRadial s = 1 := Real.smoothTransition.one_of_one_le (by linarith)

private theorem handleProfileRadial_large {s : ℝ} (hs : 5 / 4 ≤ s) :
    handleProfileRadial s = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem handleProfileTime_middle {t : ℝ} (ht : -1 / 8 ≤ t ∧ t ≤ 9 / 8) :
    handleProfileTime t = 1 := by
  rw [handleProfileTime, Real.smoothTransition.one_of_one_le (by linarith [ht.1]),
    Real.smoothTransition.one_of_one_le (by linarith [ht.2])]
  norm_num

private theorem handleProfileTime_bounds (t : ℝ) :
    0 ≤ handleProfileTime t ∧ handleProfileTime t ≤ 1 := by
  have ha0 := Real.smoothTransition.nonneg (16 * (t + 3 / 16))
  have ha1 := Real.smoothTransition.le_one (16 * (t + 3 / 16))
  have hb0 := Real.smoothTransition.nonneg (16 * (19 / 16 - t))
  have hb1 := Real.smoothTransition.le_one (16 * (19 / 16 - t))
  refine ⟨mul_nonneg ha0 hb0, ?_⟩
  calc
    _ ≤ 1 * Real.smoothTransition (16 * (19 / 16 - t)) :=
      mul_le_mul_of_nonneg_right ha1 hb0
    _ ≤ 1 := by simpa only [one_mul] using hb1

private theorem handleProfileTime_zero {t : ℝ} (ht : t ≤ -3 / 16 ∨ 19 / 16 ≤ t) :
    handleProfileTime t = 0 := by
  rcases ht with ht | ht
  · rw [handleProfileTime, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  · have he : Real.smoothTransition (16 * (19 / 16 - t)) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [handleProfileTime, he, mul_zero]

def loopHandleProfile (s t : ℝ) : ℝ :=
  -1 + handleProfileRadial s * handleProfileTime t * (17 - 16 * s)

theorem loopHandleProfile_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => loopHandleProfile p.1 p.2) := by
  have hr : ContDiff ℝ ∞ (fun p : ℝ × ℝ => handleProfileRadial p.1) :=
    (Real.smoothTransition.contDiff (n := ⊤)).comp
      (contDiff_const.mul (contDiff_const.sub contDiff_fst))
  have ht : ContDiff ℝ ∞ (fun p : ℝ × ℝ => handleProfileTime p.2) :=
    ((Real.smoothTransition.contDiff (n := ⊤)).comp
      (contDiff_const.mul (contDiff_snd.add contDiff_const))).mul
      ((Real.smoothTransition.contDiff (n := ⊤)).comp
        (contDiff_const.mul (contDiff_const.sub contDiff_snd)))
  exact contDiff_const.add ((hr.mul ht).mul
    (contDiff_const.sub (contDiff_const.mul contDiff_fst)))

theorem loopHandleProfile_outer {s t : ℝ} (h : 5 / 4 ≤ s ∨ t ≤ -3 / 16 ∨ 19 / 16 ≤ t) :
    loopHandleProfile s t = -1 := by
  rcases h with h | h
  · rw [loopHandleProfile, handleProfileRadial_large h, zero_mul, zero_mul, add_zero]
  · rw [loopHandleProfile, handleProfileTime_zero h, mul_zero, zero_mul, add_zero]

theorem loopHandleProfile_middle {s t : ℝ} (hs : s ≤ 9 / 8) (ht : -1 / 8 ≤ t ∧ t ≤ 9 / 8) :
    loopHandleProfile s t = 16 * (1 - s) := by
  rw [loopHandleProfile, handleProfileRadial_small hs, handleProfileTime_middle ht]
  ring

theorem loopHandleProfile_zero_bounds {s t : ℝ} (h : loopHandleProfile s t = 0) :
    s ≤ 1 ∧ -3 / 16 < t ∧ t < 19 / 16 := by
  have hs : s ≤ 1 := by
    by_contra hs
    have ha0 := Real.smoothTransition.nonneg (8 * (5 / 4 - s))
    have ha1 := Real.smoothTransition.le_one (8 * (5 / 4 - s))
    have ht := handleProfileTime_bounds t
    have hp0 : 0 ≤ handleProfileRadial s * handleProfileTime t := mul_nonneg ha0 ht.1
    have hp1 : handleProfileRadial s * handleProfileTime t ≤ 1 := by
      calc
        _ ≤ 1 * handleProfileTime t := mul_le_mul_of_nonneg_right ha1 ht.1
        _ ≤ 1 := by simpa only [one_mul] using ht.2
    have hf : 17 - 16 * s < 1 := by linarith
    have hm : handleProfileRadial s * handleProfileTime t * (17 - 16 * s) < 1 := by
      by_cases hn : 0 ≤ 17 - 16 * s
      · have hh := mul_le_mul_of_nonneg_right hp1 hn
        linarith
      · have hh := mul_nonpos_of_nonneg_of_nonpos hp0 (le_of_not_ge hn)
        linarith
    dsimp [loopHandleProfile] at h
    linarith
  refine ⟨hs, ?_, ?_⟩
  · by_contra ht
    have he := loopHandleProfile_outer (Or.inr (Or.inl (le_of_not_gt ht))) (s := s)
    rw [h] at he
    norm_num at he
  · by_contra ht
    have he := loopHandleProfile_outer (Or.inr (Or.inr (le_of_not_gt ht))) (s := s)
    rw [h] at he
    norm_num at he

theorem loopHandleProfile_zero_time {s t : ℝ} (h : loopHandleProfile s t = 0) :
    0 < handleProfileTime t := by
  have ht := (handleProfileTime_bounds t).1
  by_contra hn
  have he : handleProfileTime t = 0 := le_antisymm (le_of_not_gt hn) ht
  rw [loopHandleProfile, he, mul_zero, zero_mul, add_zero] at h
  norm_num at h

theorem loopHandleProfile_rim (b : Bool) {x y : ℝ} (hx : |x| < 2) (hy : |y| < 2) :
    loopHandleProfile (1 + (1 / 16) * x) (if b then 1 - (1 / 16) * y else (1 / 16) * y) =
      -x := by
  have hx' := (abs_lt.mp hx).2
  have hy' := abs_lt.mp hy
  have ht : -1 / 8 ≤ (if b then 1 - (1 / 16) * y else (1 / 16) * y) ∧
      (if b then 1 - (1 / 16) * y else (1 / 16) * y) ≤ 9 / 8 := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith [hy'.1, hy'.2]
  rw [loopHandleProfile_middle (by linarith) ht]
  ring

end GC.GraphManifold.Assembly

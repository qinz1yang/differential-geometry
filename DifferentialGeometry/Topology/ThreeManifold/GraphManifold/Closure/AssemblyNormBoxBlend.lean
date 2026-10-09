import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRimRounding
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# FC42 normalization, packet N1 (a)–(b): the blended box rounding and the box scalings

Lane ASM-NRM (frozen text `build-logs/scratch/ASM-NRM/Targets.lean`, sections N1 (a), (b)). The
support preparation N1 shrinks every corner chart of the circle region and every rim chart by the
scaling `v ↦ ε • v` of the rim box. Since the standard rim rounding `ψ_std = roundedMin (1/4)` is
not homogeneous, the common rounding must be re-chosen on the old charts; this file provides the
plane function used there and the two scalings as partial diffeomorphisms.

* `boxCutoff`: a smooth cutoff, `0` on the closed box `|x|, |y| ≤ 5/4`, `1` off the open box
  `rimBox (3/2)`, with values in `[0, 1]` and vanishing differential where it is `0` or `1`.
* `boxBlend ε = (1 - φ) · ε ψ_std(ε⁻¹ •  ·) + φ · ψ_std`. Facts (for `0 < ε ≤ 1/2`):
  `boxBlend_smul` (`g (ε • v) = ε ψ_std v` on `rimBox 2`), `boxBlend_eq_of_not_mem`
  (`g = ψ_std` off `rimBox (3/2)`), `boxBlend_nonneg_iff` (off `rimBox ε`, `0 ≤ g` is the closed
  quadrant), `fderiv_boxBlend_diag` (at a zero of `g`, the derivative along `(1, 1)` is `1`).
  Regularity: at a zero either the cutoff is `0` or `1` (a critical point of the cutoff), or both
  roundings equal `min` (`|x - y| ≥ 1/4`); in the remaining band both have the same strict sign.
* `boxScaling ε`: `v ↦ ε • v` from `rimBox 2` onto `rimBox (2 ε)`; `rimScaling ε`:
  `(θ, v) ↦ (θ, ε • v)` from `Circle × rimBox 2` onto `Circle × rimBox (2 ε)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry.Topology.Manifold.CornerRounding
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

/-! ## The cutoff -/

/-- The line bump: `1` on `[-5/4, 5/4]`, `0` off `(-3/2, 3/2)`. -/
def cutoffBump : ContDiffBump (0 : ℝ) :=
  ⟨5 / 4, 3 / 2, by norm_num, by norm_num⟩

theorem cutoffBump_eq_one {t : ℝ} (ht : |t| ≤ 5 / 4) : cutoffBump t = 1 :=
  cutoffBump.one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact ht)

theorem cutoffBump_eq_zero {t : ℝ} (ht : 3 / 2 ≤ |t|) : cutoffBump t = 0 :=
  cutoffBump.zero_of_le_dist (by
    rw [Real.dist_eq, sub_zero]
    exact ht)

/-- **N1.** The plateau cutoff of the blend: `0` on `closedBox (5/4)`, `1` off `rimBox (3/2)`. -/
def boxCutoff (v : ℝ × ℝ) : ℝ :=
  1 - cutoffBump v.1 * cutoffBump v.2

theorem contDiff_boxCutoff : ContDiff ℝ ∞ boxCutoff :=
  contDiff_const.sub ((cutoffBump.contDiff.comp contDiff_fst).mul
    (cutoffBump.contDiff.comp contDiff_snd))

theorem boxCutoff_nonneg (v : ℝ × ℝ) : 0 ≤ boxCutoff v := by
  have h1 := cutoffBump.nonneg' v.1
  have h2 := cutoffBump.nonneg' v.2
  have h3 : cutoffBump v.1 ≤ 1 := cutoffBump.le_one
  have h4 : cutoffBump v.2 ≤ 1 := cutoffBump.le_one
  unfold boxCutoff
  nlinarith

theorem boxCutoff_le_one (v : ℝ × ℝ) : boxCutoff v ≤ 1 := by
  have h1 := cutoffBump.nonneg' v.1
  have h2 := cutoffBump.nonneg' v.2
  unfold boxCutoff
  nlinarith

theorem boxCutoff_eq_zero {v : ℝ × ℝ} (h1 : |v.1| ≤ 5 / 4) (h2 : |v.2| ≤ 5 / 4) :
    boxCutoff v = 0 := by
  rw [boxCutoff, cutoffBump_eq_one h1, cutoffBump_eq_one h2]
  ring

theorem boxCutoff_eq_one {v : ℝ × ℝ} (hv : v ∉ rimBox (3 / 2)) : boxCutoff v = 1 := by
  simp only [rimBox, mem_ofPred_eq, not_and_or, not_lt] at hv
  rcases hv with h | h
  · rw [boxCutoff, cutoffBump_eq_zero h]
    ring
  · rw [boxCutoff, cutoffBump_eq_zero h]
    ring

theorem boxCutoff_eq_zero_of_mem {v : ℝ × ℝ} (hv : v ∈ rimBox 1) : boxCutoff v = 0 :=
  boxCutoff_eq_zero (by linarith [hv.1]) (by linarith [hv.2])

/-- Where the cutoff is `0` or `1` its differential vanishes (a global minimum or maximum). -/
theorem fderiv_boxCutoff_eq_zero {v : ℝ × ℝ} (h : boxCutoff v = 0 ∨ boxCutoff v = 1) :
    fderiv ℝ boxCutoff v = 0 := by
  rcases h with h | h
  · apply IsLocalMin.fderiv_eq_zero
    exact Filter.Eventually.of_forall fun y => by rw [h]; exact boxCutoff_nonneg y
  · apply IsLocalMax.fderiv_eq_zero
    exact Filter.Eventually.of_forall fun y => by rw [h]; exact boxCutoff_le_one y

/-! ## The diagonal-slope lemma -/

/-- A function differentiable at `v` that grows with slope one along the diagonal has derivative
`1` in the direction `(1, 1)`. -/
theorem fderiv_diag_eq_one_of_add_diag {f : ℝ × ℝ → ℝ} {v : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f v) (hdiag : ∀ t : ℝ, f (v + (t, t)) = f v + t) :
    fderiv ℝ f v (1, 1) = 1 := by
  have hline : HasDerivAt (fun t : ℝ => v + t • ((1 : ℝ), (1 : ℝ))) ((1 : ℝ), (1 : ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ((1 : ℝ), (1 : ℝ))).const_add v
  have hcomp : HasDerivAt (fun t : ℝ => f (v + t • ((1 : ℝ), (1 : ℝ)))) (fderiv ℝ f v (1, 1)) 0 := by
    have hd : HasFDerivAt f (fderiv ℝ f v) (v + (0 : ℝ) • ((1 : ℝ), (1 : ℝ))) := by
      simpa using hf.hasFDerivAt
    exact hd.comp_hasDerivAt (0 : ℝ) hline
  have hfun : (fun t : ℝ => f (v + t • ((1 : ℝ), (1 : ℝ)))) = fun t => f v + t := by
    funext t
    have ht : t • ((1 : ℝ), (1 : ℝ)) = (t, t) := by simp
    rw [ht, hdiag]
  rw [hfun] at hcomp
  exact hcomp.unique ((hasDerivAt_id (0 : ℝ)).const_add (f v))

/-! ## The scaled standard rounding -/

/-- The scaled standard rim rounding `ε ψ_std(ε⁻¹ • v)`. -/
def scaledRimRounding (ε : ℝ) (v : ℝ × ℝ) : ℝ :=
  ε * standardRimRounding (ε⁻¹ • v)

theorem contDiff_scaledRimRounding (ε : ℝ) : ContDiff ℝ ∞ (scaledRimRounding ε) :=
  contDiff_const.mul (contDiff_standardRimRounding.comp (contDiff_const_smul ε⁻¹))

theorem scaledRimRounding_add_diag {ε : ℝ} (hε : ε ≠ 0) (v : ℝ × ℝ) (t : ℝ) :
    scaledRimRounding ε (v + (t, t)) = scaledRimRounding ε v + t := by
  have h : ε⁻¹ • (v + (t, t)) = ε⁻¹ • v + (ε⁻¹ * t, ε⁻¹ * t) := by
    rw [smul_add]
    simp
  rw [scaledRimRounding, scaledRimRounding, h, standardRimRounding_add_diag, mul_add,
    mul_inv_cancel_left₀ hε]

theorem fderiv_scaledRimRounding_diag {ε : ℝ} (hε : ε ≠ 0) (v : ℝ × ℝ) :
    fderiv ℝ (scaledRimRounding ε) v (1, 1) = 1 :=
  fderiv_diag_eq_one_of_add_diag
    ((contDiff_scaledRimRounding ε).differentiable (by simp) v) (scaledRimRounding_add_diag hε v)

theorem standardRimRounding_eq_min {v : ℝ × ℝ} (h : 1 / 4 ≤ |v.1 - v.2|) :
    standardRimRounding v = min v.1 v.2 :=
  roundedMin_eq_min rimRoundingWidth_pos (by rw [rimRoundingWidth]; exact h)

theorem scaledRimRounding_eq_min {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {v : ℝ × ℝ}
    (h : 1 / 4 ≤ |v.1 - v.2|) : scaledRimRounding ε v = min v.1 v.2 := by
  have hsc : (ε⁻¹ • v).1 - (ε⁻¹ • v).2 = ε⁻¹ * (v.1 - v.2) := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hge : 1 / 4 ≤ |(ε⁻¹ • v).1 - (ε⁻¹ • v).2| := by
    rw [hsc, abs_mul, abs_of_pos (inv_pos.mpr hε)]
    have h1 : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
    nlinarith [abs_nonneg (v.1 - v.2)]
  rw [scaledRimRounding, standardRimRounding_eq_min hge]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rcases le_total v.1 v.2 with hv | hv
  · have : ε⁻¹ * v.1 ≤ ε⁻¹ * v.2 := mul_le_mul_of_nonneg_left hv (inv_pos.mpr hε).le
    rw [min_eq_left this, min_eq_left hv]
    field_simp
  · have : ε⁻¹ * v.2 ≤ ε⁻¹ * v.1 := mul_le_mul_of_nonneg_left hv (inv_pos.mpr hε).le
    rw [min_eq_right this, min_eq_right hv]
    field_simp

theorem scaledRimRounding_le_min {ε : ℝ} (hε : 0 < ε) (v : ℝ × ℝ) :
    scaledRimRounding ε v ≤ min v.1 v.2 := by
  have h := standardRimRounding_le_min (ε⁻¹ • v)
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h
  have h' := mul_le_mul_of_nonneg_left h hε.le
  rw [scaledRimRounding]
  refine h'.trans (le_of_eq ?_)
  rcases le_total v.1 v.2 with hv | hv
  · have : ε⁻¹ * v.1 ≤ ε⁻¹ * v.2 := mul_le_mul_of_nonneg_left hv (inv_pos.mpr hε).le
    rw [min_eq_left this, min_eq_left hv]
    field_simp
  · have : ε⁻¹ * v.2 ≤ ε⁻¹ * v.1 := mul_le_mul_of_nonneg_left hv (inv_pos.mpr hε).le
    rw [min_eq_right this, min_eq_right hv]
    field_simp

theorem min_sub_le_scaledRimRounding {ε : ℝ} (hε : 0 < ε) (v : ℝ × ℝ) :
    min v.1 v.2 - ε / 4 ≤ scaledRimRounding ε v := by
  have h := min_sub_le_roundedMin rimRoundingWidth_pos (ε⁻¹ • v).1 (ε⁻¹ • v).2
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, rimRoundingWidth] at h
  have h' := mul_le_mul_of_nonneg_left h hε.le
  rw [scaledRimRounding, standardRimRounding]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, rimRoundingWidth]
  refine le_trans (le_of_eq ?_) h'
  rw [mul_sub]
  congr 1
  · rcases le_total v.1 v.2 with hv | hv
    · have : ε⁻¹ * v.1 ≤ ε⁻¹ * v.2 := mul_le_mul_of_nonneg_left hv (inv_pos.mpr hε).le
      rw [min_eq_left this, min_eq_left hv]
      field_simp
    · have : ε⁻¹ * v.2 ≤ ε⁻¹ * v.1 := mul_le_mul_of_nonneg_left hv (inv_pos.mpr hε).le
      rw [min_eq_right this, min_eq_right hv]
      field_simp
  · ring

theorem min_sub_le_standardRimRounding (v : ℝ × ℝ) : min v.1 v.2 - 1 / 4 ≤ standardRimRounding v := by
  have h := min_sub_le_roundedMin rimRoundingWidth_pos v.1 v.2
  rw [rimRoundingWidth] at h
  exact h

/-- Off the box `rimBox ε`, the scaled rounding is nonnegative exactly on the closed quadrant. -/
theorem scaledRimRounding_nonneg_iff {ε : ℝ} (hε : 0 < ε) {v : ℝ × ℝ} (hv : v ∉ rimBox ε) :
    0 ≤ scaledRimRounding ε v ↔ (0 ≤ v.1 ∧ 0 ≤ v.2) := by
  have hv' : ε⁻¹ • v ∉ rimBox 1 := by
    rintro ⟨h1, h2⟩
    apply hv
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul,
      abs_of_pos (inv_pos.mpr hε)] at h1 h2
    refine ⟨?_, ?_⟩
    · have := (inv_mul_lt_iff₀ hε).mp h1
      linarith
    · have := (inv_mul_lt_iff₀ hε).mp h2
      linarith
  rw [scaledRimRounding, mul_nonneg_iff_of_pos_left hε, standardRimRounding_nonneg_iff hv']
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have hi := inv_pos.mpr hε
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(mul_nonneg_iff_of_pos_left hi).mp h1, (mul_nonneg_iff_of_pos_left hi).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_nonneg hi.le h1, mul_nonneg hi.le h2⟩

/-! ## The blend -/

/-- **N1.** The blend `g_ε = (1 - φ) · ε ψ_std(ε⁻¹ •  ·) + φ · ψ_std` of the scaled and the original
standard rim rounding. -/
def boxBlend (ε : ℝ) (v : ℝ × ℝ) : ℝ :=
  (1 - boxCutoff v) * (ε * standardRimRounding (ε⁻¹ • v)) + boxCutoff v * standardRimRounding v

theorem boxBlend_eq (ε : ℝ) (v : ℝ × ℝ) :
    boxBlend ε v = (1 - boxCutoff v) * scaledRimRounding ε v + boxCutoff v * standardRimRounding v :=
  rfl

theorem contDiff_boxBlend (ε : ℝ) : ContDiff ℝ ∞ (boxBlend ε) :=
  ((contDiff_const.sub contDiff_boxCutoff).mul (contDiff_scaledRimRounding ε)).add
    (contDiff_boxCutoff.mul contDiff_standardRimRounding)

theorem boxBlend_smul {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    boxBlend ε (ε • v) = ε * standardRimRounding v := by
  have hbox : ε • v ∈ rimBox 1 := by
    simp only [rimBox, mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul,
      abs_of_pos hε]
    exact ⟨by nlinarith [hv.1, abs_nonneg v.1], by nlinarith [hv.2, abs_nonneg v.2]⟩
  rw [boxBlend, boxCutoff_eq_zero_of_mem hbox, inv_smul_smul₀ hε.ne']
  ring

theorem boxBlend_eq_of_not_mem {ε : ℝ} {v : ℝ × ℝ} (hv : v ∉ rimBox (3 / 2)) :
    boxBlend ε v = standardRimRounding v := by
  rw [boxBlend, boxCutoff_eq_one hv]
  ring

/-- A positive cutoff value puts the point off the open unit box. -/
theorem not_mem_rimBox_one_of_boxCutoff_ne_zero {v : ℝ × ℝ} (h : boxCutoff v ≠ 0) :
    v ∉ rimBox 1 :=
  fun hv => h (boxCutoff_eq_zero_of_mem hv)

theorem boxBlend_nonneg_iff {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) {v : ℝ × ℝ}
    (hv : v ∉ rimBox ε) : 0 ≤ boxBlend ε v ↔ (0 ≤ v.1 ∧ 0 ≤ v.2) := by
  rw [boxBlend_eq]
  have hA := scaledRimRounding_nonneg_iff hε hv
  have hφ0 := boxCutoff_nonneg v
  have hφ1 := boxCutoff_le_one v
  by_cases h0 : boxCutoff v = 0
  · rw [h0]
    simpa using hA
  · have hB := standardRimRounding_nonneg_iff (not_mem_rimBox_one_of_boxCutoff_ne_zero h0)
    constructor
    · intro hg
      by_contra hq
      have hA' : scaledRimRounding ε v < 0 := not_le.mp fun h => hq (hA.mp h)
      have hB' : standardRimRounding v < 0 := not_le.mp fun h => hq (hB.mp h)
      have hpos : 0 < boxCutoff v := lt_of_le_of_ne hφ0 (Ne.symm h0)
      nlinarith
    · intro hq
      have hA' := hA.mpr hq
      have hB' := hB.mpr hq
      nlinarith

/-- The derivative of the blend in the direction `(1, 1)`. -/
theorem fderiv_boxBlend_diag_eq {ε : ℝ} (hε : ε ≠ 0) (v : ℝ × ℝ) :
    fderiv ℝ (boxBlend ε) v (1, 1) =
      1 + (standardRimRounding v - scaledRimRounding ε v) * fderiv ℝ boxCutoff v (1, 1) := by
  have hφ : HasFDerivAt boxCutoff (fderiv ℝ boxCutoff v) v :=
    (contDiff_boxCutoff.differentiable (by simp) v).hasFDerivAt
  have hA : HasFDerivAt (scaledRimRounding ε) (fderiv ℝ (scaledRimRounding ε) v) v :=
    ((contDiff_scaledRimRounding ε).differentiable (by simp) v).hasFDerivAt
  have hB : HasFDerivAt standardRimRounding (fderiv ℝ standardRimRounding v) v :=
    (contDiff_standardRimRounding.differentiable (by simp) v).hasFDerivAt
  have hg : HasFDerivAt (boxBlend ε)
      (((1 - boxCutoff v) • fderiv ℝ (scaledRimRounding ε) v +
          scaledRimRounding ε v • (-fderiv ℝ boxCutoff v)) +
        (boxCutoff v • fderiv ℝ standardRimRounding v +
          standardRimRounding v • fderiv ℝ boxCutoff v)) v := by
    have h1 : HasFDerivAt (fun w => 1 - boxCutoff w) (-fderiv ℝ boxCutoff v) v := by
      simpa using hφ.const_sub (1 : ℝ)
    have := (h1.mul hA).add (hφ.mul hB)
    convert this using 1
    funext w
    rfl
  rw [hg.fderiv]
  simp only [add_apply, smul_apply, neg_apply, smul_eq_mul, fderiv_scaledRimRounding_diag hε,
    fderiv_standardRimRounding_diag]
  ring

/-- **Regularity of the blend.** At a zero of the blend the derivative along `(1, 1)` is `1`. -/
theorem fderiv_boxBlend_diag {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) {v : ℝ × ℝ}
    (hv : boxBlend ε v = 0) : fderiv ℝ (boxBlend ε) v (1, 1) = 1 := by
  rw [fderiv_boxBlend_diag_eq hε.ne']
  suffices h : standardRimRounding v = scaledRimRounding ε v ∨ fderiv ℝ boxCutoff v = 0 by
    rcases h with h | h
    · rw [h]
      ring
    · rw [h]
      simp
  by_cases hd : 1 / 4 ≤ |v.1 - v.2|
  · left
    rw [standardRimRounding_eq_min hd, scaledRimRounding_eq_min hε (by linarith) hd]
  right
  apply fderiv_boxCutoff_eq_zero
  by_contra hmid
  obtain ⟨h0, h1⟩ := not_or.mp hmid
  have hφ0 : 0 < boxCutoff v := lt_of_le_of_ne (boxCutoff_nonneg v) (Ne.symm h0)
  have hφ1 : boxCutoff v < 1 := lt_of_le_of_ne (boxCutoff_le_one v) h1
  have hout : ¬ (|v.1| ≤ 5 / 4 ∧ |v.2| ≤ 5 / 4) := fun h => h0 (boxCutoff_eq_zero h.1 h.2)
  rw [not_le] at hd
  have hd' := abs_lt.mp hd
  rw [boxBlend_eq] at hv
  have hAl := scaledRimRounding_le_min hε v
  have hAg := min_sub_le_scaledRimRounding hε v
  have hBl := standardRimRounding_le_min v
  have hBg := min_sub_le_standardRimRounding v
  -- both coordinates exceed `1` in absolute value and have the same sign
  rcases not_and_or.mp hout with ho | ho <;> rw [not_le] at ho <;>
    rcases lt_abs.mp ho with ho' | ho'
  · have hm : 1 < min v.1 v.2 := lt_min (by linarith) (by linarith)
    have hA : 0 < scaledRimRounding ε v := by linarith
    have hB : 0 < standardRimRounding v := by linarith
    nlinarith
  · have hm : min v.1 v.2 < -1 := min_lt_iff.mpr (Or.inl (by linarith))
    have hA : scaledRimRounding ε v < 0 := by linarith [min_le_left v.1 v.2]
    have hB : standardRimRounding v < 0 := by linarith [min_le_left v.1 v.2]
    nlinarith
  · have hm : 1 < min v.1 v.2 := lt_min (by linarith) (by linarith)
    have hA : 0 < scaledRimRounding ε v := by linarith
    have hB : 0 < standardRimRounding v := by linarith
    nlinarith
  · have hm : min v.1 v.2 < -1 := min_lt_iff.mpr (Or.inr (by linarith))
    have hA : scaledRimRounding ε v < 0 := by linarith [min_le_right v.1 v.2]
    have hB : standardRimRounding v < 0 := by linarith [min_le_right v.1 v.2]
    nlinarith

/-- The blend is everywhere differentiable with nonzero differential at its zeros. -/
theorem fderiv_boxBlend_ne_zero {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) {v : ℝ × ℝ}
    (hv : boxBlend ε v = 0) : fderiv ℝ (boxBlend ε) v ≠ 0 := by
  intro h
  have := fderiv_boxBlend_diag hε hε1 hv
  rw [h] at this
  simp at this

/-! ## The box scalings -/

theorem isOpen_rimBox (r : ℝ) : IsOpen (rimBox r) :=
  (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)

theorem smul_mem_rimBox_iff {ε r : ℝ} (hε : 0 < ε) {v : ℝ × ℝ} :
    ε • v ∈ rimBox (r * ε) ↔ v ∈ rimBox r := by
  simp only [rimBox, mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul,
    abs_of_pos hε]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩

theorem smul_mem_rimBox {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {r : ℝ} {v : ℝ × ℝ}
    (hv : v ∈ rimBox r) : ε • v ∈ rimBox r := by
  have h := (smul_mem_rimBox_iff hε).mpr hv
  refine rimBox_mono ?_ h
  have hr : 0 ≤ r := (abs_nonneg _).trans hv.1.le
  nlinarith

/-- **N1.** `v ↦ ε • v` from `rimBox 2` onto `rimBox (2 ε)`. -/
def boxScaling (ε : ℝ) (hε : 0 < ε) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞ where
  toFun v := ε • v
  invFun w := ε⁻¹ • w
  source := rimBox 2
  target := rimBox (2 * ε)
  map_source' _ hv := (smul_mem_rimBox_iff hε).mpr hv
  map_target' w hw := by
    rw [← smul_mem_rimBox_iff hε, smul_inv_smul₀ hε.ne']
    exact hw
  left_inv' v _ := inv_smul_smul₀ hε.ne' v
  right_inv' w _ := smul_inv_smul₀ hε.ne' w
  open_source := isOpen_rimBox 2
  open_target := isOpen_rimBox (2 * ε)
  contMDiffOn_toFun := (contDiff_const_smul ε).contMDiff.contMDiffOn
  contMDiffOn_invFun := (contDiff_const_smul ε⁻¹).contMDiff.contMDiffOn

theorem boxScaling_source (ε : ℝ) (hε : 0 < ε) : (boxScaling ε hε).source = rimBox 2 :=
  rfl

theorem boxScaling_target (ε : ℝ) (hε : 0 < ε) : (boxScaling ε hε).target = rimBox (2 * ε) :=
  rfl

theorem boxScaling_apply (ε : ℝ) (hε : 0 < ε) (v : ℝ × ℝ) : boxScaling ε hε v = ε • v :=
  rfl

theorem boxScaling_symm_apply (ε : ℝ) (hε : 0 < ε) (w : ℝ × ℝ) :
    (boxScaling ε hε).symm w = ε⁻¹ • w :=
  rfl

/-- The rim scaling as a map. -/
def rimScaleMap (ε : ℝ) (p : Circle × (ℝ × ℝ)) : Circle × (ℝ × ℝ) :=
  (p.1, ε • p.2)

theorem contMDiff_rimScaleMap (ε : ℝ) :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ∞ (rimScaleMap ε) :=
  contMDiff_fst.prodMk ((contDiff_const_smul ε).contMDiff.comp contMDiff_snd)

/-- **N1.** `(θ, v) ↦ (θ, ε • v)` from `Circle × rimBox 2` onto `Circle × rimBox (2 ε)`. -/
def rimScaling (ε : ℝ) (hε : 0 < ε) :
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) (Circle × (ℝ × ℝ))
      (Circle × (ℝ × ℝ)) ∞ where
  toFun := rimScaleMap ε
  invFun := rimScaleMap ε⁻¹
  source := {p | p.2 ∈ rimBox 2}
  target := {p | p.2 ∈ rimBox (2 * ε)}
  map_source' _ hp := (smul_mem_rimBox_iff hε).mpr hp
  map_target' p hp := by
    change ε⁻¹ • p.2 ∈ rimBox 2
    rw [← smul_mem_rimBox_iff hε, smul_inv_smul₀ hε.ne']
    exact hp
  left_inv' p _ := by
    change (p.1, ε⁻¹ • ε • p.2) = p
    rw [inv_smul_smul₀ hε.ne']
  right_inv' p _ := by
    change (p.1, ε • ε⁻¹ • p.2) = p
    rw [smul_inv_smul₀ hε.ne']
  open_source := (isOpen_rimBox 2).preimage continuous_snd
  open_target := (isOpen_rimBox (2 * ε)).preimage continuous_snd
  contMDiffOn_toFun := (contMDiff_rimScaleMap ε).contMDiffOn
  contMDiffOn_invFun := (contMDiff_rimScaleMap ε⁻¹).contMDiffOn

theorem rimScaling_source (ε : ℝ) (hε : 0 < ε) {p : Circle × (ℝ × ℝ)} :
    p ∈ (rimScaling ε hε).source ↔ p.2 ∈ rimBox 2 :=
  Iff.rfl

theorem rimScaling_target {ε : ℝ} {hε : 0 < ε} {p : Circle × (ℝ × ℝ)} :
    p ∈ (rimScaling ε hε).target ↔ p.2 ∈ rimBox (2 * ε) :=
  Iff.rfl

theorem rimScaling_apply (ε : ℝ) (hε : 0 < ε) (p : Circle × (ℝ × ℝ)) :
    rimScaling ε hε p = (p.1, ε • p.2) :=
  rfl

end GC.GraphManifold.Assembly

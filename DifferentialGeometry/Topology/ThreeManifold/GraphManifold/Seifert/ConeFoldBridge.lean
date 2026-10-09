import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldApex

/-!
# Two circles meeting with a prescribed sign: the generic bridge

Lane A4, tier 2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §4).
For real centres `a ≠ b` and radii `A, B`, the point
`twoCircle a b A B w P = a + (A² - B² + (b - a)²)/(2(b - a)) + i w √P / (2|b - a|)`
lies on both circles `|u - a| = A`, `|u - b| = B` as soon as the Heron product
`((A + B)² - (b - a)²)((b - a)² - (A - B)²)` equals `w² P` with `P ≥ 0`
(`twoCircle_normSq_sub_left`, `_right`); its imaginary part has the sign of `w` when `P > 0`,
changing `w` into `-w` conjugates it (`twoCircle_neg`), and it is smooth wherever the data are and
`P > 0` (`contDiffAt_twoCircle`). A bridge between two families is this point with radii the two
moduli, `w` a side function of the wall and `P` the explicit positive cofactor of `w²` in the
Heron product: the vanishing factor is the second-order defect of the virtual heights.
The modulus `A ≥ 0` is recovered from the point, which gives injectivity of bridges
(`twoCircle_eq_iff`).
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

def twoCircle (a b A B w P : ℝ) : ℂ :=
  ((a + (A ^ 2 - B ^ 2 + (b - a) ^ 2) / (2 * (b - a)) : ℝ) : ℂ) +
    ((w * Real.sqrt P / (2 * |b - a|) : ℝ) : ℂ) * I

variable {a b A B w P : ℝ}

@[simp] theorem twoCircle_re (a b A B w P : ℝ) :
    (twoCircle a b A B w P).re = a + (A ^ 2 - B ^ 2 + (b - a) ^ 2) / (2 * (b - a)) := by
  simp only [twoCircle, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
  ring

@[simp] theorem twoCircle_im (a b A B w P : ℝ) :
    (twoCircle a b A B w P).im = w * Real.sqrt P / (2 * |b - a|) := by
  simp only [twoCircle, add_im, ofReal_re, mul_im, ofReal_im, I_re, I_im]
  ring

theorem heron_identity (A B d : ℝ) :
    4 * d ^ 2 * A ^ 2 - (A ^ 2 - B ^ 2 + d ^ 2) ^ 2 =
      ((A + B) ^ 2 - d ^ 2) * (d ^ 2 - (A - B) ^ 2) := by
  ring

theorem twoCircle_normSq_sub_left (hab : a ≠ b) (hP : 0 ≤ P)
    (hH : ((A + B) ^ 2 - (b - a) ^ 2) * ((b - a) ^ 2 - (A - B) ^ 2) = w ^ 2 * P) :
    normSq (twoCircle a b A B w P - a) = A ^ 2 := by
  have hd : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have hd2 : |b - a| ^ 2 = (b - a) ^ 2 := sq_abs _
  rw [normSq_apply]
  simp only [sub_re, sub_im, twoCircle_re, twoCircle_im, ofReal_re, ofReal_im, sub_zero,
    add_sub_cancel_left]
  have habs : |b - a| ≠ 0 := abs_ne_zero.2 hd
  have e : w * Real.sqrt P / (2 * |b - a|) * (w * Real.sqrt P / (2 * |b - a|)) =
      w ^ 2 * P / (4 * (b - a) ^ 2) := by
    rw [div_mul_div_comm, ← hd2]
    congr 1
    · rw [mul_mul_mul_comm, Real.mul_self_sqrt hP]
      ring
    · ring
  rw [e, ← hH]
  field_simp
  ring

theorem twoCircle_normSq_sub_right (hab : a ≠ b) (hP : 0 ≤ P)
    (hH : ((A + B) ^ 2 - (b - a) ^ 2) * ((b - a) ^ 2 - (A - B) ^ 2) = w ^ 2 * P) :
    normSq (twoCircle a b A B w P - b) = B ^ 2 := by
  have h := twoCircle_normSq_sub_left hab hP hH
  have hd : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  rw [normSq_apply] at h ⊢
  simp only [sub_re, sub_im, twoCircle_re, twoCircle_im, ofReal_re, ofReal_im, sub_zero,
    add_sub_cancel_left] at h ⊢
  set m := (A ^ 2 - B ^ 2 + (b - a) ^ 2) / (2 * (b - a)) with hm
  set y := w * Real.sqrt P / (2 * |b - a|)
  have hm' : m * (2 * (b - a)) = A ^ 2 - B ^ 2 + (b - a) ^ 2 := by
    rw [hm]
    field_simp
  have e : a + m - b = m - (b - a) := by ring
  rw [e]
  nlinarith [hm', h]

theorem norm_twoCircle_sub_left (hab : a ≠ b) (hP : 0 ≤ P) (hA : 0 ≤ A)
    (hH : ((A + B) ^ 2 - (b - a) ^ 2) * ((b - a) ^ 2 - (A - B) ^ 2) = w ^ 2 * P) :
    ‖twoCircle a b A B w P - a‖ = A := by
  conv_rhs => rw [← Real.sqrt_sq hA, ← twoCircle_normSq_sub_left hab hP hH, ← Complex.sq_norm,
    Real.sqrt_sq (norm_nonneg _)]

theorem norm_twoCircle_sub_right (hab : a ≠ b) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (hH : ((A + B) ^ 2 - (b - a) ^ 2) * ((b - a) ^ 2 - (A - B) ^ 2) = w ^ 2 * P) :
    ‖twoCircle a b A B w P - b‖ = B := by
  conv_rhs => rw [← Real.sqrt_sq hB, ← twoCircle_normSq_sub_right hab hP hH, ← Complex.sq_norm,
    Real.sqrt_sq (norm_nonneg _)]

theorem twoCircle_neg (a b A B w P : ℝ) :
    twoCircle a b A B (-w) P = conj (twoCircle a b A B w P) := by
  apply Complex.ext <;> simp [neg_div]

theorem twoCircle_im_pos (hab : a ≠ b) (hw : 0 < w) (hP : 0 < P) :
    0 < (twoCircle a b A B w P).im := by
  rw [twoCircle_im]
  have : 0 < |b - a| := abs_pos.2 (sub_ne_zero.2 hab.symm)
  have := Real.sqrt_pos.2 hP
  positivity

theorem twoCircle_im_eq_zero (a b A B P : ℝ) : (twoCircle a b A B 0 P).im = 0 := by
  simp

theorem twoCircle_im_neg (hab : a ≠ b) (hw : w < 0) (hP : 0 < P) :
    (twoCircle a b A B w P).im < 0 := by
  have h := twoCircle_im_pos (A := A) (B := B) hab (neg_pos.2 hw) hP
  rw [twoCircle_neg, conj_im] at h
  linarith

theorem contDiffAt_twoCircle {fA fB fw fP : ℂ → ℝ} {z : ℂ}
    (hA : ContDiffAt ℝ ∞ fA z) (hB : ContDiffAt ℝ ∞ fB z) (hw : ContDiffAt ℝ ∞ fw z)
    (hP : ContDiffAt ℝ ∞ fP z) (hP0 : 0 < fP z) (hab : a ≠ b) :
    ContDiffAt ℝ ∞ (fun u => twoCircle a b (fA u) (fB u) (fw u) (fP u)) z := by
  have hd : 2 * (b - a) ≠ 0 := mul_ne_zero two_ne_zero (sub_ne_zero.2 hab.symm)
  have hre : ContDiffAt ℝ ∞
      (fun u => a + ((fA u) ^ 2 - (fB u) ^ 2 + (b - a) ^ 2) / (2 * (b - a))) z :=
    contDiffAt_const.add (((hA.pow 2).sub (hB.pow 2)).add contDiffAt_const |>.div_const _)
  have hs : ContDiffAt ℝ ∞ (fun u => Real.sqrt (fP u)) z := hP.sqrt hP0.ne'
  have him : ContDiffAt ℝ ∞ (fun u => fw u * Real.sqrt (fP u) / (2 * |b - a|)) z :=
    (hw.mul hs).div_const _
  have hc : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  exact ((hc.contDiffAt.comp z hre).add ((hc.contDiffAt.comp z him).mul contDiffAt_const))

theorem twoCircle_eq_left (hab : a ≠ b) (hP : 0 ≤ P) (hA : 0 ≤ A)
    (hH : ((A + B) ^ 2 - (b - a) ^ 2) * ((b - a) ^ 2 - (A - B) ^ 2) = w ^ 2 * P)
    {A' B' w' P' : ℝ} (hP' : 0 ≤ P') (hA' : 0 ≤ A')
    (hH' : ((A' + B') ^ 2 - (b - a) ^ 2) * ((b - a) ^ 2 - (A' - B') ^ 2) = w' ^ 2 * P')
    (h : twoCircle a b A B w P = twoCircle a b A' B' w' P') : A = A' := by
  rw [← norm_twoCircle_sub_left hab hP hA hH, h, norm_twoCircle_sub_left hab hP' hA' hH']

theorem twoCircle_eq_right (hab : a ≠ b) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (hH : ((A + B) ^ 2 - (b - a) ^ 2) * ((b - a) ^ 2 - (A - B) ^ 2) = w ^ 2 * P)
    {A' B' w' P' : ℝ} (hP' : 0 ≤ P') (hB' : 0 ≤ B')
    (hH' : ((A' + B') ^ 2 - (b - a) ^ 2) * ((b - a) ^ 2 - (A' - B') ^ 2) = w' ^ 2 * P')
    (h : twoCircle a b A B w P = twoCircle a b A' B' w' P') : B = B' := by
  rw [← norm_twoCircle_sub_right hab hP hB hH, h, norm_twoCircle_sub_right hab hP' hB' hH']

end GC.Seifert

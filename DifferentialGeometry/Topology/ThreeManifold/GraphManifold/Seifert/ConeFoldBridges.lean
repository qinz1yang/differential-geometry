import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldBridge

/-!
# The two kinds of bridges of the cone fold

Lane A4, tier 2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §4).
With the profile `G = coneProfile K`:

* `outerBridge K b y η w q` is the point `u` with `|u| = 3/2 + G y`, `|u - b| = G η` (`b = ±3/2`)
  and `Im u` of the sign of `w`, given the factorisation `η - y = w² q` of the defect between the
  virtual height `η` of the vertex family and the height `y` of the cusp `∞`: the circles are
  internally tangent where `w = 0` and the Heron product is `w²` times the explicit
  `outerCofactor` (`outerBridge_heron`), positive when `q > 0` (`outerCofactor_pos`);
* `innerBridge K η₂ η₁ w q` is the point with `|u - 3/2| = G η₂`, `|u + 3/2| = G η₁`, for the wall
  between the two vertex families, given `η₁ η₂ - K = w² q`: the circles are externally tangent
  where `w = 0`, by the inversion identity of `G`.

The moduli (`norm_outerBridge`, `norm_outerBridge_sub`, `norm_innerBridge_sub`,
`norm_innerBridge_add`) and the reflection identity (`outerBridge_neg`, `innerBridge_neg`: changing
`w` into `-w` conjugates the point) follow from the generic `twoCircle`. Global facts used for the
separation of images: `Re` of an outer bridge has the sign of `b` and its modulus is `> 2`
(`outerBridge_re_mul_pos`), an inner bridge has modulus `< 2` (`norm_innerBridge_lt_two`).
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

variable {K : ℝ}

def outerCofactor (K b y η q : ℝ) : ℝ :=
  ((3 / 2 + coneProfile K y + coneProfile K η) ^ 2 - b ^ 2) *
    (|b| + 3 / 2 + coneProfile K y - coneProfile K η) *
    (q * (2 * K * (η + y) / ((η ^ 2 + K) * (y ^ 2 + K))))

def outerBridge (K b y η w q : ℝ) : ℂ :=
  twoCircle 0 b (3 / 2 + coneProfile K y) (coneProfile K η) w (outerCofactor K b y η q)

def innerCofactor (K η₂ η₁ q : ℝ) : ℝ :=
  (coneProfile K η₂ + coneProfile K η₁ + 3) * (9 - (coneProfile K η₂ - coneProfile K η₁) ^ 2) *
    (q * (2 * (η₁ * η₂ + K) / ((η₂ ^ 2 + K) * (η₁ ^ 2 + K))))

def innerBridge (K η₂ η₁ w q : ℝ) : ℂ :=
  twoCircle (3 / 2) (-(3 / 2)) (coneProfile K η₂) (coneProfile K η₁) w (innerCofactor K η₂ η₁ q)

theorem abs_three_halves {b : ℝ} (hb : b = 3 / 2 ∨ b = -(3 / 2)) : |b| = 3 / 2 := by
  rcases hb with rfl | rfl <;> norm_num

theorem outerBridge_heron (hK : 0 < K) {b y η w q : ℝ} (hb : b = 3 / 2 ∨ b = -(3 / 2))
    (hd : η - y = w ^ 2 * q) :
    ((3 / 2 + coneProfile K y + coneProfile K η) ^ 2 - (b - 0) ^ 2) *
        ((b - 0) ^ 2 - (3 / 2 + coneProfile K y - coneProfile K η) ^ 2) =
      w ^ 2 * outerCofactor K b y η q := by
  have hab := abs_three_halves hb
  have hb2 : b ^ 2 = 9 / 4 := by rcases hb with rfl | rfl <;> norm_num
  have hG := coneProfile_sub hK η y
  have e : (b - 0) ^ 2 - (3 / 2 + coneProfile K y - coneProfile K η) ^ 2 =
      (3 + coneProfile K y - coneProfile K η) * (coneProfile K η - coneProfile K y) := by
    rw [sub_zero, hb2]
    ring
  rw [e, hG, outerCofactor, hab, hd, sub_zero]
  ring

theorem outerCofactor_pos (hK : 0 < K) {b y η q : ℝ} (hb : b = 3 / 2 ∨ b = -(3 / 2))
    (hy : 0 < y) (hη : 0 < η) (hq : 0 < q) : 0 < outerCofactor K b y η q := by
  have hab := abs_three_halves hb
  have hb2 : b ^ 2 = 9 / 4 := by rcases hb with rfl | rfl <;> norm_num
  have h1 := half_le_coneProfile hK y
  have h2 := half_le_coneProfile hK η
  have h3 := coneProfile_lt hK η
  unfold outerCofactor
  rw [hab, hb2]
  have e1 : 0 < (3 / 2 + coneProfile K y + coneProfile K η) ^ 2 - 9 / 4 := by nlinarith
  have e2 : 0 < 3 / 2 + 3 / 2 + coneProfile K y - coneProfile K η := by linarith
  have e3 : 0 < 2 * K * (η + y) / ((η ^ 2 + K) * (y ^ 2 + K)) := by positivity
  positivity

theorem innerBridge_heron (hK : 0 < K) {η₂ η₁ w q : ℝ} (hd : η₁ * η₂ - K = w ^ 2 * q) :
    ((coneProfile K η₂ + coneProfile K η₁) ^ 2 - (-(3 / 2) - 3 / 2) ^ 2) *
        ((-(3 / 2) - 3 / 2) ^ 2 - (coneProfile K η₂ - coneProfile K η₁) ^ 2) =
      w ^ 2 * innerCofactor K η₂ η₁ q := by
  have hG := coneProfile_add_sub_three hK η₂ η₁
  have e : (coneProfile K η₂ + coneProfile K η₁) ^ 2 - (-(3 / 2) - 3 / 2) ^ 2 =
      (coneProfile K η₂ + coneProfile K η₁ - 3) * (coneProfile K η₂ + coneProfile K η₁ + 3) := by
    ring
  rw [e, hG, innerCofactor, show η₂ * η₁ = η₁ * η₂ by ring, hd]
  ring

theorem innerCofactor_pos (hK : 0 < K) {η₂ η₁ q : ℝ} (hη₂ : 0 < η₂) (hη₁ : 0 < η₁)
    (hq : 0 < q) : 0 < innerCofactor K η₂ η₁ q := by
  have h1 := half_le_coneProfile hK η₂
  have h2 := half_le_coneProfile hK η₁
  have h3 := coneProfile_lt hK η₂
  have h4 := coneProfile_lt hK η₁
  unfold innerCofactor
  have e1 : 0 < coneProfile K η₂ + coneProfile K η₁ + 3 := by linarith
  have e2 : 0 < 9 - (coneProfile K η₂ - coneProfile K η₁) ^ 2 := by nlinarith
  have e3 : 0 < 2 * (η₁ * η₂ + K) / ((η₂ ^ 2 + K) * (η₁ ^ 2 + K)) := by positivity
  positivity

theorem three_halves_ne {b : ℝ} (hb : b = 3 / 2 ∨ b = -(3 / 2)) : (0 : ℝ) ≠ b := by
  rcases hb with rfl | rfl <;> norm_num

theorem norm_outerBridge (hK : 0 < K) {b y η w q : ℝ} (hb : b = 3 / 2 ∨ b = -(3 / 2))
    (hy : 0 < y) (hη : 0 < η) (hq : 0 < q) (hd : η - y = w ^ 2 * q) :
    ‖outerBridge K b y η w q‖ = 3 / 2 + coneProfile K y := by
  have h := norm_twoCircle_sub_left (three_halves_ne hb)
    (outerCofactor_pos hK hb hy hη hq).le
    (by linarith [half_le_coneProfile hK y]) (outerBridge_heron hK hb hd)
  simpa [outerBridge] using h

theorem norm_outerBridge_sub (hK : 0 < K) {b y η w q : ℝ} (hb : b = 3 / 2 ∨ b = -(3 / 2))
    (hy : 0 < y) (hη : 0 < η) (hq : 0 < q) (hd : η - y = w ^ 2 * q) :
    ‖outerBridge K b y η w q - b‖ = coneProfile K η :=
  norm_twoCircle_sub_right (three_halves_ne hb) (outerCofactor_pos hK hb hy hη hq).le
    (by linarith [half_le_coneProfile hK η]) (outerBridge_heron hK hb hd)

theorem norm_innerBridge_sub (hK : 0 < K) {η₂ η₁ w q : ℝ} (hη₂ : 0 < η₂) (hη₁ : 0 < η₁)
    (hq : 0 < q) (hd : η₁ * η₂ - K = w ^ 2 * q) :
    ‖innerBridge K η₂ η₁ w q - 3 / 2‖ = coneProfile K η₂ := by
  have h := norm_twoCircle_sub_left (a := 3 / 2) (b := -(3 / 2)) (by norm_num)
    (innerCofactor_pos hK hη₂ hη₁ hq).le (by linarith [half_le_coneProfile hK η₂])
    (innerBridge_heron hK hd)
  simpa [innerBridge] using h

theorem norm_innerBridge_add (hK : 0 < K) {η₂ η₁ w q : ℝ} (hη₂ : 0 < η₂) (hη₁ : 0 < η₁)
    (hq : 0 < q) (hd : η₁ * η₂ - K = w ^ 2 * q) :
    ‖innerBridge K η₂ η₁ w q + 3 / 2‖ = coneProfile K η₁ := by
  have h := norm_twoCircle_sub_right (a := 3 / 2) (b := -(3 / 2)) (by norm_num)
    (innerCofactor_pos hK hη₂ hη₁ hq).le (by linarith [half_le_coneProfile hK η₁])
    (innerBridge_heron hK hd)
  simpa [innerBridge, sub_neg_eq_add] using h

theorem outerBridge_neg (K b y η w q : ℝ) :
    outerBridge K b y η (-w) q = conj (outerBridge K b y η w q) :=
  twoCircle_neg _ _ _ _ _ _

theorem innerBridge_neg (K η₂ η₁ w q : ℝ) :
    innerBridge K η₂ η₁ (-w) q = conj (innerBridge K η₂ η₁ w q) :=
  twoCircle_neg _ _ _ _ _ _

theorem outerBridge_im_pos (hK : 0 < K) {b y η w q : ℝ} (hb : b = 3 / 2 ∨ b = -(3 / 2))
    (hy : 0 < y) (hη : 0 < η) (hq : 0 < q) (hw : 0 < w) :
    0 < (outerBridge K b y η w q).im :=
  twoCircle_im_pos (three_halves_ne hb) hw (outerCofactor_pos hK hb hy hη hq)

theorem innerBridge_im_pos (hK : 0 < K) {η₂ η₁ w q : ℝ} (hη₂ : 0 < η₂) (hη₁ : 0 < η₁)
    (hq : 0 < q) (hw : 0 < w) : 0 < (innerBridge K η₂ η₁ w q).im :=
  twoCircle_im_pos (by norm_num) hw (innerCofactor_pos hK hη₂ hη₁ hq)

theorem outerBridge_re_mul_pos (hK : 0 < K) {b y η w q : ℝ} (hb : b = 3 / 2 ∨ b = -(3 / 2))
    (hy : 0 < y) : 0 < b * (outerBridge K b y η w q).re := by
  have h1 := half_lt_coneProfile hK hy.ne'
  have h2 := coneProfile_lt hK η
  have h3 := half_le_coneProfile hK η
  have hb2 : b ^ 2 = 9 / 4 := by rcases hb with rfl | rfl <;> norm_num
  have hb0 : b ≠ 0 := (three_halves_ne hb).symm
  rw [outerBridge, twoCircle_re, sub_zero, zero_add]
  rw [show b * (((3 / 2 + coneProfile K y) ^ 2 - coneProfile K η ^ 2 + b ^ 2) / (2 * b)) =
    ((3 / 2 + coneProfile K y) ^ 2 - coneProfile K η ^ 2 + b ^ 2) / 2 by field_simp]
  nlinarith

theorem two_lt_norm_outerBridge (hK : 0 < K) {b y η w q : ℝ} (hb : b = 3 / 2 ∨ b = -(3 / 2))
    (hy : 0 < y) (hη : 0 < η) (hq : 0 < q) (hd : η - y = w ^ 2 * q) :
    2 < ‖outerBridge K b y η w q‖ := by
  rw [norm_outerBridge hK hb hy hη hq hd]
  linarith [half_lt_coneProfile hK hy.ne']

theorem norm_innerBridge_lt_two (hK : 0 < K) {η₂ η₁ w q : ℝ} (hη₂ : 0 < η₂) (hη₁ : 0 < η₁)
    (hq : 0 < q) (hd : η₁ * η₂ - K = w ^ 2 * q) : ‖innerBridge K η₂ η₁ w q‖ < 2 := by
  have h1 := norm_innerBridge_sub hK hη₂ hη₁ hq hd
  have h2 := norm_innerBridge_add hK hη₂ hη₁ hq hd
  have h3 := coneProfile_lt hK η₂
  have h4 := coneProfile_lt hK η₁
  set u := innerBridge K η₂ η₁ w q
  have hpar : 2 * ‖u‖ ^ 2 = ‖u - 3 / 2‖ ^ 2 + ‖u + 3 / 2‖ ^ 2 - 9 / 2 := by
    simp only [Complex.sq_norm, normSq_apply, sub_re, add_re, sub_im, add_im]
    norm_num
    ring
  rw [h1, h2] at hpar
  have h5 := half_le_coneProfile hK η₂
  have h6 := half_le_coneProfile hK η₁
  nlinarith [norm_nonneg u]

theorem contDiffAt_outerBridge (hK : 0 < K) {b : ℝ} (hb : b = 3 / 2 ∨ b = -(3 / 2))
    {fy fη fw fq : ℂ → ℝ} {z : ℂ} (hy : ContDiffAt ℝ ∞ fy z) (hη : ContDiffAt ℝ ∞ fη z)
    (hw : ContDiffAt ℝ ∞ fw z) (hq : ContDiffAt ℝ ∞ fq z) (hy0 : 0 < fy z) (hη0 : 0 < fη z)
    (hq0 : 0 < fq z) :
    ContDiffAt ℝ ∞ (fun u => outerBridge K b (fy u) (fη u) (fw u) (fq u)) z := by
  have hG := contDiff_coneProfile hK
  have hA : ContDiffAt ℝ ∞ (fun u => 3 / 2 + coneProfile K (fy u)) z :=
    contDiffAt_const.add (hG.contDiffAt.comp z hy)
  have hB : ContDiffAt ℝ ∞ (fun u => coneProfile K (fη u)) z := hG.contDiffAt.comp z hη
  have hd : ∀ u, (fη u ^ 2 + K) * (fy u ^ 2 + K) ≠ 0 := fun u => by positivity
  have h1 : ContDiffAt ℝ ∞
      (fun u => (3 / 2 + coneProfile K (fy u) + coneProfile K (fη u)) ^ 2 - b ^ 2) z :=
    ((hA.add hB).pow 2).sub contDiffAt_const
  have h2 : ContDiffAt ℝ ∞
      (fun u => |b| + 3 / 2 + coneProfile K (fy u) - coneProfile K (fη u)) z :=
    (contDiffAt_const.add (hG.contDiffAt.comp z hy)).sub hB
  have h3 : ContDiffAt ℝ ∞
      (fun u => 2 * K * (fη u + fy u) / ((fη u ^ 2 + K) * (fy u ^ 2 + K))) z :=
    (contDiffAt_const.mul (hη.add hy)).div ((hη.pow 2 |>.add contDiffAt_const).mul
      (hy.pow 2 |>.add contDiffAt_const)) (hd z)
  have hP : ContDiffAt ℝ ∞ (fun u => outerCofactor K b (fy u) (fη u) (fq u)) z :=
    (h1.mul h2).mul (hq.mul h3)
  exact contDiffAt_twoCircle hA hB hw hP (outerCofactor_pos hK hb hy0 hη0 hq0)
    (three_halves_ne hb)

theorem contDiffAt_innerBridge (hK : 0 < K) {fη₂ fη₁ fw fq : ℂ → ℝ} {z : ℂ}
    (hη₂ : ContDiffAt ℝ ∞ fη₂ z) (hη₁ : ContDiffAt ℝ ∞ fη₁ z) (hw : ContDiffAt ℝ ∞ fw z)
    (hq : ContDiffAt ℝ ∞ fq z) (hη₂0 : 0 < fη₂ z) (hη₁0 : 0 < fη₁ z) (hq0 : 0 < fq z) :
    ContDiffAt ℝ ∞ (fun u => innerBridge K (fη₂ u) (fη₁ u) (fw u) (fq u)) z := by
  have hG := contDiff_coneProfile hK
  have hA : ContDiffAt ℝ ∞ (fun u => coneProfile K (fη₂ u)) z := hG.contDiffAt.comp z hη₂
  have hB : ContDiffAt ℝ ∞ (fun u => coneProfile K (fη₁ u)) z := hG.contDiffAt.comp z hη₁
  have hP : ContDiffAt ℝ ∞ (fun u => innerCofactor K (fη₂ u) (fη₁ u) (fq u)) z := by
    unfold innerCofactor
    have hd : ∀ u, (fη₂ u ^ 2 + K) * (fη₁ u ^ 2 + K) ≠ 0 := fun u => by positivity
    exact (((hA.add hB).add contDiffAt_const).mul (contDiffAt_const.sub ((hA.sub hB).pow 2))).mul
      (hq.mul ((contDiffAt_const.mul ((hη₁.mul hη₂).add contDiffAt_const)).div
        ((hη₂.pow 2 |>.add contDiffAt_const).mul (hη₁.pow 2 |>.add contDiffAt_const)) (hd z)))
  exact contDiffAt_twoCircle hA hB hw hP (innerCofactor_pos hK hη₂0 hη₁0 hq0) (by norm_num)

end GC.Seifert

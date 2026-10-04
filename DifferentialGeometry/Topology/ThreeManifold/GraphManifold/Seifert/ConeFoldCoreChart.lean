import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldOneConeInjective

/-!
# The disc chart of the Jordan core of the cone fold

Lane A4b2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §7 and erratum
7). The Jordan core of the layout is handled in the disc chart
`coreMap z = coneDisc ζ_h (fermiChart z)`, `ζ_h = coreHyp = -201/1000 + 49/50 i`, a Möbius
isometry of the upper half-plane onto the unit disc (`coreInv` is its inverse,
`coreMap_coreInv`, `coreInv_coreMap`, both with nonvanishing complex derivative). Concentric
circles of the chart are hyperbolic circles about `chartInv ζ_h`:
* the disc `‖w‖ < 17/200` contains the inner Euclidean core of `SF/ConeFoldLayout.lean`
  (`le_norm_of_inner_core`), so outside it the local forms of the assembled fold apply;
* the disc `‖w‖ ≤ 89/1000` lies in the outer Euclidean core (`outer_core_of_norm_le`), hence in the
  open triangle.
The triangle is star-shaped about `0` in the chart (`coreInv_smul_mem_triangle`): each wall is a
half-plane `A|ζ|² + B Re ζ + C ≥ 0` positive at `ζ_h`, and along a chart ray such a function
times `|1 - w|²` is a convex quadratic in the radius with positive value at `0`
(`wall_discInv`, `star_quadratic`). Consequently the triangle minus the closed chart disc of
radius `87/1000` is preconnected (`isPreconnected_coreOut`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set Metric
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

/-! ### Möbius inverses -/

def discInv (a w : ℂ) : ℂ := (a - conj a * w) / (1 - w)

theorem one_sub_ne_of_norm_lt' {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := one_sub_ne_of_norm_lt hw

theorem discInv_im (a : ℂ) {w : ℂ} (hw : ‖w‖ < 1) :
    (discInv a w).im = a.im * (1 - normSq w) / normSq (1 - w) := by
  have h1 := one_sub_ne_of_norm_lt hw
  have hn : normSq (1 - w) ≠ 0 := normSq_eq_zero.not.2 h1
  rw [discInv, div_im]
  simp only [sub_im, sub_re, mul_im, mul_re, conj_re, conj_im, one_re, one_im]
  rw [normSq_apply, normSq_apply] at *
  field_simp
  ring

theorem discInv_im_pos {a w : ℂ} (ha : 0 < a.im) (hw : ‖w‖ < 1) : 0 < (discInv a w).im := by
  rw [discInv_im a hw]
  have h1 : normSq w < 1 := by
    rw [← Complex.sq_norm]; nlinarith [norm_nonneg w]
  have h2 : 0 < normSq (1 - w) := normSq_pos.2 (one_sub_ne_of_norm_lt hw)
  apply div_pos _ h2
  nlinarith

theorem coneDisc_discInv {a w : ℂ} (ha : 0 < a.im) (hw : ‖w‖ < 1) :
    coneDisc a (discInv a w) = w := by
  have h1 := one_sub_ne_of_norm_lt hw
  have h2 : a - conj a ≠ 0 := sub_conj_self_ne ha
  unfold coneDisc discInv
  have e1 : (a - conj a * w) / (1 - w) - a = w * (a - conj a) / (1 - w) := by
    field_simp; ring
  have e2 : (a - conj a * w) / (1 - w) - conj a = (a - conj a) / (1 - w) := by
    field_simp; ring
  rw [e1, e2]
  field_simp

theorem discInv_coneDisc {a ζ : ℂ} (ha : 0 < a.im) (hζ : 0 < ζ.im) :
    discInv a (coneDisc a ζ) = ζ := by
  have e := mul_one_sub_coneDisc ha hζ
  have h1 : 1 - coneDisc a ζ ≠ 0 := one_sub_ne_of_norm_lt (norm_coneDisc_lt_one ha hζ)
  rw [discInv, ← e, mul_div_cancel_right₀ _ h1]

theorem hasDerivAt_discInv (a : ℂ) {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (discInv a) ((a - conj a) / (1 - w) ^ 2) w := by
  have h1 := one_sub_ne_of_norm_lt hw
  have hn : HasDerivAt (fun x : ℂ => a - conj a * x) (0 - conj a * 1) w :=
    (hasDerivAt_const w a).sub ((hasDerivAt_id' w).const_mul (conj a))
  have hd : HasDerivAt (fun x : ℂ => 1 - x) (0 - 1) w :=
    (hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id' w)
  have h := hn.div hd h1
  unfold discInv
  convert h using 1
  field_simp
  ring

theorem wall_discInv (A B C : ℝ) (a : ℂ) {w : ℂ} (hw : w ≠ 1) :
    (A * normSq (discInv a w) + B * (discInv a w).re + C) * normSq (1 - w) =
      (A * normSq a + B * a.re + C) * (1 + normSq w) -
        2 * (conj w * (A * a ^ 2 + B * a + C)).re := by
  have h1 : 1 - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
  have hn : normSq (1 - w) ≠ 0 := normSq_eq_zero.not.2 h1
  rw [discInv, normSq_div, div_re]
  field_simp
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im,
    add_re, add_im, ofReal_re, ofReal_im]
  ring

theorem star_quadratic {s₀ m R t : ℝ} (hs : 0 < s₀) (hm0 : 0 ≤ m) (hm : m < 1)
    (h1 : 0 ≤ s₀ * (1 + m) - 2 * R) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ s₀ * (1 + t ^ 2 * m) - 2 * (t * R) := by
  have e : s₀ * (1 + t ^ 2 * m) - 2 * (t * R) =
      t * (s₀ * (1 + m) - 2 * R) + (1 - t) * s₀ * (1 - m * t) := by ring
  rw [e]
  have : 0 ≤ (1 - t) * s₀ * (1 - m * t) := by
    apply mul_nonneg (mul_nonneg (by linarith) hs.le)
    nlinarith
  nlinarith [mul_nonneg ht0 h1]

theorem wall_discInv_smul_nonneg {A B C : ℝ} {a w : ℂ}
    (hpos : 0 < A * normSq a + B * a.re + C) (hw : ‖w‖ < 1)
    (h : 0 ≤ A * normSq (discInv a w) + B * (discInv a w).re + C) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    0 ≤ A * normSq (discInv a ((t : ℂ) * w)) + B * (discInv a ((t : ℂ) * w)).re + C := by
  have hw1 : w ≠ 1 := fun h' => by rw [h'] at hw; simp at hw
  have htw : ‖(t : ℂ) * w‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    nlinarith [norm_nonneg w]
  have htw1 : (t : ℂ) * w ≠ 1 := fun h' => by rw [h'] at htw; simp at htw
  have e1 := wall_discInv A B C a hw1
  have e2 := wall_discInv A B C a htw1
  have hn1 : 0 < normSq (1 - w) := normSq_pos.2 (sub_ne_zero.2 (Ne.symm hw1))
  have hn2 : 0 < normSq (1 - (t : ℂ) * w) := normSq_pos.2 (sub_ne_zero.2 (Ne.symm htw1))
  have hm : normSq w < 1 := by rw [← Complex.sq_norm]; nlinarith [norm_nonneg w]
  have key : 0 ≤ (A * normSq (discInv a ((t : ℂ) * w)) + B * (discInv a ((t : ℂ) * w)).re + C) *
      normSq (1 - (t : ℂ) * w) := by
    rw [e2]
    have hconj : conj ((t : ℂ) * w) = (t : ℂ) * conj w := by simp
    have hnorm : normSq ((t : ℂ) * w) = t ^ 2 * normSq w := by
      rw [normSq_mul, normSq_ofReal]; ring
    rw [hconj, hnorm, mul_assoc, re_ofReal_mul]
    have h1' : 0 ≤ (A * normSq a + B * a.re + C) * (1 + normSq w) -
        2 * (conj w * (A * a ^ 2 + B * a + C)).re := by
      rw [← e1]; exact mul_nonneg h hn1.le
    exact star_quadratic hpos (normSq_nonneg w) hm h1' ht0 ht1
  exact nonneg_of_mul_nonneg_left key hn2

namespace ConeShape

variable (σ : ConeShape)

/-! ### The inverse of the Fermi chart -/

def chartInv (ζ : ℂ) : ℂ :=
  ((σ.rightFoot : ℂ) * ζ + σ.chartScale * σ.leftFoot) / (ζ + σ.chartScale)

theorem rightFoot_sub_leftFoot : σ.rightFoot - σ.leftFoot = 1 / 2 := by
  unfold rightFoot leftFoot; ring

theorem add_chartScale_ne {ζ : ℂ} (hζ : 0 < ζ.im) : ζ + σ.chartScale ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem chartInv_im {ζ : ℂ} (hζ : 0 < ζ.im) :
    (σ.chartInv ζ).im = σ.chartScale * (1 / 2) * ζ.im / normSq (ζ + σ.chartScale) := by
  have h := σ.add_chartScale_ne hζ
  have hn : normSq (ζ + σ.chartScale) ≠ 0 := normSq_eq_zero.not.2 h
  rw [chartInv, div_im]
  simp only [add_im, add_re, mul_im, mul_re, ofReal_re, ofReal_im]
  rw [← σ.rightFoot_sub_leftFoot]
  rw [normSq_apply] at hn ⊢
  field_simp
  ring

theorem chartInv_im_pos {ζ : ℂ} (hζ : 0 < ζ.im) : 0 < (σ.chartInv ζ).im := by
  rw [σ.chartInv_im hζ]
  have := σ.chartScale_pos
  have := normSq_pos.2 (σ.add_chartScale_ne hζ)
  positivity

theorem fermiChart_chartInv {ζ : ℂ} (hζ : 0 < ζ.im) : σ.fermiChart (σ.chartInv ζ) = ζ := by
  have h := σ.add_chartScale_ne hζ
  have hk : (σ.chartScale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 σ.chartScale_pos.ne'
  have hd : ((σ.rightFoot : ℂ) - σ.leftFoot) ≠ 0 := by
    rw [← Complex.ofReal_sub, σ.rightFoot_sub_leftFoot]; norm_num
  unfold fermiChart chartInv
  have e1 : ((σ.rightFoot : ℂ) * ζ + σ.chartScale * σ.leftFoot) / (ζ + σ.chartScale) - σ.leftFoot =
      ζ * ((σ.rightFoot : ℂ) - σ.leftFoot) / (ζ + σ.chartScale) := by field_simp; ring
  have e2 : (σ.rightFoot : ℂ) - ((σ.rightFoot : ℂ) * ζ + σ.chartScale * σ.leftFoot) /
      (ζ + σ.chartScale) =
        σ.chartScale * ((σ.rightFoot : ℂ) - σ.leftFoot) / (ζ + σ.chartScale) := by
    field_simp; ring
  rw [e1, e2]
  field_simp

theorem chartInv_fermiChart {z : ℂ} (hz : 0 < z.im) : σ.chartInv (σ.fermiChart z) = z := by
  have h1 := σ.rightFoot_sub_ne hz
  have hk : (σ.chartScale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 σ.chartScale_pos.ne'
  have hd : ((σ.rightFoot : ℂ) - σ.leftFoot) ≠ 0 := by
    rw [← Complex.ofReal_sub, σ.rightFoot_sub_leftFoot]; norm_num
  unfold fermiChart chartInv
  have e1 : (σ.chartScale : ℂ) * (z - σ.leftFoot) / (σ.rightFoot - z) + σ.chartScale =
      σ.chartScale * ((σ.rightFoot : ℂ) - σ.leftFoot) / (σ.rightFoot - z) := by field_simp; ring
  rw [e1]
  field_simp
  ring

theorem hasDerivAt_fermiChart {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt σ.fermiChart
      (σ.chartScale * ((σ.rightFoot : ℂ) - σ.leftFoot) / ((σ.rightFoot : ℂ) - z) ^ 2) z := by
  have h1 := σ.rightFoot_sub_ne hz
  have hn : HasDerivAt (fun x : ℂ => (σ.chartScale : ℂ) * (x - σ.leftFoot))
      (σ.chartScale * (1 - 0)) z :=
    ((hasDerivAt_id' z).sub (hasDerivAt_const z (σ.leftFoot : ℂ))).const_mul _
  have hd : HasDerivAt (fun x : ℂ => (σ.rightFoot : ℂ) - x) (0 - 1) z :=
    (hasDerivAt_const z (σ.rightFoot : ℂ)).sub (hasDerivAt_id' z)
  have h := hn.div hd h1
  unfold fermiChart
  convert h using 1
  field_simp
  ring

theorem hasDerivAt_chartInv {ζ : ℂ} (hζ : 0 < ζ.im) :
    HasDerivAt σ.chartInv
      (σ.chartScale * ((σ.rightFoot : ℂ) - σ.leftFoot) / (ζ + σ.chartScale) ^ 2) ζ := by
  have h1 := σ.add_chartScale_ne hζ
  have hn : HasDerivAt (fun x : ℂ => (σ.rightFoot : ℂ) * x + σ.chartScale * σ.leftFoot)
      (σ.rightFoot * 1 + 0) ζ :=
    ((hasDerivAt_id' ζ).const_mul _).add (hasDerivAt_const ζ _)
  have hd : HasDerivAt (fun x : ℂ => x + σ.chartScale) (1 + 0) ζ :=
    (hasDerivAt_id' ζ).add (hasDerivAt_const ζ _)
  have h := hn.div hd h1
  unfold chartInv
  convert h using 1
  field_simp
  ring

end ConeShape

/-! ### The core chart -/

namespace ConeLayout

def coreHyp : ℂ := ⟨-(201 / 1000), 49 / 50⟩

theorem coreHyp_im_pos : 0 < coreHyp.im := by
  simp [coreHyp]

end ConeLayout

open ConeLayout

namespace ConeShape

variable (σ : ConeShape)

def coreMap (z : ℂ) : ℂ := coneDisc coreHyp (σ.fermiChart z)

def coreInv (w : ℂ) : ℂ := σ.chartInv (discInv coreHyp w)

theorem norm_coreMap_lt_one {z : ℂ} (hz : 0 < z.im) : ‖σ.coreMap z‖ < 1 :=
  norm_coneDisc_lt_one coreHyp_im_pos (σ.fermiChart_im_pos hz)

theorem coreInv_im_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (σ.coreInv w).im :=
  σ.chartInv_im_pos (discInv_im_pos coreHyp_im_pos hw)

theorem coreMap_coreInv {w : ℂ} (hw : ‖w‖ < 1) : σ.coreMap (σ.coreInv w) = w := by
  rw [coreMap, coreInv, σ.fermiChart_chartInv (discInv_im_pos coreHyp_im_pos hw),
    coneDisc_discInv coreHyp_im_pos hw]

theorem coreInv_coreMap {z : ℂ} (hz : 0 < z.im) : σ.coreInv (σ.coreMap z) = z := by
  rw [coreMap, coreInv, discInv_coneDisc coreHyp_im_pos (σ.fermiChart_im_pos hz),
    σ.chartInv_fermiChart hz]

theorem hasDerivAt_coreMap {z : ℂ} (hz : 0 < z.im) :
    ∃ d : ℂ, d ≠ 0 ∧ HasDerivAt σ.coreMap d z := by
  have hY := σ.fermiChart_im_pos hz
  have h1 := σ.hasDerivAt_fermiChart hz
  have h2 := hasDerivAt_coneDisc coreHyp_im_pos hY
  refine ⟨_, ?_, h2.comp z h1⟩
  have hk : (σ.chartScale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 σ.chartScale_pos.ne'
  have hd : ((σ.rightFoot : ℂ) - σ.leftFoot) ≠ 0 := by
    rw [← Complex.ofReal_sub, σ.rightFoot_sub_leftFoot]; norm_num
  apply mul_ne_zero
  · exact div_ne_zero (sub_conj_self_ne coreHyp_im_pos)
      (pow_ne_zero 2 (sub_conj_ne_zero coreHyp_im_pos hY))
  · exact div_ne_zero (mul_ne_zero hk hd) (pow_ne_zero 2 (σ.rightFoot_sub_ne hz))

theorem hasDerivAt_coreInv {w : ℂ} (hw : ‖w‖ < 1) :
    ∃ d : ℂ, d ≠ 0 ∧ HasDerivAt σ.coreInv d w := by
  have hζ := discInv_im_pos coreHyp_im_pos hw
  have h1 := hasDerivAt_discInv coreHyp hw
  have h2 := σ.hasDerivAt_chartInv hζ
  refine ⟨_, ?_, h2.comp w h1⟩
  have hk : (σ.chartScale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 σ.chartScale_pos.ne'
  have hd : ((σ.rightFoot : ℂ) - σ.leftFoot) ≠ 0 := by
    rw [← Complex.ofReal_sub, σ.rightFoot_sub_leftFoot]; norm_num
  apply mul_ne_zero
  · exact div_ne_zero (mul_ne_zero hk hd) (pow_ne_zero 2 (σ.add_chartScale_ne hζ))
  · exact div_ne_zero (sub_conj_self_ne coreHyp_im_pos)
      (pow_ne_zero 2 (one_sub_ne_of_norm_lt hw))

theorem contDiffAt_coreMap {z : ℂ} (hz : 0 < z.im) : ContDiffAt ℝ ∞ σ.coreMap z := by
  have hY := σ.fermiChart_im_pos hz
  have h1 : ContDiffAt ℂ ∞ σ.fermiChart z := by
    have h1 := σ.rightFoot_sub_ne hz
    unfold fermiChart
    exact (contDiffAt_const.mul (contDiffAt_id.sub contDiffAt_const)).div
      (contDiffAt_const.sub contDiffAt_id) h1
  exact ((contDiffAt_coneDisc coreHyp_im_pos hY).comp z h1).restrict_scalars ℝ

theorem contDiffAt_coreInv {w : ℂ} (hw : ‖w‖ < 1) : ContDiffAt ℝ ∞ σ.coreInv w := by
  have hζ := discInv_im_pos coreHyp_im_pos hw
  have h1 : ContDiffAt ℂ ∞ (discInv coreHyp) w := by
    unfold discInv
    exact (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)).div
      (contDiffAt_const.sub contDiffAt_id) (one_sub_ne_of_norm_lt hw)
  have h2 : ContDiffAt ℂ ∞ σ.chartInv (discInv coreHyp w) := by
    unfold chartInv
    exact ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const).div
      (contDiffAt_id.add contDiffAt_const) (σ.add_chartScale_ne hζ)
  exact (h2.comp w h1).restrict_scalars ℝ

theorem continuousOn_coreInv : ContinuousOn σ.coreInv (ball 0 1) := fun w hw =>
  (σ.contDiffAt_coreInv (by simpa using hw)).continuousAt.continuousWithinAt

theorem det_fderiv_coreMap_pos {z : ℂ} (hz : 0 < z.im) : 0 < (fderiv ℝ σ.coreMap z).det := by
  obtain ⟨d, hd, h⟩ := σ.hasDerivAt_coreMap hz
  rw [det_fderiv_of_hasDerivAt h]
  exact normSq_pos.2 hd

theorem det_fderiv_coreInv_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (fderiv ℝ σ.coreInv w).det := by
  obtain ⟨d, hd, h⟩ := σ.hasDerivAt_coreInv hw
  rw [det_fderiv_of_hasDerivAt h]
  exact normSq_pos.2 hd

theorem coreInv_injOn : InjOn σ.coreInv (ball 0 1) := by
  intro w hw w' hw' h
  have := congrArg σ.coreMap h
  rwa [σ.coreMap_coreInv (by simpa using hw), σ.coreMap_coreInv (by simpa using hw')] at this

theorem coreMap_injOn {z z' : ℂ} (hz : 0 < z.im) (hz' : 0 < z'.im)
    (h : σ.coreMap z = σ.coreMap z') : z = z' := by
  have := congrArg σ.coreInv h
  rwa [σ.coreInv_coreMap hz, σ.coreInv_coreMap hz'] at this

end ConeShape

/-! ### Comparison with the Euclidean core discs -/

namespace ConeLayout

theorem normSq_coneDisc_coreHyp (ζ : ℂ) :
    normSq (coneDisc coreHyp ζ) =
      ((ζ.re + 201 / 1000) ^ 2 + (ζ.im - 49 / 50) ^ 2) /
        ((ζ.re + 201 / 1000) ^ 2 + (ζ.im + 49 / 50) ^ 2) := by
  rw [normSq_coneDisc, normSq_apply, normSq_apply]
  simp [coreHyp]
  ring_nf

theorem denom_pos {ζ : ℂ} (hζ : 0 < ζ.im) :
    0 < (ζ.re + 201 / 1000) ^ 2 + (ζ.im + 49 / 50) ^ 2 := by positivity

theorem norm_lt_of_inner_core {ζ : ℂ} (hζ : 0 < ζ.im)
    (h : normSq (ζ - coreCentre) < coreInner ^ 2) : ‖coneDisc coreHyp ζ‖ < 17 / 200 := by
  rw [normSq_sub_coreCentre, coreInner] at h
  have hsq : normSq (coneDisc coreHyp ζ) < (17 / 200) ^ 2 := by
    rw [normSq_coneDisc_coreHyp, div_lt_iff₀ (denom_pos hζ)]
    have hY : 828 / 1000 < ζ.im := by nlinarith [sq_nonneg (-ζ.re - 201 / 1000)]
    nlinarith [sq_nonneg (ζ.re + 201 / 1000)]
  rw [← Complex.sq_norm] at hsq
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

theorem le_norm_of_inner_core {ζ : ℂ} (hζ : 0 < ζ.im)
    (h : 17 / 200 ≤ ‖coneDisc coreHyp ζ‖) : coreInner ^ 2 ≤ normSq (ζ - coreCentre) := by
  by_contra hlt
  push Not at hlt
  have := norm_lt_of_inner_core hζ hlt
  linarith

theorem outer_core_of_norm_le {ζ : ℂ} (hζ : 0 < ζ.im) (h : ‖coneDisc coreHyp ζ‖ ≤ 89 / 1000) :
    normSq (ζ - coreCentre) ≤ coreOuter ^ 2 := by
  have hsq : normSq (coneDisc coreHyp ζ) ≤ (89 / 1000) ^ 2 := by
    rw [← Complex.sq_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [normSq_coneDisc_coreHyp, div_le_iff₀ (denom_pos hζ)] at hsq
  rw [normSq_sub_coreCentre, coreOuter]
  have hY : ζ.im ≤ 6 / 5 := by nlinarith [sq_nonneg (ζ.re + 201 / 1000)]
  nlinarith [sq_nonneg (ζ.re + 201 / 1000)]

end ConeLayout

namespace ConeShape

variable (σ : ConeShape)

theorem outer_core_of_coreMap_le {z : ℂ} (hz : 0 < z.im) (h : ‖σ.coreMap z‖ ≤ 89 / 1000) :
    normSq (σ.fermiChart z - coreCentre) ≤ coreOuter ^ 2 :=
  outer_core_of_norm_le (σ.fermiChart_im_pos hz) h

theorem inner_core_of_coreMap {z : ℂ} (hz : 0 < z.im) (h : 17 / 200 ≤ ‖σ.coreMap z‖) :
    coreInner ^ 2 ≤ normSq (σ.fermiChart z - coreCentre) :=
  le_norm_of_inner_core (σ.fermiChart_im_pos hz) h

theorem mem_triangle_of_coreMap_le (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
    (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂) {z : ℂ} (hz : 0 < z.im)
    (h : ‖σ.coreMap z‖ ≤ 89 / 1000) :
    z ∈ σ.triangle ∧ 0 < σ.wallSide 0 z ∧ 0 < σ.wallSide 1 z ∧ 0 < σ.wallSide 2 z := by
  obtain ⟨h0, h1, h2⟩ := σ.wallSide_pos_of_outer_core h₁ h₂ hz (σ.outer_core_of_coreMap_le hz h)
  have h2' : 0 < σ.wallSide 2 z := by
    have h3 : 0 < σ.sinhN z := by linarith
    unfold sinhN at h3
    have h4 := mul_pos h3 hz
    rw [div_mul_cancel₀ _ hz.ne'] at h4
    linarith
  refine ⟨⟨hz, fun i => ?_⟩, h0, h1, h2'⟩
  fin_cases i
  · exact h0.le
  · exact h1.le
  · exact h2'.le

end ConeShape

end GC.Seifert

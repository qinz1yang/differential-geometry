import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypScrews

/-!
# The fibre gauge of the `SL₂~` connection model in the disc chart

Lane B3b (design `docs/geometrization/handoffs/20261004-design-b3c-hyperbolic-rows.md`, §2 (H3)
and §4). For the connection model `SL₂~` (`hyperbolicProfile 1`) the fibre coordinate of the
hyperboloid chart is shifted by `γ(Z) = 2 arctan(Re Z/(Im Z + 1))` of the upper half-plane
coordinate `Z = uhp x` (`hyperboloidInv_one_two`, `hyperboloidMap_one_two`). X14's recentring at
`v` acts on `Z` by `Z ↦ A Z + B` (`A = hypShiftA v > 0`, `B = hypShiftB v`,
`uhp_recentre_universalSL2`) and on the fibre by `t ↦ t + v₂ - γ(uhp v) - γ(Z) + γ(A Z + B)`
(`recentre_universalSL2_two`). Hence the inverse recentring lowers the fibre coordinate by the
gauge `gaugeU v Z = γ Z - γ((Z - B)/A) - γ(uhp v) + v₂` of the base point
(`recentre_symm_universalSL2_two`), and the clockwise screw about the fibre over `v` raises it by
the gauge difference (`screwAt_universalSL2_two_gaugeU`, `screwAt_universalSL2_two_gauge`), with
`gauge v w = gaugeU v (cayInv w)` on the disc (`gauge_hb`). The gauge is smooth on the open disc
(`contDiffOn_gauge`) and vanishes at the base point of a centre of zero height (`gauge_hb_self`).
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

namespace ClosedTriangle

namespace Hyp

open GC.Geometry

def gam (Z : ℂ) : ℝ := 2 * Real.arctan (Z.re / (Z.im + 1))

theorem uhp_re (x : ModelCoordinates) : (uhp x).re = hyperboloidInv 0 x 0 := by
  simp [uhp]

theorem uhp_im (x : ModelCoordinates) : (uhp x).im = Real.exp (hyperboloidInv 0 x 1) := by
  simp [uhp, Complex.exp_ofReal_re]

theorem hyperboloidInv_one_two (x : ModelCoordinates) :
    hyperboloidInv 1 x 2 = x 2 - gam (uhp x) := by
  have hd := hyperboloidHeight_sub_pos x
  have hre : (uhp x).re = x 0 / (hyperboloidHeight x - x 1) := by
    rw [uhp_re]; simp [hyperboloidInv]
  have him : (uhp x).im = 1 / (hyperboloidHeight x - x 1) := by
    rw [uhp_im]
    simp [hyperboloidInv, Real.exp_neg, Real.exp_log hd]
  rw [gam, hre, him]
  have : x 0 / (hyperboloidHeight x - x 1) / (1 / (hyperboloidHeight x - x 1) + 1) =
      x 0 / (1 + (hyperboloidHeight x - x 1)) := by
    field_simp
  rw [this]
  simp [hyperboloidInv]

theorem hyperboloidMap_one_two (g : ModelCoordinates) :
    hyperboloidMap 1 g 2 = g 2 + gam ((g 0 : ℂ) + I * (Real.exp (g 1) : ℂ)) := by
  simp [hyperboloidMap, gam, Complex.exp_ofReal_re]

theorem uhp_hyperboloidMap (l : ℝ) (g : ModelCoordinates) :
    uhp (hyperboloidMap l g) = (g 0 : ℂ) + I * (Real.exp (g 1) : ℂ) := by
  have h := hyperboloidInv_hyperboloidMap l g
  have h0 : hyperboloidInv 0 (hyperboloidMap l g) 0 = g 0 := by
    rw [(hyperboloidInv_base l _).1.symm, h]
  have h1 : hyperboloidInv 0 (hyperboloidMap l g) 1 = g 1 := by
    rw [(hyperboloidInv_base l _).2.symm, h]
  rw [uhp, h0, h1]

theorem hyperboloidInv_one_base (v : ModelCoordinates) :
    hyperboloidInv 1 v 0 = hypShiftB v ∧ Real.exp (hyperboloidInv 1 v 1) = hypShiftA v := by
  have h := hyperboloidInv_base 1 v
  exact ⟨h.1, by rw [h.2]; rfl⟩

theorem uhp_recentre_universalSL2 (hm : ConnectionModel.universalSL2.baseCurvature ≤ 0)
    (v x : ModelCoordinates) :
    uhp (recentre .universalSL2 hm v x) = hypShiftA v * uhp x + hypShiftB v := by
  rw [recentre_universalSL2_apply, uhp_hyperboloidMap, hyperboloidInv_zero]
  obtain ⟨hb0, hb1⟩ := hyperboloidInv_one_base v
  have hx := hyperboloidInv_base 1 x
  simp only [coordinateShift, coordinateShiftLinear, PiLp.add_apply, sub_zero]
  simp [hx.1, hx.2, uhp, Real.exp_add, ← hb0, ← hb1]
  ring

theorem recentre_universalSL2_two (hm : ConnectionModel.universalSL2.baseCurvature ≤ 0)
    (v x : ModelCoordinates) :
    recentre .universalSL2 hm v x 2 = x 2 + v 2 - gam (uhp v) - gam (uhp x) +
      gam (hypShiftA v * uhp x + hypShiftB v) := by
  have hu := uhp_recentre_universalSL2 hm v x
  rw [recentre_universalSL2_apply] at hu ⊢
  rw [hyperboloidMap_one_two, ← uhp_hyperboloidMap 1, hu, hyperboloidInv_zero]
  have hv := hyperboloidInv_one_two v
  have hx := hyperboloidInv_one_two x
  simp only [coordinateShift, coordinateShiftLinear, PiLp.add_apply, sub_zero]
  simp [hv, hx]
  ring

def gaugeU (v : ModelCoordinates) (Z : ℂ) : ℝ :=
  gam Z - gam ((Z - hypShiftB v) / hypShiftA v) - gam (uhp v) + v 2

theorem hypShiftA_pos (v : ModelCoordinates) : 0 < hypShiftA v := Real.exp_pos _

theorem recentre_symm_universalSL2_two (hm : ConnectionModel.universalSL2.baseCurvature ≤ 0)
    (v y : ModelCoordinates) :
    (recentre .universalSL2 hm v).symm y 2 = y 2 - gaugeU v (uhp y) := by
  set x := (recentre .universalSL2 hm v).symm y with hx
  have hy : recentre .universalSL2 hm v x = y := (recentre .universalSL2 hm v).apply_symm_apply y
  have h2 := recentre_universalSL2_two hm v x
  have hu := uhp_recentre_universalSL2 hm v x
  rw [hy] at h2 hu
  have hA := (hypShiftA_pos v).ne'
  have hZ : uhp x = (uhp y - hypShiftB v) / hypShiftA v := by
    rw [hu, add_sub_cancel_right, mul_div_cancel_left₀ _ (ofReal_ne_zero.mpr hA)]
  rw [gaugeU, ← hZ]
  rw [← hu] at h2
  linarith

theorem screwAt_universalSL2_two_gaugeU (hm : ConnectionModel.universalSL2.baseCurvature ≤ 0)
    (v : ModelCoordinates) (p : ℕ+) (q : ℤ) (ℓ : ℝ) (x : ModelCoordinates) :
    screwAt .universalSL2 hm v p q ℓ x 2 = x 2 - ℓ * q / p +
      gaugeU v (uhp (screwAt .universalSL2 hm v p q ℓ x)) - gaugeU v (uhp x) := by
  have h1 := recentre_symm_universalSL2_two hm v (screwAt .universalSL2 hm v p q ℓ x)
  have h2 := recentre_symm_universalSL2_two hm v x
  have hS : (recentre .universalSL2 hm v).symm (screwAt .universalSL2 hm v p q ℓ x) =
      screwDiffeomorph (-2 * Real.pi / p) (-ℓ * q / p)
        ((recentre .universalSL2 hm v).symm x) := by
    change (recentre .universalSL2 hm v).symm (recentre .universalSL2 hm v
      (screwDiffeomorph (-2 * Real.pi / p) (-ℓ * q / p) ((recentre .universalSL2 hm v).symm x))) =
        _
    exact (recentre .universalSL2 hm v).symm_apply_apply _
  have h3 : ∀ y : ModelCoordinates, screwDiffeomorph (-2 * Real.pi / p) (-ℓ * q / p) y 2 =
      y 2 + -ℓ * q / p := fun y => by
    rw [screwDiffeomorph_apply']
    simp [fibreShift]
  rw [hS, h3, h2] at h1
  have e : -ℓ * q / ((p : ℕ) : ℝ) = -(ℓ * q / ((p : ℕ) : ℝ)) := by ring
  linarith

def cayInv (w : ℂ) : ℂ := (1 - I * w) / (w - I)

theorem cayInv_cay {Z : ℂ} (hZ : 0 < Z.im) : cayInv (cay Z) = Z := by
  have h1 := add_I_ne_zero hZ
  unfold cayInv cay
  have hn : 1 - I * ((I * Z + 1) / (Z + I)) = 2 * Z / (Z + I) := by
    rw [eq_div_iff h1, sub_mul, mul_assoc, div_mul_cancel₀ _ h1]
    linear_combination (-Z) * I_sq
  have hd : (I * Z + 1) / (Z + I) - I = 2 / (Z + I) := by
    rw [eq_div_iff h1, sub_mul, div_mul_cancel₀ _ h1]
    linear_combination (-1 : ℂ) * I_sq
  rw [hn, hd, div_div_div_cancel_right₀ h1]
  ring

theorem cayInv_im {w : ℂ} (hw : w ≠ I) :
    (cayInv w).im = (1 - normSq w) / normSq (w - I) := by
  have hn : normSq (w - I) ≠ 0 := (normSq_pos.mpr (sub_ne_zero.mpr hw)).ne'
  unfold cayInv
  rw [div_eq_mul_inv, mul_im, inv_re, inv_im]
  simp only [sub_re, sub_im, one_re, one_im, mul_re, mul_im, I_re, I_im, normSq_apply]
  field_simp
  ring

theorem ne_I_of_norm_lt {w : ℂ} (hw : ‖w‖ < 1) : w ≠ I := by
  rintro rfl
  simp at hw

theorem cayInv_im_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (cayInv w).im := by
  rw [cayInv_im (ne_I_of_norm_lt hw)]
  have h1 : normSq w < 1 := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  exact div_pos (by linarith) (normSq_pos.mpr (sub_ne_zero.mpr (ne_I_of_norm_lt hw)))

def gauge (v : ModelCoordinates) (w : ℂ) : ℝ := gaugeU v (cayInv w)

theorem gauge_hb (v x : ModelCoordinates) : gauge v (hb x) = gaugeU v (uhp x) := by
  rw [gauge, hb_eq_cay_uhp 0 x, cayInv_cay (uhp_im_pos x)]

theorem recentre_symm_universalSL2_two_gauge
    (hm : ConnectionModel.universalSL2.baseCurvature ≤ 0)
    (v y : ModelCoordinates) :
    (recentre .universalSL2 hm v).symm y 2 = y 2 - gauge v (hb y) := by
  rw [gauge_hb]
  exact recentre_symm_universalSL2_two hm v y

theorem screwAt_universalSL2_two_gauge (hm : ConnectionModel.universalSL2.baseCurvature ≤ 0)
    (v : ModelCoordinates) (p : ℕ+) (q : ℤ) (ℓ : ℝ) (x : ModelCoordinates) :
    screwAt .universalSL2 hm v p q ℓ x 2 = x 2 - ℓ * q / p +
      gauge v (hb (screwAt .universalSL2 hm v p q ℓ x)) - gauge v (hb x) := by
  rw [gauge_hb, gauge_hb]
  exact screwAt_universalSL2_two_gaugeU hm v p q ℓ x

theorem gaugeU_uhp_self (v : ModelCoordinates) (hv : v 2 = 0) : gaugeU v (uhp v) = 0 := by
  have hA := (hypShiftA_pos v).ne'
  have h : (uhp v - hypShiftB v) / hypShiftA v = I := by
    rw [uhp_eq_shift, add_sub_cancel_left, mul_div_right_comm, div_self (ofReal_ne_zero.mpr hA),
      one_mul]
  rw [gaugeU, h, hv]
  simp [gam]

theorem gauge_hb_self (v : ModelCoordinates) (hv : v 2 = 0) : gauge v (hb v) = 0 := by
  rw [gauge_hb, gaugeU_uhp_self v hv]

theorem contDiffAt_gam {Z : ℂ} (hZ : Z.im + 1 ≠ 0) : ContDiffAt ℝ ∞ gam Z := by
  have h : ContDiffAt ℝ ∞ (fun W : ℂ => W.re / (W.im + 1)) Z :=
    reCLM.contDiff.contDiffAt.div (imCLM.contDiff.contDiffAt.add contDiffAt_const) hZ
  exact contDiffAt_const.mul (Real.contDiff_arctan.contDiffAt.comp Z h)

theorem contDiffAt_cayInv {w : ℂ} (hw : w ≠ I) : ContDiffAt ℝ ∞ cayInv w := by
  have h1 : ContDiffAt ℝ ∞ (fun u : ℂ => 1 - I * u) w :=
    contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)
  have h2 : ContDiffAt ℝ ∞ (fun u : ℂ => u - I) w := contDiffAt_id.sub contDiffAt_const
  have h := h1.mul (h2.inv (sub_ne_zero.mpr hw))
  have e : cayInv = fun u : ℂ => (1 - I * u) * (u - I)⁻¹ := funext fun u => div_eq_mul_inv _ _
  rw [e]
  exact h

theorem contDiffOn_gauge (v : ModelCoordinates) :
    ContDiffOn ℝ ∞ (gauge v) {w | ‖w‖ < 1} := by
  intro w hw
  have hw' : ‖w‖ < 1 := hw
  have hZ := cayInv_im_pos hw'
  have hA := hypShiftA_pos v
  have hc := contDiffAt_cayInv (ne_I_of_norm_lt hw')
  have g1 := (contDiffAt_gam (Z := cayInv w) (by linarith)).comp w hc
  have him : ((cayInv w - hypShiftB v) / hypShiftA v).im + 1 ≠ 0 := by
    have : ((cayInv w - hypShiftB v) / hypShiftA v).im = (cayInv w).im / hypShiftA v := by
      rw [div_ofReal_im, sub_im, ofReal_im, sub_zero]
    rw [this]
    have := div_pos hZ hA
    linarith
  have hlin : ContDiffAt ℝ ∞ (fun u : ℂ => (cayInv u - hypShiftB v) / hypShiftA v) w :=
    (hc.sub contDiffAt_const).div_const _
  have g2 := (contDiffAt_gam him).comp w hlin
  exact ((g1.sub g2).sub contDiffAt_const |>.add contDiffAt_const).contDiffWithinAt

end Hyp

end ClosedTriangle

end GC.Seifert

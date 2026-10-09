import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypGauge
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryPhase

/-!
# The `SL₂~` gauge is `2 Arg (1 - c̄ w)`

Lane B3b (design `docs/geometrization/handoffs/20261004-design-b3c-hyperbolic-rows.md`, §2 (H3),
with review 33 §3.3, §5.2, §5.5, §6.2). For a centre `v` of zero fibre coordinate with base point
`c = hb v`, the recentring gauge of `SL₂~` on the unit disc is exactly
`hypGauge c w = 2 Arg (1 - c̄ w)` (`gauge_eq_hypGauge`): a real identity, not one modulo `2π`. It
comes from the positive-factor identity
`(1 - i Z')(1 - i V) = (|V + i|²/2A) (1 - c̄ w)(1 - i Z)` (`gauge_ratio`), `Z' = (Z - B)/A`, in
which all four factors lie in the right half-plane, so the principal arguments add exactly
(`arg_add_arg_eq`). Consequences, all exact on the disc:
* the screw formula `(S x)₂ = x₂ - ℓ q/p + G(S x) - G(x)` with `G = hypGauge c ∘ hb`
  (`screwAt_universalSL2_two_centre`), and the public fibre-shift commutation of the recentring at
  an arbitrary point for both hyperbolic models (`recentre_add_fibreShift_hyp`);
* smoothness on the disc (`contDiffOn_hypGauge`), `hypGauge c c = 0`, `hypGauge c 0 = 0`;
* reflection and rotation: `hypGauge (conj c) (conj w) = -hypGauge c w`, `hypGauge (u c) (u w) =
  hypGauge c w` for `|u| = 1`, and `hypGauge c z' = -hypGauge c z` whenever `c̄ z' = conj (c̄ z)`
  (`hypGauge_conj`, `hypGauge_rot`, `hypGauge_odd`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

namespace ClosedTriangle

namespace Hyp

open GC.Geometry

section Args

theorem abs_arg_lt_of_re_pos {z : ℂ} (h : 0 < z.re) : |arg z| < Real.pi / 2 :=
  abs_arg_lt_pi_div_two_iff.mpr (Or.inl h)

theorem ne_zero_of_re_pos {z : ℂ} (h : 0 < z.re) : z ≠ 0 := by
  rintro rfl; simp at h

theorem arg_eq_arctan_of_re_pos {z : ℂ} (h : 0 < z.re) : arg z = Real.arctan (z.im / z.re) := by
  have hb := abs_lt.mp (abs_arg_lt_of_re_pos h)
  rw [← tan_arg, Real.arctan_tan hb.1 hb.2]

theorem eq_of_angle_eq {a b : ℝ} (h : (a : Real.Angle) = b) (hab : |a - b| < 2 * Real.pi) :
    a = b := by
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h
  rw [hk, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at hab
  have hk1 : |(k : ℝ)| < 1 := by
    have := Real.pi_pos
    nlinarith
  have hk0 : k = 0 := by
    have := abs_lt.mp hk1
    have h1 : (k : ℝ) < 1 := this.2
    have h2 : (-1 : ℝ) < k := this.1
    have : k < 1 := by exact_mod_cast h1
    have : -1 < k := by exact_mod_cast h2
    omega
  rw [hk0, Int.cast_zero, mul_zero] at hk
  linarith

theorem arg_add_arg_eq {X Y W U : ℂ} {r : ℝ} (hr : 0 < r) (hX : 0 < X.re) (hY : 0 < Y.re)
    (hW : 0 < W.re) (hU : 0 < U.re) (h : X * Y = r * (W * U)) :
    arg X + arg Y = arg W + arg U := by
  have a1 := abs_lt.mp (abs_arg_lt_of_re_pos hX)
  have a2 := abs_lt.mp (abs_arg_lt_of_re_pos hY)
  have a3 := abs_lt.mp (abs_arg_lt_of_re_pos hW)
  have a4 := abs_lt.mp (abs_arg_lt_of_re_pos hU)
  have h1 := arg_mul_coe_angle (ne_zero_of_re_pos hX) (ne_zero_of_re_pos hY)
  have h2 := arg_mul_coe_angle (ne_zero_of_re_pos hW) (ne_zero_of_re_pos hU)
  rw [h, arg_real_mul _ hr, h2] at h1
  apply eq_of_angle_eq
  · rw [Real.Angle.coe_add, Real.Angle.coe_add, h1]
  · rw [abs_lt]
    constructor <;> linarith

end Args

def hypGauge (c w : ℂ) : ℝ := 2 * arg (1 - conj c * w)

section GaugeD

theorem re_one_sub_conj_mul_pos {c w : ℂ} (hc : ‖c‖ < 1) (hw : ‖w‖ < 1) :
    0 < (1 - conj c * w).re := by
  have h := HypFold.norm_conj_mul_lt_one hc hw
  have := re_le_norm (conj c * w)
  rw [sub_re, one_re]
  linarith

theorem abs_hypGauge_lt {c w : ℂ} (hc : ‖c‖ < 1) (hw : ‖w‖ < 1) : |hypGauge c w| < Real.pi := by
  have := abs_arg_lt_of_re_pos (re_one_sub_conj_mul_pos hc hw)
  rw [hypGauge, abs_mul, abs_two]
  linarith

theorem hypGauge_self {c : ℂ} (hc : ‖c‖ < 1) : hypGauge c c = 0 := by
  have h : 1 - conj c * c = ((1 - normSq c : ℝ) : ℂ) := by
    rw [mul_comm, mul_conj]; push_cast; ring
  have hpos : 0 < 1 - normSq c := by
    have := HypFold.normSq_lt_one_of_norm_lt hc
    linarith
  rw [hypGauge, h, arg_ofReal_of_nonneg hpos.le, mul_zero]

theorem hypGauge_zero_right (c : ℂ) : hypGauge c 0 = 0 := by simp [hypGauge]

theorem hypGauge_zero_left (w : ℂ) : hypGauge 0 w = 0 := by simp [hypGauge]

theorem hypGauge_odd {c z z' : ℂ} (hz : 0 < (1 - conj c * z).re)
    (h : conj c * z' = conj (conj c * z)) : hypGauge c z' = -hypGauge c z := by
  have e : 1 - conj c * z' = conj (1 - conj c * z) := by rw [h, map_sub, map_one]
  have hne : arg (1 - conj c * z) ≠ Real.pi := by
    have := abs_lt.mp (abs_arg_lt_of_re_pos hz)
    intro h'; linarith [Real.pi_pos]
  rw [hypGauge, hypGauge, e, arg_conj, ite_eq_right_iff.mpr (fun h' => absurd h' hne)]
  ring

theorem hypGauge_conj {c w : ℂ} (hw : 0 < (1 - conj c * w).re) :
    hypGauge (conj c) (conj w) = -hypGauge c w := by
  have e : 1 - conj (conj c) * conj w = conj (1 - conj c * w) := by
    simp [map_sub, map_mul]
  have hne : arg (1 - conj c * w) ≠ Real.pi := by
    have := abs_lt.mp (abs_arg_lt_of_re_pos hw)
    intro h'; linarith [Real.pi_pos]
  rw [hypGauge, hypGauge, e, arg_conj, ite_eq_right_iff.mpr (fun h' => absurd h' hne)]
  ring

theorem hypGauge_rot {u : ℂ} (hu : ‖u‖ = 1) (c w : ℂ) :
    hypGauge (u * c) (u * w) = hypGauge c w := by
  have h : conj (u * c) * (u * w) = conj c * w := by
    have hn : conj u * u = 1 := by
      rw [mul_comm, mul_conj, normSq_eq_norm_sq, hu]; norm_num
    rw [map_mul]
    linear_combination (conj c * w) * hn
  rw [hypGauge, hypGauge, h]

theorem contDiffOn_hypGauge (c : ℂ) (hc : ‖c‖ < 1) :
    ContDiffOn ℝ ∞ (hypGauge c) (Metric.ball 0 1) := by
  intro w hw
  rw [mem_ball_zero_iff] at hw
  have hre := re_one_sub_conj_mul_pos hc hw
  have hs : 1 - conj c * w ∈ slitPlane := Or.inl hre
  have h1 : ContDiffAt ℝ ∞ (fun u : ℂ => 1 - conj c * u) w :=
    contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)
  exact (contDiffAt_const.mul ((contDiffAt_arg_slit hs).comp w h1)).contDiffWithinAt

end GaugeD

section Formula

theorem gam_eq_neg_arg {Z : ℂ} (hZ : 0 < Z.im + 1) : gam Z = -2 * arg (1 - I * Z) := by
  have hre : (1 - I * Z).re = Z.im + 1 := by simp; ring
  have him : (1 - I * Z).im = -Z.re := by simp
  rw [arg_eq_arctan_of_re_pos (by rw [hre]; exact hZ), hre, him, neg_div, Real.arctan_neg, gam]
  ring

theorem cay_cayInv {w : ℂ} (hw : w ≠ I) : cay (cayInv w) = w := by
  have h1 : w - I ≠ 0 := sub_ne_zero.mpr hw
  unfold cay cayInv
  have hn : I * ((1 - I * w) / (w - I)) + 1 = 2 * w / (w - I) := by
    rw [eq_div_iff h1, add_mul, mul_assoc, div_mul_cancel₀ _ h1]
    linear_combination (-w) * I_sq
  have hd : (1 - I * w) / (w - I) + I = 2 / (w - I) := by
    rw [eq_div_iff h1, add_mul, div_mul_cancel₀ _ h1]
    linear_combination (-1 : ℂ) * I_sq
  rw [hn, hd, div_div_div_cancel_right₀ h1]
  ring

theorem gauge_ratio (v : ModelCoordinates) {Z : ℂ} (hZ : 0 < Z.im) :
    (1 - I * ((Z - hypShiftB v) / hypShiftA v)) * (1 - I * uhp v) =
      ((normSq (uhp v + I) / (2 * hypShiftA v) : ℝ) : ℂ) *
        ((1 - conj (cay (uhp v)) * cay Z) * (1 - I * Z)) := by
  have hA := hypShiftA_pos v
  have hA' : (hypShiftA v : ℂ) ≠ 0 := ofReal_ne_zero.mpr hA.ne'
  set V := uhp v with hV
  have hVim := uhp_im_pos v
  have hV1 := add_I_ne_zero hVim
  have hV2 := conj_sub_I_ne_zero hVim
  have hZ1 := add_I_ne_zero hZ
  have hVs : V = hypShiftB v + hypShiftA v * I := uhp_eq_shift v
  have hcV : conj V = hypShiftB v - hypShiftA v * I := by rw [hVs]; simp; ring
  have hn : ((normSq (V + I) : ℝ) : ℂ) = (V + I) * (conj V - I) := by
    rw [← mul_conj, map_add, conj_I, sub_eq_add_neg]
  have e1 : 1 - I * ((Z - hypShiftB v) / hypShiftA v) = (-I * (Z - conj V)) / hypShiftA v := by
    have : (1 : ℂ) - I * ((Z - hypShiftB v) / hypShiftA v) =
        (hypShiftA v - I * (Z - hypShiftB v)) / hypShiftA v := by field_simp
    rw [this, hcV]
    congr 1
    linear_combination (hypShiftA v : ℂ) * I_sq
  have e2 : 1 - I * V = -I * (V + I) := by linear_combination I_sq
  have e3 : 1 - I * Z = -I * (Z + I) := by linear_combination I_sq
  rw [one_sub_conj_cay_mul hV2 hZ1, e1, e2, e3]
  push_cast
  rw [hn]
  field_simp
  ring

theorem norm_cay_lt_one {Z : ℂ} (hZ : 0 < Z.im) : ‖cay Z‖ < 1 := by
  have h1 := add_I_ne_zero hZ
  rw [cay, norm_div, div_lt_one (norm_pos_iff.mpr h1)]
  have hs : normSq (I * Z + 1) < normSq (Z + I) := by
    simp only [normSq_apply, add_re, add_im, mul_re, mul_im, I_re, I_im, one_re, one_im]
    nlinarith
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at hs
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hs

theorem gaugeU_eq_hypGauge (v : ModelCoordinates) (hv : v 2 = 0) {Z : ℂ} (hZ : 0 < Z.im) :
    gaugeU v Z = hypGauge (hb v) (cay Z) := by
  have hA := hypShiftA_pos v
  have hVim := uhp_im_pos v
  have hZ' : 0 < ((Z - hypShiftB v) / hypShiftA v).im := by
    rw [div_ofReal_im, sub_im, ofReal_im, sub_zero]; exact div_pos hZ hA
  have hc : hb v = cay (uhp v) := hb_eq_cay_uhp 0 v
  have hr : 0 < normSq (uhp v + I) / (2 * hypShiftA v) :=
    div_pos (normSq_pos.mpr (add_I_ne_zero hVim)) (by positivity)
  have hreU : ∀ W : ℂ, 0 < W.im → 0 < (1 - I * W).re := fun W hW => by
    simp only [sub_re, one_re, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub]; linarith
  have hW : 0 < (1 - conj (cay (uhp v)) * cay Z).re :=
    re_one_sub_conj_mul_pos (norm_cay_lt_one hVim) (norm_cay_lt_one hZ)
  have key := arg_add_arg_eq hr (hreU _ hZ') (hreU _ hVim) hW (hreU _ hZ) (gauge_ratio v hZ)
  rw [gaugeU, hv, gam_eq_neg_arg (by linarith), gam_eq_neg_arg (by linarith),
    gam_eq_neg_arg (by linarith), hypGauge, hc]
  linarith

theorem gauge_eq_hypGauge (v : ModelCoordinates) (hv : v 2 = 0) {w : ℂ} (hw : ‖w‖ < 1) :
    gauge v w = hypGauge (hb v) w := by
  rw [gauge, gaugeU_eq_hypGauge v hv (cayInv_im_pos hw), cay_cayInv (ne_I_of_norm_lt hw)]

theorem screwAt_universalSL2_two_centre
    (hm : ConnectionModel.universalSL2.baseCurvature ≤ 0)
    (v : ModelCoordinates) (hv : v 2 = 0) (p : ℕ+) (q : ℤ) (ℓ : ℝ) (x : ModelCoordinates) :
    screwAt .universalSL2 hm v p q ℓ x 2 = x 2 - ℓ * q / p +
      hypGauge (hb v) (hb (screwAt .universalSL2 hm v p q ℓ x)) - hypGauge (hb v) (hb x) := by
  have h1 : ‖hb (screwAt .universalSL2 hm v p q ℓ x)‖ < 1 := norm_hypDisc_lt_one _
  have h2 : ‖hb x‖ < 1 := norm_hypDisc_lt_one _
  rw [screwAt_universalSL2_two_gauge hm v p q ℓ x, gauge_eq_hypGauge v hv h1,
    gauge_eq_hypGauge v hv h2]

theorem screwAt_universalSL2_two (hm : ConnectionModel.universalSL2.baseCurvature ≤ 0) {c : ℂ}
    (hc : ‖c‖ < 1) (p : ℕ+) (q : ℤ) (ℓ : ℝ) (x : ModelCoordinates) :
    screwAt .universalSL2 hm (hypVertex c) p q ℓ x 2 =
      x 2 - ℓ * q / p + hypGauge c (hb (screwAt .universalSL2 hm (hypVertex c) p q ℓ x)) -
        hypGauge c (hb x) := by
  have h := screwAt_universalSL2_two_centre hm (hypVertex c) (by simp [hypVertex]) p q ℓ x
  rwa [hb_hypVertex hc] at h

theorem hyperboloidInv_add_fibreShift (l : ℝ) (x : ModelCoordinates) (s : ℝ) :
    hyperboloidInv l (x + fibreShift s) = hyperboloidInv l x + fibreShift s := by
  ext i
  fin_cases i <;> simp [hyperboloidInv, hyperboloidHeight, fibreShift]
  ring

theorem hyperboloidMap_add_fibreShift (l : ℝ) (g : ModelCoordinates) (s : ℝ) :
    hyperboloidMap l (g + fibreShift s) = hyperboloidMap l g + fibreShift s := by
  ext i
  fin_cases i <;> simp [hyperboloidMap, fibreShift]
  ring

theorem coordinateShift_add_fibreShift (k : CoordinateModel)
    (hk : k = .hyperbolicProduct ∨ k = .universalSL2) (a b y : ModelCoordinates) (s : ℝ) :
    coordinateShift k a b (y + fibreShift s) = coordinateShift k a b y + fibreShift s := by
  rcases hk with rfl | rfl <;>
  · ext i
    fin_cases i <;> simp [coordinateShift, coordinateShiftLinear, fibreShift]
    ring

theorem recentre_add_fibreShift_hyp (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (hmm : m = .hyperbolicProduct ∨ m = .universalSL2) (v x : ModelCoordinates) (s : ℝ) :
    recentre m hm v (x + fibreShift s) = recentre m hm v x + fibreShift s := by
  rcases hmm with rfl | rfl
  · rw [recentre_hyperbolicProduct_apply, recentre_hyperbolicProduct_apply,
      hyperboloidInv_add_fibreShift, coordinateShift_add_fibreShift _ (Or.inl rfl),
      hyperboloidMap_add_fibreShift]
  · rw [recentre_universalSL2_apply, recentre_universalSL2_apply,
      hyperboloidInv_add_fibreShift, coordinateShift_add_fibreShift _ (Or.inr rfl),
      hyperboloidMap_add_fibreShift]

end Formula

end Hyp

end ClosedTriangle

end GC.Seifert

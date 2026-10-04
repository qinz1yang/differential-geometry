import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphBridges

/-!
# Circles about a point in the stereographic chart

Lane CF-S, tier 2, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §4). The circle about `a` through `z` is
`sphCirc a z t = sphMoebInv a (sphMoeb a z · e^{it})`: in the disc coordinate at `a` it is the
rotation about the origin, so the chordal distance `‖sphMoeb a ·‖` is constant along it
(`eventually_norm_sphMoeb_sphCirc`), and it passes through `z` with an explicit velocity
(`hasDerivAt_sphCirc`).

Along the rotation `ζ e^{it}` the chordal distance to a point `b` has derivative
`Im (b̄ ζ) (1 + ‖ζ‖²)(1 + ‖b‖²) / (‖1 + b̄ ζ‖⁴ ‖sphMoeb b ζ‖)` (`hasDerivAt_norm_sphMoeb_rot`),
because `‖sphMoeb b w‖² = (‖b‖² + ‖w‖² - 2 Re (b̄ w))/(1 + ‖b‖² ‖w‖² + 2 Re (b̄ w))`
(`norm_sphMoeb_eq_sqrt`). By the invariance of the chordal distance under the rotations of the
sphere the same holds along `sphCirc a z` with `b, ζ` replaced by their disc coordinates at `a`
(`hasDerivAt_norm_sphMoeb_sphCirc`): the sign of the derivative is the side of the geodesic
through `a` and `b` on which `z` lies.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem norm_sphMoeb_eq_sqrt (b w : ℂ) : ‖sphMoeb b w‖ =
    Real.sqrt ((‖b‖ ^ 2 + ‖w‖ ^ 2 - 2 * (conj b * w).re) /
      (1 + ‖b‖ ^ 2 * ‖w‖ ^ 2 + 2 * (conj b * w).re)) := by
  rw [sphMoeb, norm_div, ← sq_norm_sub_eq_sph, ← sq_norm_one_add_eq_sph, ← div_pow,
    Real.sqrt_sq (div_nonneg (norm_nonneg _) (norm_nonneg _))]

theorem norm_mul_exp_I_sph (ζ : ℂ) (t : ℝ) : ‖ζ * exp ((t : ℂ) * I)‖ = ‖ζ‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem re_conj_mul_rot_sph (b ζ : ℂ) (t : ℝ) : (conj b * (ζ * exp ((t : ℂ) * I))).re =
    (conj b * ζ).re * Real.cos t - (conj b * ζ).im * Real.sin t := by
  rw [← mul_assoc, mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem hasDerivAt_re_conj_mul_rot_sph (b ζ : ℂ) :
    HasDerivAt (fun t : ℝ => (conj b * (ζ * exp ((t : ℂ) * I))).re) (-(conj b * ζ).im) 0 := by
  have e : (fun t : ℝ => (conj b * (ζ * exp ((t : ℂ) * I))).re) =
      fun t => (conj b * ζ).re * Real.cos t - (conj b * ζ).im * Real.sin t :=
    funext (re_conj_mul_rot_sph b ζ)
  rw [e]
  refine (((Real.hasDerivAt_cos 0).const_mul _).sub
    ((Real.hasDerivAt_sin 0).const_mul _)).congr_deriv ?_
  simp

theorem hasDerivAt_norm_sphMoeb_rot {b ζ : ℂ} (h1 : 1 + conj b * ζ ≠ 0)
    (h0 : sphMoeb b ζ ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖sphMoeb b (ζ * exp ((t : ℂ) * I))‖)
      ((conj b * ζ).im * (1 + ‖ζ‖ ^ 2) * (1 + ‖b‖ ^ 2) /
        (‖1 + conj b * ζ‖ ^ 4 * ‖sphMoeb b ζ‖)) 0 := by
  set X := (conj b * ζ).re with hX
  set Y := (conj b * ζ).im with hY
  set A := ‖b‖ ^ 2 + ‖ζ‖ ^ 2 with hA
  set B := 1 + ‖b‖ ^ 2 * ‖ζ‖ ^ 2 with hB
  have hc := hasDerivAt_re_conj_mul_rot_sph b ζ
  have e : (fun t : ℝ => ‖sphMoeb b (ζ * exp ((t : ℂ) * I))‖) = fun t : ℝ =>
      Real.sqrt ((A - 2 * (conj b * (ζ * exp ((t : ℂ) * I))).re) /
        (B + 2 * (conj b * (ζ * exp ((t : ℂ) * I))).re)) := by
    funext t
    rw [norm_sphMoeb_eq_sqrt, norm_mul_exp_I_sph]
  have hD : B + 2 * X = ‖1 + conj b * ζ‖ ^ 2 := by rw [sq_norm_one_add_eq_sph]
  have hN : A - 2 * X = ‖ζ - b‖ ^ 2 := by rw [sq_norm_sub_eq_sph]
  have hDpos : 0 < ‖1 + conj b * ζ‖ := norm_pos_iff.2 h1
  have hr : ‖sphMoeb b ζ‖ = ‖ζ - b‖ / ‖1 + conj b * ζ‖ := by rw [sphMoeb, norm_div]
  have hpos : 0 < ‖sphMoeb b ζ‖ := norm_pos_iff.2 h0
  have hζb : 0 < ‖ζ - b‖ := by
    rw [hr] at hpos
    exact (div_pos_iff_of_pos_right hDpos).1 hpos
  have h0' : (A - 2 * (conj b * (ζ * exp (((0 : ℝ) : ℂ) * I))).re) /
      (B + 2 * (conj b * (ζ * exp (((0 : ℝ) : ℂ) * I))).re) ≠ 0 := by
    simp only [ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [← hX, hD, hN]
    positivity
  have hden : B + 2 * (conj b * (ζ * exp (((0 : ℝ) : ℂ) * I))).re ≠ 0 := by
    simp only [ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [← hX, hD]
    positivity
  rw [e]
  refine (((hasDerivAt_const (0 : ℝ) A).sub (hc.const_mul 2)).div
    ((hasDerivAt_const (0 : ℝ) B).add (hc.const_mul 2)) hden |>.sqrt h0').congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, ofReal_zero, zero_mul, Complex.exp_zero,
    mul_one]
  rw [← hX, ← hY, hD, hN]
  have hsq : Real.sqrt (‖ζ - b‖ ^ 2 / ‖1 + conj b * ζ‖ ^ 2) = ‖ζ - b‖ / ‖1 + conj b * ζ‖ := by
    rw [← div_pow, Real.sqrt_sq (by positivity)]
  rw [hsq, hr]
  have hAB : A + B = (1 + ‖ζ‖ ^ 2) * (1 + ‖b‖ ^ 2) := by rw [hA, hB]; ring
  have hND : (A - 2 * X) + (B + 2 * X) = A + B := by ring
  rw [hD, hN] at hND
  field_simp
  linear_combination (2 * Y) * (hND.trans hAB)

def sphCirc (a z : ℂ) (t : ℝ) : ℂ := sphMoebInv a (sphMoeb a z * exp ((t : ℂ) * I))

theorem sphCirc_zero {a z : ℂ} (h : 1 + conj a * z ≠ 0) : sphCirc a z 0 = z := by
  simp only [sphCirc, ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  exact sphMoebInv_sphMoeb h

theorem hasDerivAt_rot_sph (ζ : ℂ) :
    HasDerivAt (fun t : ℝ => ζ * exp ((t : ℂ) * I)) (ζ * I) 0 := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I).cexp.const_mul ζ
  refine h.congr_deriv ?_
  simp

theorem hasDerivAt_sphMoebInv {a w : ℂ} (h : 1 - conj a * w ≠ 0) :
    HasDerivAt (sphMoebInv a) ((1 + conj a * a) / (1 - conj a * w) ^ 2) w := by
  have h1 : HasDerivAt (fun u : ℂ => u + a) 1 w := (hasDerivAt_id w).add_const a
  have h2 : HasDerivAt (fun u : ℂ => 1 - conj a * u) (-conj a) w := by
    simpa using ((hasDerivAt_id w).const_mul (conj a)).const_sub 1
  refine (h1.div h2 h).congr_deriv ?_
  field_simp
  ring

theorem one_sub_conj_mul_sphMoeb_ne {a z : ℂ} (h : 1 + conj a * z ≠ 0) :
    1 - conj a * sphMoeb a z ≠ 0 := by
  rw [one_sub_conj_mul_sphMoeb h]
  exact div_ne_zero (one_add_conj_mul_self_ne_sph a) h

theorem hasDerivAt_sphCirc {a z : ℂ} (h : 1 + conj a * z ≠ 0) :
    HasDerivAt (sphCirc a z)
      ((1 + conj a * a) / (1 - conj a * sphMoeb a z) ^ 2 * (sphMoeb a z * I)) 0 := by
  have hr := hasDerivAt_rot_sph (sphMoeb a z)
  have hm : HasDerivAt (sphMoebInv a) ((1 + conj a * a) / (1 - conj a * sphMoeb a z) ^ 2)
      (sphMoeb a z * exp (((0 : ℝ) : ℂ) * I)) := by
    simp only [ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    exact hasDerivAt_sphMoebInv (one_sub_conj_mul_sphMoeb_ne h)
  exact hm.comp (0 : ℝ) hr

theorem continuousAt_sphCirc {a z : ℂ} (h : 1 + conj a * z ≠ 0) :
    ContinuousAt (sphCirc a z) 0 :=
  (hasDerivAt_sphCirc h).continuousAt

theorem eventually_sphCirc {a z : ℂ} (h : 1 + conj a * z ≠ 0) {s : Set ℂ} (hs : IsOpen s)
    (hz : z ∈ s) : ∀ᶠ t in 𝓝 (0 : ℝ), sphCirc a z t ∈ s := by
  have hc := continuousAt_sphCirc h
  rw [ContinuousAt, sphCirc_zero h] at hc
  exact hc (hs.mem_nhds hz)

theorem eventually_sphMoeb_sphCirc {a z : ℂ} (h : 1 + conj a * z ≠ 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), sphMoeb a (sphCirc a z t) = sphMoeb a z * exp ((t : ℂ) * I) := by
  have hc : ContinuousAt (fun t : ℝ => 1 - conj a * (sphMoeb a z * exp ((t : ℂ) * I))) 0 := by
    fun_prop
  have h0 : (fun t : ℝ => 1 - conj a * (sphMoeb a z * exp ((t : ℂ) * I))) 0 ≠ 0 := by
    simp only [ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    exact one_sub_conj_mul_sphMoeb_ne h
  filter_upwards [hc.eventually_ne h0] with t ht
  exact sphMoeb_sphMoebInv ht

theorem eventually_norm_sphMoeb_sphCirc {a z : ℂ} (h : 1 + conj a * z ≠ 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ‖sphMoeb a (sphCirc a z t)‖ = ‖sphMoeb a z‖ := by
  filter_upwards [eventually_sphMoeb_sphCirc h] with t ht
  rw [ht, norm_mul_exp_I_sph]

theorem eventually_ne_sphCirc {a z b : ℂ} (h : 1 + conj a * z ≠ 0) (hb : 1 + conj b * z ≠ 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), 1 + conj b * sphCirc a z t ≠ 0 := by
  have hc : ContinuousAt (fun t : ℝ => 1 + conj b * sphCirc a z t) 0 :=
    continuousAt_const.add (continuousAt_const.mul (continuousAt_sphCirc h))
  have h0 : (fun t : ℝ => 1 + conj b * sphCirc a z t) 0 ≠ 0 := by
    simp only [sphCirc_zero h]
    exact hb
  exact hc.eventually_ne h0

theorem one_add_conj_sphMoeb_ne {a b z : ℂ} (h1 : 1 + conj a * z ≠ 0)
    (h2 : 1 + conj a * b ≠ 0) (h3 : 1 + conj b * z ≠ 0) :
    1 + conj (sphMoeb a b) * sphMoeb a z ≠ 0 := by
  rw [one_add_conj_sphMoeb_mul h1 h2]
  exact div_ne_zero (mul_ne_zero (one_add_conj_mul_self_ne_sph a) h3)
    (mul_ne_zero (one_add_mul_conj_ne_sph h2) h1)

theorem hasDerivAt_norm_sphMoeb_sphCirc {a b z : ℂ} (h1 : 1 + conj a * z ≠ 0)
    (h2 : 1 + conj a * b ≠ 0) (h3 : 1 + conj b * z ≠ 0) (h0 : sphMoeb b z ≠ 0) :
    HasDerivAt (fun t => ‖sphMoeb b (sphCirc a z t)‖)
      ((conj (sphMoeb a b) * sphMoeb a z).im * (1 + ‖sphMoeb a z‖ ^ 2) *
        (1 + ‖sphMoeb a b‖ ^ 2) /
        (‖1 + conj (sphMoeb a b) * sphMoeb a z‖ ^ 4 * ‖sphMoeb b z‖)) 0 := by
  have hD := one_add_conj_sphMoeb_ne h1 h2 h3
  have hn := norm_sphMoeb_comp h1 h2 h3
  have h0' : sphMoeb (sphMoeb a b) (sphMoeb a z) ≠ 0 := by
    rw [← norm_ne_zero_iff, hn, norm_ne_zero_iff]
    exact h0
  have hd := hasDerivAt_norm_sphMoeb_rot hD h0'
  rw [hn] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [eventually_sphMoeb_sphCirc h1, eventually_ne_sphCirc h1 h1,
    eventually_ne_sphCirc h1 h3] with t e1 e2 e3
  rw [← e1, norm_sphMoeb_comp e2 h2 e3]

end GC.Seifert

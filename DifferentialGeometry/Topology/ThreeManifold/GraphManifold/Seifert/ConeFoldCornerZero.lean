import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldCornerBlend

/-!
# The corner at the cusp `0` of the `(p, ⊤, ⊤)` fold

Lane A4, tier 2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5).
Horocycles at the cusp `0` are the curves `horoCurve z t = z/(1 - 4tz)`: the horocyclic coordinate
`horoX = Re(-1/(4z))` moves by `t` and the height `η₀ = |z|²/Im z` stays fixed
(`horoX_horoCurve`, `cuspZeroHeight_horoCurve`); the velocity is `4z²`.

The corner `cornerZero a b z = 3/2 + G(η₀) e^{i angleHole}` is polar about `3/2`; its angle
blends, with the weight `coneStep a b (horoX z)`, the angle `angleZeroHole` of the wall-0 bridge
`bridgeZero` about `3/2` (used for `horoX ≥ b`) and the angle `angleTwoHole` of the wall-2
bridge `bridgeTwo` (used for `horoX ≤ a`). Along every horocycle, oriented towards wall 0:
* `angleZeroHole` strictly decreases (`exists_hasDerivAt_angleZeroHole`): the varying circle
  `|u| = 3/2 + G(y)` has radius derivative `x · 32 K y²/(y² + K)²`, a multiple of the wall-0
  function;
* `angleTwoHole` strictly decreases (`exists_hasDerivAt_angleTwoHole`): `η₁` has derivative
  `wallTwo · κ₁` with `κ₁ > 0` (`exists_hasDerivAt_etaOne_horo`, from the exact identity
  `d|ω₁|²/dt = 2(1 + cos θ₁) y wallTwo/|z - v̄₁|²`, `horo_identity`), and `wallTwo` increases
  through its zeros (`wallTwo_horo_deriv`); the general curve derivative of a cone height is
  `hasDerivAt_coneHeight_curve`;
* on the triangle side `angleZeroHole ≤ angleTwoHole` (`angleZeroHole_le_angleTwoHole`, from
  `|bridgeZero| > 2 > |bridgeTwo|` on the common circle `|u - 3/2| = G(η₀)`).
Hence the blended angle strictly decreases (`exists_hasDerivAt_angleHole`) and the polar Jacobian
with the radial direction `z` and the horocycle direction `4z²` is nonzero
(`det_fderiv_cornerZero_ne_zero`). The corner equals the bridges in the weight zones
(`cornerZero_eq_bridgeZero`, `cornerZero_eq_bridgeTwo`) and is equivariant for the reflections in
wall 0 and wall 2 where the weight is `1` resp. `0` at both points (`cornerZero_refl_zero`,
`cornerZero_refl_two`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

def horoCurve (z : ℂ) (t : ℝ) : ℂ := z / (1 - 4 * (t : ℂ) * z)

def horoX (z : ℂ) : ℝ := (-1 / (4 * z)).re

theorem one_sub_four_mul_ne {z : ℂ} (hz : 0 < z.im) (t : ℝ) : 1 - 4 * (t : ℂ) * z ≠ 0 := by
  intro h
  have e1 : (1 - 4 * (t : ℂ) * z).im = -(4 * t * z.im) := by simp
  have e2 : (1 - 4 * (t : ℂ) * z).re = 1 - 4 * t * z.re := by simp
  rw [h] at e1 e2
  have h0 : t * z.im = 0 := by
    have : (0 : ℂ).im = 0 := rfl
    linarith
  rcases mul_eq_zero.1 h0 with ht | ht
  · rw [ht] at e2
    have : (0 : ℂ).re = 0 := rfl
    linarith
  · linarith

theorem horoCurve_zero (z : ℂ) : horoCurve z 0 = z := by
  simp [horoCurve]

theorem horoCurve_im {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    (horoCurve z t).im = z.im / normSq (1 - 4 * (t : ℂ) * z) := by
  have hn : normSq (1 - 4 * (t : ℂ) * z) ≠ 0 := normSq_eq_zero.not.2 (one_sub_four_mul_ne hz t)
  rw [horoCurve, div_im]
  simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, sub_im, one_im, mul_im]
  field_simp
  simp
  ring

theorem horoCurve_im_pos {z : ℂ} (hz : 0 < z.im) (t : ℝ) : 0 < (horoCurve z t).im := by
  rw [horoCurve_im hz]
  have := normSq_pos.2 (one_sub_four_mul_ne hz t)
  positivity

theorem cuspZeroHeight_horoCurve {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    cuspZeroHeight (horoCurve z t) = cuspZeroHeight z := by
  have hn : normSq (1 - 4 * (t : ℂ) * z) ≠ 0 := normSq_eq_zero.not.2 (one_sub_four_mul_ne hz t)
  rw [cuspZeroHeight, cuspZeroHeight, horoCurve_im hz, horoCurve, map_div₀]
  field_simp

theorem horoX_horoCurve {z : ℂ} (hz : 0 < z.im) (t : ℝ) : horoX (horoCurve z t) = horoX z + t := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have h1 := one_sub_four_mul_ne hz t
  have e : -1 / (4 * horoCurve z t) = -1 / (4 * z) + t := by
    rw [horoCurve]
    field_simp
    ring
  rw [horoX, horoX, e]
  simp

theorem hasDerivAt_horoCurve {z : ℂ} (hz : 0 < z.im) : HasDerivAt (horoCurve z) (4 * z ^ 2) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => 1 - 4 * (t : ℂ) * z) (-(4 * 1 * z)) 0 :=
    ((h1.const_mul 4).mul_const z).const_sub 1
  have hne : (fun t : ℝ => 1 - 4 * (t : ℂ) * z) 0 ≠ 0 := one_sub_four_mul_ne hz 0
  have h3 := (hasDerivAt_const (0 : ℝ) z).div h2 hne
  refine h3.congr_deriv ?_
  simp
  ring

theorem hasDerivAt_horoCurve_re {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun t => (horoCurve z t).re) (4 * (z.re ^ 2 - z.im ^ 2)) 0 := by
  have h := reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_horoCurve hz)
  refine h.congr_deriv ?_
  simp [sq]

theorem hasDerivAt_horoCurve_im {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun t => (horoCurve z t).im) (8 * z.re * z.im) 0 := by
  have h := imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_horoCurve hz)
  refine h.congr_deriv ?_
  simp [sq]
  ring

theorem continuous_horoCurve {z : ℂ} (hz : 0 < z.im) : Continuous (horoCurve z) := by
  unfold horoCurve
  exact continuous_const.div (continuous_const.sub ((continuous_const.mul
    Complex.continuous_ofReal).mul continuous_const)) (fun t => one_sub_four_mul_ne hz t)

theorem hasDerivAt_normSq_curve {γ : ℝ → ℂ} {V : ℂ} (hγ : HasDerivAt γ V 0) (c : ℂ) :
    HasDerivAt (fun t => normSq (γ t - c))
      (2 * ((γ 0 - c).re * V.re + (γ 0 - c).im * V.im)) 0 := by
  have hre : HasDerivAt (fun t => (γ t).re) V.re 0 := by
    refine (reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ).congr_deriv ?_
    simp
  have him : HasDerivAt (fun t => (γ t).im) V.im 0 := by
    refine (imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ).congr_deriv ?_
    simp
  have e : (fun t => normSq (γ t - c)) =
      fun t => ((γ t).re - c.re) ^ 2 + ((γ t).im - c.im) ^ 2 := by
    funext t
    simp [normSq_apply]
    ring
  rw [e]
  refine (((hre.sub_const c.re).pow 2).add ((him.sub_const c.im).pow 2)).congr_deriv ?_
  simp
  ring

theorem hasDerivAt_coneHeight_curve {v : ℂ} {γ : ℝ → ℂ} {V : ℂ} (hv : 0 < v.im)
    (hγ : HasDerivAt γ V 0) (hz : 0 < (γ 0).im) (hzv : γ 0 ≠ v) :
    HasDerivAt (fun t => coneHeight v (γ t))
      (v.im / ((1 - ‖coneDisc v (γ 0)‖) ^ 2 * ‖coneDisc v (γ 0)‖) *
        ((2 * ((γ 0 - v).re * V.re + (γ 0 - v).im * V.im) * normSq (γ 0 - conj v) -
          normSq (γ 0 - v) * (2 * ((γ 0 - conj v).re * V.re + (γ 0 - conj v).im * V.im))) /
            normSq (γ 0 - conj v) ^ 2)) 0 := by
  have hN := normSq_sub_conj_pos hv hz
  have hr1 := norm_coneDisc_lt_one hv hz
  have hr0 : 0 < ‖coneDisc v (γ 0)‖ := norm_pos_iff.2 (coneDisc_ne_zero hv hz hzv)
  have hq := (hasDerivAt_normSq_curve hγ v).div (hasDerivAt_normSq_curve hγ (conj v)) hN.ne'
  have hq0 : normSq (γ 0 - v) / normSq (γ 0 - conj v) ≠ 0 := by
    have : 0 < normSq (γ 0 - v) := normSq_pos.2 (sub_ne_zero.2 hzv)
    positivity
  have hs := hq.sqrt hq0
  have e : (fun t => ‖coneDisc v (γ t)‖) =
      fun t => Real.sqrt (normSq (γ t - v) / normSq (γ t - conj v)) :=
    funext fun t => norm_coneDisc_eq_sqrt v (γ t)
  have hsq : Real.sqrt (normSq (γ 0 - v) / normSq (γ 0 - conj v)) = ‖coneDisc v (γ 0)‖ :=
    (norm_coneDisc_eq_sqrt v (γ 0)).symm
  have hs' : HasDerivAt (fun t => ‖coneDisc v (γ t)‖)
      ((2 * ((γ 0 - v).re * V.re + (γ 0 - v).im * V.im) * normSq (γ 0 - conj v) -
          normSq (γ 0 - v) * (2 * ((γ 0 - conj v).re * V.re + (γ 0 - conj v).im * V.im))) /
            normSq (γ 0 - conj v) ^ 2 / (2 * ‖coneDisc v (γ 0)‖)) 0 := by
    rw [e, ← hsq]
    exact hs
  have hne : (fun t => 1 - ‖coneDisc v (γ t)‖) 0 ≠ 0 := by
    dsimp only
    linarith
  have h := ((hs'.const_add 1).const_mul v.im).div (hs'.const_sub 1) hne
  refine h.congr_deriv ?_
  have h1 : 1 - ‖coneDisc v (γ 0)‖ ≠ 0 := by linarith
  field_simp
  ring

namespace ConeShape

variable (σ : ConeShape)

def angleZeroHole (z : ℂ) : ℝ :=
  halfArg (coneProfile σ.constK (cuspZeroHeight z)) ((σ.bridgeZero z).re - 3 / 2)
    (σ.bridgeZero z).im

theorem bridgeZero_eq_twoCircle (z : ℂ) :
    σ.bridgeZero z = twoCircle (3 / 2) 0 (coneProfile σ.constK (cuspZeroHeight z))
      (3 / 2 + coneProfile σ.constK z.im) z.re
      (outerCofactor σ.constK (3 / 2) z.im (cuspZeroHeight z) (1 / z.im)) := by
  rw [bridgeZero, outerBridge, twoCircle_swap]

theorem three_halves_hole_pos {z : ℂ} (hz : 0 < z.im) :
    0 < coneProfile σ.constK (cuspZeroHeight z) + ((σ.bridgeZero z).re - 3 / 2) := by
  have hK := σ.constK_pos
  have h1 := σ.norm_bridgeZero_sub hz
  have h2 := σ.norm_bridgeZero hz
  have hG := half_lt_coneProfile hK (cuspZeroHeight_pos hz).ne'
  have hG' := coneProfile_lt hK (cuspZeroHeight z)
  have hR : 2 < 3 / 2 + coneProfile σ.constK z.im := by
    have := half_lt_coneProfile hK hz.ne'
    linarith
  have e1 : ((σ.bridgeZero z).re - 3 / 2) ^ 2 + (σ.bridgeZero z).im ^ 2 =
      coneProfile σ.constK (cuspZeroHeight z) ^ 2 := by
    have := sq_add_sq_eq_of_norm h1
    simpa using this
  have e2 : (σ.bridgeZero z).re ^ 2 + (σ.bridgeZero z).im ^ 2 =
      (3 / 2 + coneProfile σ.constK z.im) ^ 2 := sq_add_sq_eq_of_norm h2
  by_contra hc
  have hle : (σ.bridgeZero z).re ≤ 3 / 2 - coneProfile σ.constK (cuspZeroHeight z) := by
    linarith [not_lt.1 hc]
  nlinarith

theorem exists_hasDerivAt_angleZeroHole {z : ℂ} (hz : 0 < z.im) :
    ∃ D : ℝ, D < 0 ∧ HasDerivAt (fun t : ℝ => σ.angleZeroHole (horoCurve z t)) D 0 := by
  set K := σ.constK
  have hK := σ.constK_pos
  set η₀ := cuspZeroHeight z with hη₀
  have hη₀pos : 0 < η₀ := cuspZeroHeight_pos hz
  set A₀ := coneProfile K η₀ with hA₀
  have hA₀pos : 0 < A₀ := by have := half_le_coneProfile hK η₀; linarith
  set y : ℝ → ℝ := fun t => (horoCurve z t).im with hydef
  set x : ℝ → ℝ := fun t => (horoCurve z t).re with hxdef
  have hy' : HasDerivAt y (8 * z.re * z.im) 0 := hasDerivAt_horoCurve_im hz
  have hx' : HasDerivAt x (4 * (z.re ^ 2 - z.im ^ 2)) 0 := hasDerivAt_horoCurve_re hz
  have hypos : ∀ t, 0 < y t := fun t => horoCurve_im_pos hz t
  have hy0 : y 0 = z.im := by simp [hydef, horoCurve_zero]
  have hx0 : x 0 = z.re := by simp [hxdef, horoCurve_zero]
  set κ := 4 * K * z.im / (z.im ^ 2 + K) ^ 2 * (8 * z.im) with hκ
  have hB : HasDerivAt (fun t => 3 / 2 + coneProfile K (y t)) (x 0 * κ) 0 := by
    have := ((hasDerivAt_coneProfile hK (y 0)).comp 0 hy').const_add (3 / 2)
    refine this.congr_deriv ?_
    rw [hy0, hx0, hκ]
    ring
  have hPc : ContDiffAt ℝ ∞ (fun u : ℂ => outerCofactor K (3 / 2) u.im η₀ (1 / u.im)) z := by
    have hi : ContDiffAt ℝ ∞ (fun u : ℂ => u.im) z := imCLM.contDiff.contDiffAt
    unfold outerCofactor
    have hd : (η₀ ^ 2 + K) * (z.im ^ 2 + K) ≠ 0 := by positivity
    have hG' := (contDiff_coneProfile hK).contDiffAt (x := z.im)
    exact ((((contDiffAt_const.add (hG'.comp z hi)).add contDiffAt_const).pow 2).sub
      contDiffAt_const).mul (((contDiffAt_const.add (hG'.comp z hi)).sub
        contDiffAt_const)) |>.mul
      ((contDiffAt_const.div hi hz.ne').mul ((contDiffAt_const.mul (contDiffAt_const.add hi)).div
        ((contDiffAt_const).mul (hi.pow 2 |>.add contDiffAt_const)) hd))
  have hPd : DifferentiableAt ℝ (fun t : ℝ => outerCofactor K (3 / 2) (y t) η₀ (1 / y t)) 0 := by
    have hz0 : z = horoCurve z 0 := (horoCurve_zero z).symm
    have := ((hPc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (hasDerivAt_horoCurve hz) hz0).differentiableAt
    simpa [Function.comp_def, hydef] using this
  have hP0 : ∀ᶠ t : ℝ in 𝓝 0, 0 < outerCofactor K (3 / 2) (y t) η₀ (1 / y t) :=
    Eventually.of_forall fun t => outerCofactor_pos hK (Or.inl rfl) (hypos t) hη₀pos
      (by have := hypos t; positivity)
  have hH : ∀ᶠ t : ℝ in 𝓝 0, ((A₀ + (3 / 2 + coneProfile K (y t))) ^ 2 - (0 - 3 / 2) ^ 2) *
      ((0 - 3 / 2) ^ 2 - (A₀ - (3 / 2 + coneProfile K (y t))) ^ 2) =
      x t ^ 2 * outerCofactor K (3 / 2) (y t) η₀ (1 / y t) := by
    refine Eventually.of_forall fun t => ?_
    have hsub : η₀ - y t = x t ^ 2 * (1 / y t) := by
      have := cuspZeroHeight_sub_im (horoCurve_im_pos hz t)
      rw [cuspZeroHeight_horoCurve hz t] at this
      simpa [hydef, hxdef] using this
    have h := outerBridge_heron hK (Or.inl rfl) (y := y t) (η := η₀) (w := x t)
      (q := 1 / y t) hsub
    rw [hA₀]
    linear_combination h
  have hev : ∀ t, σ.bridgeZero (horoCurve z t) = twoCircle (3 / 2) 0 A₀
      (3 / 2 + coneProfile K (y t)) (x t) (outerCofactor K (3 / 2) (y t) η₀ (1 / y t)) := by
    intro t
    rw [bridgeZero_eq_twoCircle, cuspZeroHeight_horoCurve hz t]
  have hpos : 0 < A₀ + ((twoCircle (3 / 2) 0 A₀ (3 / 2 + coneProfile K (y 0)) (x 0)
      (outerCofactor K (3 / 2) (y 0) η₀ (1 / y 0))).re - 3 / 2) := by
    have := σ.three_halves_hole_pos hz
    rw [← hev 0, horoCurve_zero]
    exact this
  have h := hasDerivAt_halfArg_twoCircle' (a := 3 / 2) (b := 0) (by norm_num) hA₀pos hB hx' hPd
    hP0 hH hpos
  have he : (fun t : ℝ => σ.angleZeroHole (horoCurve z t)) = fun t : ℝ => halfArg A₀
      ((twoCircle (3 / 2) 0 A₀ (3 / 2 + coneProfile K (y t)) (x t)
        (outerCofactor K (3 / 2) (y t) η₀ (1 / y t))).re - 3 / 2)
      (twoCircle (3 / 2) 0 A₀ (3 / 2 + coneProfile K (y t)) (x t)
        (outerCofactor K (3 / 2) (y t) η₀ (1 / y t))).im := by
    funext t
    rw [angleZeroHole, hev t, cuspZeroHeight_horoCurve hz t]
  rw [he]
  refine ⟨_, ?_, h⟩
  have hsq := Real.sqrt_pos.2 (hP0.self_of_nhds)
  have hκpos : 0 < κ := by
    rw [hκ]
    positivity
  split_ifs with h0
  · have h32 : (0 : ℝ) < |0 - 3 / 2| := by norm_num
    have : 4 * (z.re ^ 2 - z.im ^ 2) < 0 := by
      rw [hx0] at h0
      rw [h0]
      nlinarith
    have : 0 < 2 * |(0 : ℝ) - 3 / 2| * A₀ := by positivity
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hsq) this
  · have hB0 : 0 < 3 / 2 + coneProfile K (y 0) := by
      have := half_le_coneProfile hK (y 0)
      linarith
    have e : 2 * |(0 : ℝ) - 3 / 2| * (3 / 2 + coneProfile K (y 0)) * κ /
        ((0 - 3 / 2) * Real.sqrt (outerCofactor K (3 / 2) (y 0) η₀ (1 / y 0))) =
        -(2 * (3 / 2 + coneProfile K (y 0)) * κ /
          Real.sqrt (outerCofactor K (3 / 2) (y 0) η₀ (1 / y 0))) := by
      rw [show |(0 : ℝ) - 3 / 2| = 3 / 2 by norm_num]
      field_simp
      ring
    rw [e]
    have : 0 < 2 * (3 / 2 + coneProfile K (y 0)) * κ /
        Real.sqrt (outerCofactor K (3 / 2) (y 0) η₀ (1 / y 0)) := by positivity
    linarith

def angleTwoHole (z : ℂ) : ℝ :=
  negHalfArg (coneProfile σ.constK (cuspZeroHeight z)) ((σ.bridgeTwo z).re - 3 / 2)
    (σ.bridgeTwo z).im

theorem isOpen_domTwo : IsOpen σ.domTwo := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hd1 := σ.contDiffAt_discOne hz.1
  have hn : ContDiffAt ℝ ∞ (fun u => ‖σ.discOne u‖) z :=
    hd1.norm ℝ (σ.discOne_ne_zero_of_domTwo hz)
  have hre : ContDiffAt ℝ ∞ (fun u => (exp (-(σ.θ₁ * I)) * σ.discOne u).re) z :=
    reCLM.contDiff.contDiffAt.comp z (contDiffAt_const.mul hd1)
  have hc : ContinuousAt (fun u => ‖σ.discOne u‖ + (exp (-(σ.θ₁ * I)) * σ.discOne u).re) z :=
    (hn.add hre).continuousAt
  have h1 : ∀ᶠ u in nhds z, 0 < u.im :=
    Complex.continuous_im.continuousAt.eventually (lt_mem_nhds hz.1)
  have h2 : ∀ᶠ u in nhds z, 0 < ‖σ.discOne u‖ + (exp (-(σ.θ₁ * I)) * σ.discOne u).re :=
    hc.eventually (lt_mem_nhds hz.2)
  filter_upwards [h1, h2] with u hu1 hu2
  exact ⟨hu1, hu2⟩

theorem contDiffAt_etaOne_of_domTwo {z : ℂ} (hz : z ∈ σ.domTwo) :
    ContDiffAt ℝ ∞ σ.etaOne z :=
  contDiffAt_coneHeight σ.vertexOne_im_pos hz.1 (fun h => σ.discOne_ne_zero_of_domTwo hz (by
    rw [discOne, h, coneDisc_self]))

theorem contDiffAt_cofTwo {z : ℂ} (hz : z ∈ σ.domTwo) : ContDiffAt ℝ ∞ σ.cofTwo z := by
  have hd1 := σ.contDiffAt_discOne hz.1
  have hn : ContDiffAt ℝ ∞ (fun u => ‖σ.discOne u‖) z :=
    hd1.norm ℝ (σ.discOne_ne_zero_of_domTwo hz)
  have hre : ContDiffAt ℝ ∞ (fun u => (exp (-(σ.θ₁ * I)) * σ.discOne u).re) z :=
    reCLM.contDiff.contDiffAt.comp z (contDiffAt_const.mul hd1)
  have h1 := σ.norm_discOne_lt_one hz.1
  have hden : (‖σ.discOne z‖ + (exp (-(σ.θ₁ * I)) * σ.discOne z).re) *
      (1 - ‖σ.discOne z‖) ^ 2 ≠ 0 := by
    have h4 : 0 < 1 - ‖σ.discOne z‖ := by linarith
    have := hz.2
    positivity
  exact contDiffAt_const.div ((hn.add hre).mul ((contDiffAt_const.sub hn).pow 2)) hden

theorem contDiffAt_wallTwo {z : ℂ} (hz : 0 < z.im) : ContDiffAt ℝ ∞ σ.wallTwo z :=
  (imCLM.contDiff.contDiffAt.comp z (contDiffAt_const.mul (σ.contDiffAt_discOne hz))).neg

theorem wallTwo_mul (hθ : σ.θ₂ = 0) (z : ℂ) :
    σ.wallTwo z * normSq (z - conj σ.vertexOne) =
      Real.sin σ.θ₁ * ((z.re - 1 / 4) ^ 2 + z.im ^ 2 - 1 / 16) := by
  have h := σ.im_rot_coneDisc_vertexOne_mul z
  rw [wallTwo, discOne]
  simp only [wallSide, σ.cusp_centre hθ] at h
  linarith

theorem horo_identity (hθ : σ.θ₂ = 0) (x y : ℝ) :
    2 * ((x - σ.width) * (4 * (x ^ 2 - y ^ 2)) + (y - Real.sin σ.θ₁ / 4) * (8 * x * y)) *
        ((x - σ.width) ^ 2 + (y + Real.sin σ.θ₁ / 4) ^ 2) -
      ((x - σ.width) ^ 2 + (y - Real.sin σ.θ₁ / 4) ^ 2) *
        (2 * ((x - σ.width) * (4 * (x ^ 2 - y ^ 2)) + (y + Real.sin σ.θ₁ / 4) * (8 * x * y))) =
      2 * (1 + Real.cos σ.θ₁) * Real.sin σ.θ₁ * y * ((x - 1 / 4) ^ 2 + y ^ 2 - 1 / 16) := by
  have hs := Real.sin_sq_add_cos_sq σ.θ₁
  rw [width, hθ, Real.cos_zero]
  linear_combination (-(Real.sin σ.θ₁ * x * y / 2)) * hs

theorem exists_hasDerivAt_etaOne_horo (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.domTwo) :
    ∃ κ₁ : ℝ, 0 < κ₁ ∧
      HasDerivAt (fun t => σ.etaOne (horoCurve z t)) (σ.wallTwo z * κ₁) 0 := by
  have hv := σ.vertexOne_im_pos
  have hzv : z ≠ σ.vertexOne := fun h => σ.discOne_ne_zero_of_domTwo hz (by
    rw [discOne, h, coneDisc_self])
  have hγ := hasDerivAt_horoCurve hz.1
  have h0 : horoCurve z 0 = z := horoCurve_zero z
  have h := hasDerivAt_coneHeight_curve hv hγ (by rw [h0]; exact hz.1) (by rw [h0]; exact hzv)
  rw [h0] at h
  have hN := normSq_sub_conj_pos hv hz.1
  have hr1 := norm_coneDisc_lt_one hv hz.1
  have hr0 : 0 < ‖coneDisc σ.vertexOne z‖ :=
    norm_pos_iff.2 (coneDisc_ne_zero hv hz.1 hzv)
  refine ⟨σ.vertexOne.im / ((1 - ‖coneDisc σ.vertexOne z‖) ^ 2 * ‖coneDisc σ.vertexOne z‖) *
    (2 * (1 + Real.cos σ.θ₁) * z.im / normSq (z - conj σ.vertexOne)), ?_, ?_⟩
  · have h1 : 0 < 1 - ‖coneDisc σ.vertexOne z‖ := by linarith
    have := σ.one_add_cos_θ₁_pos
    have := hz.1
    positivity
  · refine h.congr_deriv ?_
    have hid := σ.horo_identity hθ z.re z.im
    have hw := σ.wallTwo_mul hθ z
    have e1 : normSq (z - σ.vertexOne) =
        (z.re - σ.width) ^ 2 + (z.im - Real.sin σ.θ₁ / 4) ^ 2 := by
      simp [normSq_apply, vertexOne_re, vertexOne_im]
      ring
    have e2 : normSq (z - conj σ.vertexOne) =
        (z.re - σ.width) ^ 2 + (z.im + Real.sin σ.θ₁ / 4) ^ 2 := by
      simp [normSq_apply, vertexOne_re, vertexOne_im]
      ring
    have e3 : (z - σ.vertexOne).re = z.re - σ.width := by simp [vertexOne_re]
    have e4 : (z - σ.vertexOne).im = z.im - Real.sin σ.θ₁ / 4 := by simp [vertexOne_im]
    have e5 : (z - conj σ.vertexOne).re = z.re - σ.width := by simp [vertexOne_re]
    have e6 : (z - conj σ.vertexOne).im = z.im + Real.sin σ.θ₁ / 4 := by simp [vertexOne_im]
    have e7 : (4 * z ^ 2).re = 4 * (z.re ^ 2 - z.im ^ 2) := by simp [sq]
    have e8 : (4 * z ^ 2).im = 8 * z.re * z.im := by simp [sq]; ring
    rw [e3, e4, e5, e6, e7, e8]
    rw [← e1, ← e2] at hid
    rw [hid]
    have h1 : 1 - ‖coneDisc σ.vertexOne z‖ ≠ 0 := by linarith
    have hw' : σ.wallTwo z = Real.sin σ.θ₁ * ((z.re - 1 / 4) ^ 2 + z.im ^ 2 - 1 / 16) /
        normSq (z - conj σ.vertexOne) := by
      rw [eq_div_iff hN.ne']
      exact hw
    rw [hw']
    field_simp

theorem wallTwo_horo_deriv (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun t : ℝ => σ.wallTwo (horoCurve z t))
        (deriv (fun t : ℝ => σ.wallTwo (horoCurve z t)) 0) 0 ∧
      (σ.wallTwo z = 0 → 0 < deriv (fun t : ℝ => σ.wallTwo (horoCurve z t)) 0) := by
  have hγ := hasDerivAt_horoCurve hz
  have h0 : horoCurve z 0 = z := horoCurve_zero z
  have hd : DifferentiableAt ℝ (fun t : ℝ => σ.wallTwo (horoCurve z t)) 0 := by
    have hw := ((σ.contDiffAt_wallTwo hz).differentiableAt (by simp)).hasFDerivAt
    have := (hw.comp_hasDerivAt_of_eq (0 : ℝ) hγ h0.symm).differentiableAt
    simpa [Function.comp_def] using this
  refine ⟨hd.hasDerivAt, fun hw0 => ?_⟩
  set w' := deriv (fun t : ℝ => σ.wallTwo (horoCurve z t)) 0
  have hD := hasDerivAt_normSq_curve hγ (conj σ.vertexOne)
  rw [h0] at hD
  have hprod := hd.hasDerivAt.mul hD
  have hS : HasDerivAt (fun t : ℝ => Real.sin σ.θ₁ * (((horoCurve z t).re - 1 / 4) ^ 2 +
      (horoCurve z t).im ^ 2 - 1 / 16))
      (Real.sin σ.θ₁ * (2 * (z.re - 1 / 4) * (4 * (z.re ^ 2 - z.im ^ 2)) +
        2 * z.im * (8 * z.re * z.im))) 0 := by
    have hre := hasDerivAt_horoCurve_re hz
    have him := hasDerivAt_horoCurve_im hz
    have := ((((hre.sub_const (1 / 4)).pow 2).add (him.pow 2)).sub_const (1 / 16)).const_mul
      (Real.sin σ.θ₁)
    refine this.congr_deriv ?_
    simp only [horoCurve_zero]
    ring
  have hprod' := hprod.congr_of_eventuallyEq
    (Eventually.of_forall fun t => (σ.wallTwo_mul hθ (horoCurve z t)).symm)
  have huniq := hprod'.unique hS
  have hw0' : σ.wallTwo (horoCurve z 0) = 0 := by rw [h0]; exact hw0
  rw [hw0', zero_mul, add_zero, h0] at huniq
  have hwall : (z.re - 1 / 4) ^ 2 + z.im ^ 2 - 1 / 16 = 0 := by
    have h := σ.wallTwo_mul hθ z
    rw [hw0, zero_mul] at h
    have := σ.sin_θ₁_pos
    rcases mul_eq_zero.1 h.symm with h' | h'
    · linarith
    · exact h'
  have hN := normSq_sub_conj_pos σ.vertexOne_im_pos hz
  have hs := σ.sin_θ₁_pos
  have hpos : 0 < Real.sin σ.θ₁ * (2 * (z.re - 1 / 4) * (4 * (z.re ^ 2 - z.im ^ 2)) +
      2 * z.im * (8 * z.re * z.im)) := by
    apply mul_pos hs
    nlinarith [sq_nonneg z.re]
  rw [← huniq] at hpos
  by_contra hc
  have : w' * normSq (z - conj σ.vertexOne) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) hN.le
  linarith

theorem bridgeTwo_hole_pos (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.domTwo) :
    0 < coneProfile σ.constK (cuspZeroHeight z) - ((σ.bridgeTwo z).re - 3 / 2) := by
  have hK := σ.constK_pos
  have h1 := σ.norm_bridgeTwo_sub hθ hz
  have h2 := σ.norm_bridgeTwo_lt_two hθ hz
  have hG := half_lt_coneProfile hK (cuspZeroHeight_pos hz.1).ne'
  have e1 : ((σ.bridgeTwo z).re - 3 / 2) ^ 2 + (σ.bridgeTwo z).im ^ 2 =
      coneProfile σ.constK (cuspZeroHeight z) ^ 2 := by
    have := sq_add_sq_eq_of_norm h1
    simpa using this
  have e2 : (σ.bridgeTwo z).re ^ 2 + (σ.bridgeTwo z).im ^ 2 < 4 := by
    have := sq_add_sq_eq_of_norm (u := σ.bridgeTwo z) rfl
    nlinarith [norm_nonneg (σ.bridgeTwo z)]
  by_contra hc
  have hle : 3 / 2 + coneProfile σ.constK (cuspZeroHeight z) ≤ (σ.bridgeTwo z).re := by
    linarith [not_lt.1 hc]
  nlinarith

theorem exists_hasDerivAt_angleTwoHole (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.domTwo) :
    ∃ D : ℝ, D < 0 ∧ HasDerivAt (fun t : ℝ => σ.angleTwoHole (horoCurve z t)) D 0 := by
  set K := σ.constK
  have hK := σ.constK_pos
  set η₀ := cuspZeroHeight z with hη₀
  have hη₀pos : 0 < η₀ := cuspZeroHeight_pos hz.1
  set A₀ := coneProfile K η₀ with hA₀
  have hA₀pos : 0 < A₀ := by have := half_le_coneProfile hK η₀; linarith
  have h0 : horoCurve z 0 = z := horoCurve_zero z
  have hev : ∀ᶠ t : ℝ in 𝓝 0, horoCurve z t ∈ σ.domTwo := by
    have := (continuous_horoCurve hz.1).continuousAt (x := 0) |>.preimage_mem_nhds
      (σ.isOpen_domTwo.mem_nhds (by rw [h0]; exact hz))
    exact this
  set η : ℝ → ℝ := fun t => σ.etaOne (horoCurve z t) with hη
  obtain ⟨κ₁, hκ₁, hη'⟩ := σ.exists_hasDerivAt_etaOne_horo hθ hz
  set κ := 4 * K * η 0 / (η 0 ^ 2 + K) ^ 2 * κ₁ with hκ
  have hη0 : η 0 = σ.etaOne z := by simp [hη, h0]
  have hκpos : 0 < κ := by
    have : 0 < η 0 := by rw [hη0]; exact σ.etaOne_pos hz.1
    rw [hκ]
    positivity
  have hB : HasDerivAt (fun t => coneProfile K (η t))
      (σ.wallTwo (horoCurve z 0) * κ) 0 := by
    refine ((hasDerivAt_coneProfile hK (η 0)).comp 0 hη').congr_deriv ?_
    rw [h0, hκ]
    ring
  obtain ⟨hw, hw'⟩ := σ.wallTwo_horo_deriv hθ hz.1
  have hPc : ContDiffAt ℝ ∞ (fun u : ℂ => innerCofactor K η₀ (σ.etaOne u) (σ.cofTwo u)) z := by
    have h1 := σ.contDiffAt_etaOne_of_domTwo hz
    have h2 := σ.contDiffAt_cofTwo hz
    have hηz := σ.etaOne_pos hz.1
    unfold innerCofactor
    have hd : (η₀ ^ 2 + K) * (σ.etaOne z ^ 2 + K) ≠ 0 := by positivity
    have hG'' := (contDiff_coneProfile hK).contDiffAt (x := σ.etaOne z)
    exact (((contDiffAt_const.add (hG''.comp z h1)).add contDiffAt_const).mul
      (contDiffAt_const.sub ((contDiffAt_const.sub (hG''.comp z h1)).pow 2))).mul
      (h2.mul ((contDiffAt_const.mul ((h1.mul contDiffAt_const).add contDiffAt_const)).div
        (contDiffAt_const.mul ((h1.pow 2).add contDiffAt_const)) hd))
  have hPd : DifferentiableAt ℝ
      (fun t : ℝ => innerCofactor K η₀ (η t) (σ.cofTwo (horoCurve z t))) 0 := by
    have := ((hPc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (hasDerivAt_horoCurve hz.1) h0.symm).differentiableAt
    simpa [Function.comp_def, hη] using this
  have hP0 : ∀ᶠ t : ℝ in 𝓝 0, 0 < innerCofactor K η₀ (η t) (σ.cofTwo (horoCurve z t)) := by
    filter_upwards [hev] with t ht
    exact innerCofactor_pos hK hη₀pos (σ.etaOne_pos ht.1) (σ.cofTwo_pos ht)
  have hH : ∀ᶠ t : ℝ in 𝓝 0, ((A₀ + coneProfile K (η t)) ^ 2 - (-(3 / 2) - 3 / 2) ^ 2) *
      ((-(3 / 2) - 3 / 2) ^ 2 - (A₀ - coneProfile K (η t)) ^ 2) =
      σ.wallTwo (horoCurve z t) ^ 2 * innerCofactor K η₀ (η t) (σ.cofTwo (horoCurve z t)) := by
    filter_upwards [hev] with t ht
    have hd := σ.etaOne_mul_cuspZeroHeight_sub hθ ht
    rw [cuspZeroHeight_horoCurve hz.1 t] at hd
    exact innerBridge_heron hK hd
  have hbr : ∀ t, σ.bridgeTwo (horoCurve z t) = twoCircle (3 / 2) (-(3 / 2)) A₀
      (coneProfile K (η t)) (σ.wallTwo (horoCurve z t))
      (innerCofactor K η₀ (η t) (σ.cofTwo (horoCurve z t))) := by
    intro t
    rw [bridgeTwo, innerBridge, cuspZeroHeight_horoCurve hz.1 t]
  have hpos : 0 < A₀ - ((twoCircle (3 / 2) (-(3 / 2)) A₀ (coneProfile K (η 0))
      (σ.wallTwo (horoCurve z 0))
      (innerCofactor K η₀ (η 0) (σ.cofTwo (horoCurve z 0)))).re - 3 / 2) := by
    rw [← hbr 0, h0]
    exact σ.bridgeTwo_hole_pos hθ hz
  have h := hasDerivAt_negHalfArg_twoCircle' (a := 3 / 2) (b := -(3 / 2)) (by norm_num) hA₀pos hB
    hw hPd hP0 hH hpos
  have he : (fun t : ℝ => σ.angleTwoHole (horoCurve z t)) = fun t : ℝ => negHalfArg A₀
      ((twoCircle (3 / 2) (-(3 / 2)) A₀ (coneProfile K (η t)) (σ.wallTwo (horoCurve z t))
        (innerCofactor K η₀ (η t) (σ.cofTwo (horoCurve z t)))).re - 3 / 2)
      (twoCircle (3 / 2) (-(3 / 2)) A₀ (coneProfile K (η t)) (σ.wallTwo (horoCurve z t))
        (innerCofactor K η₀ (η t) (σ.cofTwo (horoCurve z t)))).im := by
    funext t
    rw [angleTwoHole, hbr t, cuspZeroHeight_horoCurve hz.1 t]
  rw [he]
  refine ⟨_, ?_, h⟩
  have hsq := Real.sqrt_pos.2 (hP0.self_of_nhds)
  split_ifs with hw0
  · rw [h0] at hw0
    have := hw' hw0
    have h3 : (0 : ℝ) < 2 * |-(3 / 2) - 3 / 2| * A₀ := by positivity
    have : 0 < deriv (fun t : ℝ => σ.wallTwo (horoCurve z t)) 0 *
        Real.sqrt (innerCofactor K η₀ (η 0) (σ.cofTwo (horoCurve z 0))) /
        (2 * |-(3 / 2) - 3 / 2| * A₀) := by positivity
    linarith
  · have hB0 : 0 < coneProfile K (η 0) := by
      have := half_le_coneProfile hK (η 0)
      linarith
    have e : 2 * |-(3 / 2) - 3 / 2| * coneProfile K (η 0) * κ /
        ((-(3 / 2) - 3 / 2) * Real.sqrt (innerCofactor K η₀ (η 0) (σ.cofTwo (horoCurve z 0)))) =
        -(2 * coneProfile K (η 0) * κ /
          Real.sqrt (innerCofactor K η₀ (η 0) (σ.cofTwo (horoCurve z 0)))) := by
      rw [show |-(3 / 2) - (3 / 2 : ℝ)| = 3 by norm_num]
      field_simp
      ring
    rw [e]
    have : 0 < 2 * coneProfile K (η 0) * κ /
        Real.sqrt (innerCofactor K η₀ (η 0) (σ.cofTwo (horoCurve z 0))) := by positivity
    linarith

def angleHole (a b : ℝ) (z : ℂ) : ℝ :=
  coneStep a b (horoX z) * σ.angleZeroHole z + (1 - coneStep a b (horoX z)) * σ.angleTwoHole z

def cornerZero (a b : ℝ) (z : ℂ) : ℂ :=
  (3 / 2 : ℂ) + ((coneProfile σ.constK (cuspZeroHeight z) : ℝ) : ℂ) *
    exp ((σ.angleHole a b z : ℂ) * I)

theorem bridgeZero_hole_sq {z : ℂ} (hz : 0 < z.im) :
    ((σ.bridgeZero z).re - 3 / 2) ^ 2 + (σ.bridgeZero z).im ^ 2 =
      coneProfile σ.constK (cuspZeroHeight z) ^ 2 := by
  have := sq_add_sq_eq_of_norm (σ.norm_bridgeZero_sub hz)
  simpa using this

theorem bridgeTwo_hole_sq (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.domTwo) :
    ((σ.bridgeTwo z).re - 3 / 2) ^ 2 + (σ.bridgeTwo z).im ^ 2 =
      coneProfile σ.constK (cuspZeroHeight z) ^ 2 := by
  have := sq_add_sq_eq_of_norm (σ.norm_bridgeTwo_sub hθ hz)
  simpa using this

theorem holeModulus_pos (z : ℂ) : 0 < coneProfile σ.constK (cuspZeroHeight z) := by
  have := half_le_coneProfile σ.constK_pos (cuspZeroHeight z)
  linarith

theorem contDiffAt_holeModulus {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (fun u => coneProfile σ.constK (cuspZeroHeight u)) z :=
  (contDiff_coneProfile σ.constK_pos).contDiffAt.comp z (contDiffAt_cuspZeroHeight hz)

theorem contDiffAt_angleZeroHole {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ σ.angleZeroHole z := by
  have hb := σ.contDiffAt_bridgeZero hz
  exact contDiffAt_halfArg_comp (σ.contDiffAt_holeModulus hz)
    ((reCLM.contDiff.contDiffAt.comp z hb).sub contDiffAt_const)
    (imCLM.contDiff.contDiffAt.comp z hb) (σ.three_halves_hole_pos hz)

theorem contDiffAt_angleTwoHole (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.domTwo) :
    ContDiffAt ℝ ∞ σ.angleTwoHole z := by
  have hb := σ.contDiffAt_bridgeTwo hz
  exact contDiffAt_negHalfArg_comp (σ.contDiffAt_holeModulus hz.1)
    ((reCLM.contDiff.contDiffAt.comp z hb).sub contDiffAt_const)
    (imCLM.contDiff.contDiffAt.comp z hb) (σ.bridgeTwo_hole_pos hθ hz)

theorem contDiffAt_horoX {z : ℂ} (hz : 0 < z.im) : ContDiffAt ℝ ∞ horoX z := by
  have hz0 : 4 * z ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have h : ContDiffAt ℝ ∞ (fun u : ℂ => -1 / (4 * u)) z :=
    (contDiffAt_const.div (contDiffAt_const.mul contDiffAt_id) hz0).restrict_scalars ℝ
  exact reCLM.contDiff.contDiffAt.comp z h

theorem contDiffAt_angleHole (hθ : σ.θ₂ = 0) (a b : ℝ) {z : ℂ} (hz : z ∈ σ.domTwo) :
    ContDiffAt ℝ ∞ (σ.angleHole a b) z := by
  have hν : ContDiffAt ℝ ∞ (fun u => coneStep a b (horoX u)) z :=
    (contDiff_coneStep a b).contDiffAt.comp z (contDiffAt_horoX hz.1)
  exact (hν.mul (σ.contDiffAt_angleZeroHole hz.1)).add
    ((contDiffAt_const.sub hν).mul (σ.contDiffAt_angleTwoHole hθ hz))

theorem angleZeroHole_le_angleTwoHole (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.domTwo)
    (hx : 0 ≤ z.re) (hw : 0 ≤ σ.wallTwo z) : σ.angleZeroHole z ≤ σ.angleTwoHole z := by
  have hK := σ.constK_pos
  set G := coneProfile σ.constK (cuspZeroHeight z)
  have hG := σ.holeModulus_pos z
  have h0 := σ.bridgeZero_hole_sq hz.1
  have h2 := σ.bridgeTwo_hole_sq hθ hz
  have hp0 := σ.three_halves_hole_pos hz.1
  have hp2 := σ.bridgeTwo_hole_pos hθ hz
  have hI0 : 0 ≤ (σ.bridgeZero z).im := by
    rcases eq_or_lt_of_le hx with h | h
    · have : (σ.bridgeZero z).im = 0 := by
        simp [bridgeZero, outerBridge, ← h]
      rw [this]
    · exact (outerBridge_im_pos σ.constK_pos (Or.inl rfl) hz.1 (cuspZeroHeight_pos hz.1)
        (by simpa using hz.1) h).le
  have hI2 : 0 ≤ (σ.bridgeTwo z).im := by
    rcases eq_or_lt_of_le hw with h | h
    · have : (σ.bridgeTwo z).im = 0 := by
        simp [bridgeTwo, innerBridge, ← h]
      rw [this]
    · exact (innerBridge_im_pos σ.constK_pos (cuspZeroHeight_pos hz.1) (σ.etaOne_pos hz.1)
        (σ.cofTwo_pos hz) h).le
  have hβ0 : 0 ≤ σ.angleZeroHole z := by
    unfold angleZeroHole halfArg
    have := Real.arctan_nonneg.2 (div_nonneg hI0 hp0.le)
    linarith
  have hγπ : σ.angleTwoHole z ≤ Real.pi := by
    unfold angleTwoHole negHalfArg
    have := Real.arctan_nonneg.2 (div_nonneg hI2 hp2.le)
    linarith
  have hcos0 := halfArg_cos hG hp0 h0
  have hcos2 := negHalfArg_cos hG hp2 h2
  have hR : (σ.bridgeTwo z).re < (σ.bridgeZero z).re := by
    have n0 := sq_add_sq_eq_of_norm (σ.norm_bridgeZero hz.1)
    have n2 : (σ.bridgeTwo z).re ^ 2 + (σ.bridgeTwo z).im ^ 2 < 4 := by
      have := sq_add_sq_eq_of_norm (u := σ.bridgeTwo z) rfl
      have := σ.norm_bridgeTwo_lt_two hθ hz
      nlinarith [norm_nonneg (σ.bridgeTwo z)]
    have hR2 : 2 < 3 / 2 + coneProfile σ.constK z.im := by
      have := half_lt_coneProfile hK hz.1.ne'
      linarith
    nlinarith
  by_contra hc
  have hlt : σ.angleTwoHole z < σ.angleZeroHole z := not_le.1 hc
  have hγ0 : 0 ≤ σ.angleTwoHole z := le_of_lt negHalfArg_mem.1
  have hβπ : σ.angleZeroHole z ≤ Real.pi := (halfArg_mem _ _ _).2.le
  have := Real.cos_le_cos_of_nonneg_of_le_pi hγ0 hβπ hlt.le
  rw [angleZeroHole, angleTwoHole, hcos0, hcos2] at this
  have : (σ.bridgeZero z).re - 3 / 2 ≤ (σ.bridgeTwo z).re - 3 / 2 := by
    rwa [div_le_div_iff_of_pos_right hG] at this
  linarith

theorem exists_hasDerivAt_angleHole (hθ : σ.θ₂ = 0) {a b : ℝ} (hab : a < b) {z : ℂ}
    (hz : z ∈ σ.domTwo) (hβγ : σ.angleZeroHole z ≤ σ.angleTwoHole z) :
    ∃ D : ℝ, D < 0 ∧ HasDerivAt (fun t : ℝ => σ.angleHole a b (horoCurve z t)) D 0 := by
  obtain ⟨d₀, hd₀, h₀⟩ := σ.exists_hasDerivAt_angleZeroHole hz.1
  obtain ⟨d₂, hd₂, h₂⟩ := σ.exists_hasDerivAt_angleTwoHole hθ hz
  have hX : HasDerivAt (fun t : ℝ => horoX (horoCurve z t)) 1 0 := by
    have e : (fun t : ℝ => horoX (horoCurve z t)) = fun t => horoX z + t :=
      funext fun t => horoX_horoCurve hz.1 t
    rw [e]
    simpa using (hasDerivAt_id' (0 : ℝ)).const_add (horoX z)
  have hν := (hasDerivAt_coneStep a b (horoX (horoCurve z 0))).comp (0 : ℝ) hX
  have h := (hν.mul h₀).add (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hν).mul h₂)
  refine ⟨_, ?_, h⟩
  simp only [Function.comp_apply, horoCurve_zero, Pi.sub_apply, mul_one]
  have hn := deriv_coneStep_nonneg hab (horoX z)
  have h0 := coneStep_nonneg a b (horoX z)
  have h1 := coneStep_le_one a b (horoX z)
  have hc : coneStep a b (horoX z) * d₀ + (1 - coneStep a b (horoX z)) * d₂ < 0 := by
    rcases eq_or_lt_of_le h0 with h' | h'
    · rw [← h']
      linarith
    · have : coneStep a b (horoX z) * d₀ < 0 := mul_neg_of_pos_of_neg h' hd₀
      have : (1 - coneStep a b (horoX z)) * d₂ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hd₂.le
      linarith
  have hd : deriv (coneStep a b) (horoX z) * (σ.angleZeroHole z - σ.angleTwoHole z) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hn (by linarith)
  nlinarith

theorem det_fderiv_cornerZero_ne_zero (hθ : σ.θ₂ = 0) {a b : ℝ} (hab : a < b) {z : ℂ}
    (hz : z ∈ σ.domTwo) (hβγ : σ.angleZeroHole z ≤ σ.angleTwoHole z) :
    (fderiv ℝ (σ.cornerZero a b) z).det ≠ 0 := by
  have hK := σ.constK_pos
  obtain ⟨D, hD, hDd⟩ := σ.exists_hasDerivAt_angleHole hθ hab hz hβγ
  have hη := cuspZeroHeight_pos hz.1
  have hS := hasDerivAt_coneProfile hK (cuspZeroHeight z)
  have hρd : DifferentiableAt ℝ cuspZeroHeight z :=
    (contDiffAt_cuspZeroHeight hz.1).differentiableAt (by simp)
  have hΘd := (σ.contDiffAt_angleHole hθ a b hz).differentiableAt (by simp)
  have hγ := hasDerivAt_horoCurve hz.1
  have hργ : ∀ᶠ t : ℝ in 𝓝 0, cuspZeroHeight (horoCurve z t) = cuspZeroHeight z :=
    Eventually.of_forall fun t => cuspZeroHeight_horoCurve hz.1 t
  have hρN : HasDerivAt (fun t : ℝ => cuspZeroHeight (z + t * z)) (cuspZeroHeight z) 0 := by
    have e : (fun t : ℝ => cuspZeroHeight (z + t * z)) =
        fun t : ℝ => ((1 + t) ^ 2 * normSq z) / ((1 + t) * z.im) := by
      funext t
      have : z + (t : ℂ) * z = ((1 + t : ℝ) : ℂ) * z := by push_cast; ring
      rw [cuspZeroHeight, this, map_mul, normSq_ofReal]
      simp
      ring
    rw [e]
    have h1 : HasDerivAt (fun t : ℝ => (1 + t) ^ 2 * normSq z) (2 * normSq z) 0 := by
      have := (((hasDerivAt_id' (0 : ℝ)).const_add 1).pow 2).mul_const (normSq z)
      refine this.congr_deriv ?_
      simp
    have h2 : HasDerivAt (fun t : ℝ => (1 + t) * z.im) z.im 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).const_add 1).mul_const z.im
      refine this.congr_deriv ?_
      simp
    have h3 := h1.div h2 (by simpa using hz.1.ne')
    refine h3.congr_deriv ?_
    simp [cuspZeroHeight]
    field_simp
    ring
  have hΘN : HasDerivAt (fun t : ℝ => σ.angleHole a b (z + t * z))
      (fderiv ℝ (σ.angleHole a b) z z) 0 := by
    have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ) * z) z 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const z).const_add z
    have hF' : HasFDerivAt (σ.angleHole a b) (fderiv ℝ (σ.angleHole a b) z)
        (z + ((0 : ℝ) : ℂ) * z) := by simpa using hΘd.hasFDerivAt
    exact hF'.comp_hasDerivAt 0 hl
  have hdet := det_fderiv_polar (c := 3 / 2) (S := coneProfile σ.constK) (ρ := cuspZeroHeight)
    (Θ := σ.angleHole a b) (V := 4 * z ^ 2) (N := z) hS hρd hΘd hγ (horoCurve_zero z) hργ hDd
    hρN hΘN
  have hfun : (fun u => (3 / 2 : ℂ) + ((coneProfile σ.constK (cuspZeroHeight u) : ℝ) : ℂ) *
      exp ((σ.angleHole a b u : ℂ) * I)) = σ.cornerZero a b := rfl
  rw [hfun] at hdet
  intro h0
  rw [h0, zero_mul] at hdet
  have hS0 := σ.holeModulus_pos z
  have hS' : 0 < 4 * σ.constK * cuspZeroHeight z / (cuspZeroHeight z ^ 2 + σ.constK) ^ 2 := by
    positivity
  have : coneProfile σ.constK (cuspZeroHeight z) *
      (4 * σ.constK * cuspZeroHeight z / (cuspZeroHeight z ^ 2 + σ.constK) ^ 2) * D *
        cuspZeroHeight z < 0 := by
    have : 0 < coneProfile σ.constK (cuspZeroHeight z) *
        (4 * σ.constK * cuspZeroHeight z / (cuspZeroHeight z ^ 2 + σ.constK) ^ 2) := by positivity
    have := mul_neg_of_pos_of_neg this hD
    exact mul_neg_of_neg_of_pos this hη
  linarith

theorem cornerZero_eq_bridgeZero {a b : ℝ} (hab : a < b) {z : ℂ} (hz : 0 < z.im)
    (hX : b ≤ horoX z) : σ.cornerZero a b z = σ.bridgeZero z := by
  have hp := halfArg_polar (σ.holeModulus_pos z) (σ.three_halves_hole_pos hz)
    (σ.bridgeZero_hole_sq hz)
  rw [cornerZero, angleHole, coneStep_eq_one hab hX]
  simp only [one_mul, sub_self, zero_mul, add_zero]
  rw [angleZeroHole, ← hp]
  apply Complex.ext <;> simp

theorem cornerZero_eq_bridgeTwo (hθ : σ.θ₂ = 0) {a b : ℝ} (hab : a < b) {z : ℂ}
    (hz : z ∈ σ.domTwo) (hX : horoX z ≤ a) : σ.cornerZero a b z = σ.bridgeTwo z := by
  have hp := negHalfArg_polar (σ.holeModulus_pos z) (σ.bridgeTwo_hole_pos hθ hz)
    (σ.bridgeTwo_hole_sq hθ hz)
  rw [cornerZero, angleHole, coneStep_eq_zero hab hX]
  simp only [zero_mul, sub_zero, one_mul, zero_add]
  rw [angleTwoHole, ← hp]
  apply Complex.ext <;> simp

theorem cornerZero_refl_zero {a b : ℝ} (hab : a < b) {z : ℂ} (hX : b ≤ horoX z)
    (hX' : b ≤ horoX (σ.refl 0 z)) :
    σ.cornerZero a b (σ.refl 0 z) = conj (σ.cornerZero a b z) := by
  have e1 : cuspZeroHeight (σ.refl 0 z) = cuspZeroHeight z := by
    simp [cuspZeroHeight, refl, normSq_apply]
  have hβ : σ.angleZeroHole (σ.refl 0 z) = -σ.angleZeroHole z := by
    rw [angleZeroHole, angleZeroHole, σ.bridgeZero_refl_zero, e1, conj_re, conj_im, halfArg_neg]
  rw [cornerZero, cornerZero, angleHole, angleHole, coneStep_eq_one hab hX,
    coneStep_eq_one hab hX', hβ, e1]
  simp only [one_mul, sub_self, zero_mul, add_zero, map_add, map_mul, Complex.conj_ofReal,
    map_div₀, map_ofNat]
  rw [← Complex.exp_conj]
  congr 3
  simp

theorem cornerZero_refl_two (hθ : σ.θ₂ = 0) {a b : ℝ} (hab : a < b) {z : ℂ} (hz : 0 < z.im)
    (hX : horoX z ≤ a) (hX' : horoX (σ.refl 2 z) ≤ a) :
    σ.cornerZero a b (σ.refl 2 z) = conj (σ.cornerZero a b z) := by
  have e1 := σ.cuspZeroHeight_refl_two hθ hz
  have hγ : σ.angleTwoHole (σ.refl 2 z) = 2 * Real.pi - σ.angleTwoHole z := by
    rw [angleTwoHole, angleTwoHole, σ.bridgeTwo_refl_two hθ hz, e1, conj_re, conj_im,
      negHalfArg_neg]
  rw [cornerZero, cornerZero, angleHole, angleHole, coneStep_eq_zero hab hX,
    coneStep_eq_zero hab hX', hγ, e1]
  simp only [zero_mul, sub_zero, one_mul, zero_add, map_add, map_mul, Complex.conj_ofReal,
    map_div₀, map_ofNat]
  rw [exp_two_pi_sub_mul_I]

end ConeShape

end GC.Seifert

import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsCornerMaps
import DifferentialGeometry.Compat.Ch567.Tensor.LinearAlgebra.ComplexDeterminant

/-!
# The corner map at the cusp `0` of the K16f fold

Packet K16f, tier 3 (design `docs/geometrization/handoffs/20261004-design-k16f-fold.md`, §4–§6).
The weight `foldMu` is a non-increasing smooth step. On the horoball `599/1000 < heightOne x y` of
the cusp `0`, `cornerZero` is smooth, equals `bridgeZero` where `foldMu (holeX x y) = 0` and
`bridgeTwo` where it is `1`, and its angle `angleHole` strictly decreases along each horocycle,
from `π` on the wall `holeX = -1/2` to `0` on the wall `holeX = 0`. In the coordinate
`w = -1/(4z)` it reads `3/2 + bridgeSigma (Im w) e^{i angleHole}`, so `polar_partials_det` gives a
nonzero Jacobian; the same computation covers `bridgeTwo` on the upper half-plane and, through
`foldMirror`, `cornerHalf`. On `-1/2 ≤ holeX ≤ 0` the modulus `‖cornerZero z - 3/2‖` fixes the
height and the angle fixes `holeX`, so `cornerZero` is injective there.
-/

set_option autoImplicit false

open scoped ContDiff Topology

namespace GC.Seifert

theorem foldMu_eq_one {t : ℝ} (ht : t ≤ -(35 / 100)) : foldMu t = 1 := by
  unfold foldMu
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by norm_num)]
  linarith

theorem foldMu_eq_zero {t : ℝ} (ht : -(31 / 100) ≤ t) : foldMu t = 0 := by
  unfold foldMu
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)

theorem exists_hasDerivAt_foldMu (t : ℝ) : ∃ D : ℝ, D ≤ 0 ∧ HasDerivAt foldMu D t := by
  have hd : DifferentiableAt ℝ Real.smoothTransition ((-(31 / 100) - t) / (1 / 25)) :=
    (Real.smoothTransition.contDiffAt (n := 1)).differentiableAt (by simp)
  have hl : HasDerivAt (fun s : ℝ => (-(31 / 100) - s) / (1 / 25)) (-1 / (1 / 25)) t :=
    ((hasDerivAt_id t).const_sub (-(31 / 100))).div_const (1 / 25)
  refine ⟨deriv Real.smoothTransition ((-(31 / 100) - t) / (1 / 25)) * (-1 / (1 / 25)), ?_,
    hd.hasDerivAt.comp t hl⟩
  have := Real.smoothTransition.monotone.deriv_nonneg
    (x := (-(31 / 100) - t) / (1 / 25))
  nlinarith

theorem three_halves_lt_bridgeRe0 {x y : ℝ} (hy : 0 < y) (h : 599 / 1000 < heightOne x y) :
    3 / 2 < bridgeRe0 x y := by
  have hρ := two_le_bridgeRho y
  have hp := heightOne_pos (x := x) hy
  have hs : bridgeSigma (heightOne x y) < 1322 / 1000 := by
    unfold bridgeSigma
    have hq : 0 < 1 + 4 * heightOne x y ^ 2 := by positivity
    have hh : (599 / 1000) ^ 2 < heightOne x y ^ 2 := by nlinarith
    have : 2 / (1 + 4 * heightOne x y ^ 2) < 822 / 1000 := by
      rw [div_lt_iff₀ hq]
      nlinarith
    linarith
  have h0 := half_lt_bridgeSigma (heightOne x y)
  unfold bridgeRe0
  nlinarith

private theorem neg_inv_four_mul_re_im {z : ℂ} (hz : 0 < z.im) :
    (-1 / (4 * z)).re = holeX z.re z.im ∧ (-1 / (4 * z)).im = heightOne z.re z.im := by
  have hs : 0 < z.re ^ 2 + z.im ^ 2 := by positivity
  constructor
  · simp only [Complex.div_re, Complex.normSq_apply, holeX]
    simp
    field_simp
  · simp only [Complex.div_im, Complex.normSq_apply, heightOne]
    simp
    field_simp

theorem coe_neg_inv_four_mul_re {z : ℂ} (hz : 0 < z.im) : (-1 / (4 * z)).re = holeX z.re z.im :=
  (neg_inv_four_mul_re_im hz).1

theorem coe_neg_inv_four_mul_im {z : ℂ} (hz : 0 < z.im) : (-1 / (4 * z)).im = heightOne z.re z.im :=
  (neg_inv_four_mul_re_im hz).2

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem contDiffAt_bridgeSigma_comp {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (fun w => bridgeSigma (f w)) z := by
  unfold bridgeSigma
  fun_prop (disch := positivity)

private theorem contDiffAt_heightOne_comp {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ ∞ f z)
    (hg : ContDiffAt ℝ ∞ g z) (hz : 0 < g z) :
    ContDiffAt ℝ ∞ (fun w => heightOne (f w) (g w)) z := by
  unfold heightOne
  fun_prop (disch := positivity)

private theorem contDiffAt_holeX_comp {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ ∞ f z)
    (hg : ContDiffAt ℝ ∞ g z) (hz : 0 < g z) :
    ContDiffAt ℝ ∞ (fun w => holeX (f w) (g w)) z := by
  unfold holeX
  fun_prop (disch := positivity)

end Smooth

private theorem contDiffAt_re {z : ℂ} : ContDiffAt ℝ ∞ (fun w : ℂ => w.re) z :=
  Complex.reCLM.contDiff.contDiffAt

private theorem contDiffAt_im {z : ℂ} : ContDiffAt ℝ ∞ (fun w : ℂ => w.im) z :=
  Complex.imCLM.contDiff.contDiffAt

private theorem contDiffAt_angleHole {z : ℂ} (hz : 0 < z.im)
    (h : 599 / 1000 < heightOne z.re z.im) :
    ContDiffAt ℝ ∞ (fun w : ℂ => angleHole w.re w.im) z := by
  have h1 := contDiffAt_angleZeroHole hz (three_halves_lt_bridgeRe0 hz h)
  have h2 := contDiffAt_angleTwoHole hz
  have h3 : ContDiffAt ℝ ∞ (fun w : ℂ => foldMu (holeX w.re w.im)) z := by
    have hX := contDiffAt_holeX_comp contDiffAt_re contDiffAt_im hz
    unfold foldMu
    exact Real.smoothTransition.contDiffAt.comp z (by fun_prop)
  unfold angleHole
  fun_prop

theorem contDiffAt_cornerZero {z : ℂ} (hz : 0 < z.im) (h : 599 / 1000 < heightOne z.re z.im) :
    ContDiffAt ℝ ∞ cornerZero z := by
  have h1 := contDiffAt_angleHole hz h
  have h2 := contDiffAt_bridgeSigma_comp (contDiffAt_heightOne_comp contDiffAt_re contDiffAt_im hz)
  have h3 : ContDiffAt ℝ ∞ (fun w : ℂ => ((angleHole w.re w.im : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z h1
  have h4 : ContDiffAt ℝ ∞ (fun w : ℂ => ((bridgeSigma (heightOne w.re w.im) : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z h2
  unfold cornerZero
  fun_prop

theorem exists_hasDerivAt_angleHole {X Y : ℝ} (hY : 599 / 1000 < Y) :
    ∃ D : ℝ, D < 0 ∧ HasDerivAt (fun t => angleHole (holeInvRe t Y) (holeInvIm t Y)) D X := by
  have hY0 : 0 < Y := by linarith
  have hre : 3 / 2 < bridgeRe0 (holeInvRe X Y) (holeInvIm X Y) :=
    three_halves_lt_bridgeRe0 (holeInvIm_pos hY0) (by rw [heightOne_holeInv hY0]; exact hY)
  obtain ⟨b, hb, hbd⟩ := exists_hasDerivAt_angleZeroHole hY0 hre
  obtain ⟨g, hg, hgd⟩ := exists_hasDerivAt_angleTwoHole (X := X) hY0
  obtain ⟨m, hm, hmd⟩ := exists_hasDerivAt_foldMu X
  have hfun : (fun t => angleHole (holeInvRe t Y) (holeInvIm t Y)) = fun t =>
      (1 - foldMu t) * angleZeroHole (holeInvRe t Y) (holeInvIm t Y) +
        foldMu t * angleTwoHole (holeInvRe t Y) (holeInvIm t Y) := by
    funext t
    rw [angleHole, holeX_holeInv hY0]
  rw [hfun]
  refine ⟨_, ?_, ((hmd.const_sub 1).mul hbd).add (hmd.mul hgd)⟩
  have hμ0 : 0 ≤ foldMu X := Real.smoothTransition.nonneg _
  have hμ1 : foldMu X ≤ 1 := Real.smoothTransition.le_one _
  have hβ : angleZeroHole (holeInvRe X Y) (holeInvIm X Y) < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  have hγ : Real.pi / 2 < angleTwoHole (holeInvRe X Y) (holeInvIm X Y) := by
    unfold angleTwoHole
    linarith [Real.arctan_lt_pi_div_two (bridgeIm2 (holeInvRe X Y) (holeInvIm X Y) /
      (3 / 2 - bridgeRe2 (holeInvRe X Y) (holeInvIm X Y)))]
  have hmγ : m * (angleTwoHole (holeInvRe X Y) (holeInvIm X Y) -
      angleZeroHole (holeInvRe X Y) (holeInvIm X Y)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hm (by linarith)
  rcases le_total b g with hbg | hbg
  · nlinarith [mul_nonneg (sub_nonneg.2 hμ1) (sub_nonneg.2 hbg)]
  · nlinarith [mul_nonneg hμ0 (sub_nonneg.2 hbg)]

private theorem hasDerivAt_bridgeSigma (s : ℝ) :
    HasDerivAt bridgeSigma (-(16 * s) / (1 + 4 * s ^ 2) ^ 2) s := by
  have h1 : HasDerivAt (fun s : ℝ => 1 + 4 * s ^ 2) (8 * s) s := by
    convert ((hasDerivAt_pow 2 s).const_mul 4).const_add 1 using 1
    push_cast
    ring
  have hne : (1 + 4 * s ^ 2) ≠ 0 := by positivity
  have h2 := ((hasDerivAt_const s (2 : ℝ)).div h1 hne).const_add (1 / 2)
  change HasDerivAt (fun t => 1 / 2 + 2 / (1 + 4 * t ^ 2)) _ s
  convert h2 using 1
  field_simp
  ring

private theorem det_fderiv_polar {A : ℂ → ℝ} {R : ℝ → ℝ} {c w : ℂ} {R' a : ℝ}
    (hA : DifferentiableAt ℝ A w) (hR : HasDerivAt R R' w.im)
    (ha : HasDerivAt (fun t : ℝ => A (w + t)) a 0) :
    (fderiv ℝ (fun u : ℂ => c + (R u.im : ℂ) * Complex.exp (Complex.I * (A u : ℂ))) w).det =
      -(R w.im * R' * a) := by
  have hb : HasDerivAt (fun t : ℝ => A (w + t * Complex.I)) (fderiv ℝ A w Complex.I) 0 := by
    have hl : HasDerivAt (fun t : ℝ => w + (t : ℂ) * Complex.I) Complex.I 0 := by
      simpa using (((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I).const_add w)
    have hA' : HasFDerivAt A (fderiv ℝ A w) (w + ((0 : ℝ) : ℂ) * Complex.I) := by
      simpa using hA.hasFDerivAt
    exact hA'.comp_hasDerivAt (0 : ℝ) hl
  have hRi : HasDerivAt (fun t : ℝ => R (w.im + t)) R' 0 :=
    HasDerivAt.comp_const_add w.im 0 (by rwa [add_zero])
  have hFd : DifferentiableAt ℝ
      (fun u : ℂ => c + (R u.im : ℂ) * Complex.exp (Complex.I * (A u : ℂ))) w := by
    have h1 : DifferentiableAt ℝ (fun u : ℂ => ((R u.im : ℝ) : ℂ)) w :=
      Complex.ofRealCLM.differentiableAt.comp w
        (hR.differentiableAt.comp w Complex.imCLM.differentiableAt)
    have h2 : DifferentiableAt ℝ (fun u : ℂ => ((A u : ℝ) : ℂ)) w :=
      Complex.ofRealCLM.differentiableAt.comp w hA
    fun_prop
  have hx : HasDerivAt
      (fun t : ℝ => c + (R (w + t).im : ℂ) * Complex.exp (Complex.I * (A (w + t) : ℂ)))
      ((R w.im : ℂ) * a * Complex.I * Complex.exp (Complex.I * (A w : ℂ))) 0 := by
    have e : (fun t : ℝ => c + (R (w + t).im : ℂ) * Complex.exp (Complex.I * (A (w + t) : ℂ))) =
        fun t : ℝ => c + (R w.im : ℂ) * Complex.exp (Complex.I * (A (w + t) : ℂ)) := by
      funext t
      simp
    rw [e]
    have h := ((ha.ofReal_comp.const_mul Complex.I).cexp.const_mul (R w.im : ℂ)).const_add c
    convert h using 1
    simp only [Complex.ofReal_zero, add_zero]
    ring
  have hy : HasDerivAt (fun t : ℝ => c + (R (w + t * Complex.I).im : ℂ) *
        Complex.exp (Complex.I * (A (w + t * Complex.I) : ℂ)))
      (((R' : ℂ) + Complex.I * R w.im * (fderiv ℝ A w Complex.I : ℝ)) *
        Complex.exp (Complex.I * (A w : ℂ))) 0 := by
    have e : (fun t : ℝ => c + (R (w + t * Complex.I).im : ℂ) *
        Complex.exp (Complex.I * (A (w + t * Complex.I) : ℂ))) =
        fun t : ℝ => c + (R (w.im + t) : ℂ) *
          Complex.exp (Complex.I * (A (w + t * Complex.I) : ℂ)) := by
      funext t
      simp
    rw [e]
    have h := (hRi.ofReal_comp.mul (hb.ofReal_comp.const_mul Complex.I).cexp).const_add c
    convert h using 1
    simp only [Complex.ofReal_zero, add_zero, zero_mul]
    ring
  rw [det_fderiv_eq_of_partials hFd hx hy]
  exact polar_partials_det _ _ _ _ _

private theorem det_fderiv_neg_inv_pos {z : ℂ} (hz : z ≠ 0) :
    0 < (fderiv ℝ (fun w : ℂ => -1 / (4 * w)) z).det := by
  have h4 : (4 : ℂ) * z ≠ 0 := mul_ne_zero (by norm_num) hz
  have hl4 : HasDerivAt (fun w : ℂ => 4 * w) 4 z := by
    simpa using (hasDerivAt_id z).const_mul (4 : ℂ)
  have hd : HasDerivAt (fun w : ℂ => -1 / (4 * w)) ((0 * (4 * z) - (-1) * 4) / (4 * z) ^ 2) z :=
    (hasDerivAt_const z (-1 : ℂ)).div hl4 h4
  set c : ℂ := (0 * (4 * z) - (-1) * 4) / (4 * z) ^ 2 with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact div_ne_zero (by norm_num) (pow_ne_zero 2 h4)
  have hd' : HasDerivAt (fun w : ℂ => -1 / (4 * w)) c (z + ((0 : ℝ) : ℂ)) := by
    simpa using hd
  have hd'' : HasDerivAt (fun w : ℂ => -1 / (4 * w)) c (z + ((0 : ℝ) : ℂ) * Complex.I) := by
    simpa using hd
  have hl1 : HasDerivAt (fun t : ℝ => z + (t : ℂ)) 1 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add z)
  have hlI : HasDerivAt (fun t : ℝ => z + (t : ℂ) * Complex.I) Complex.I 0 := by
    simpa using (((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I).const_add z)
  have hx := hd'.comp (0 : ℝ) hl1
  have hy := hd''.comp (0 : ℝ) hlI
  rw [det_fderiv_eq_of_partials (hd.differentiableAt.restrictScalars ℝ) hx hy]
  simp only [mul_one, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_sub]
  have : 0 < Complex.normSq c := Complex.normSq_pos.2 hc0
  rw [Complex.normSq_apply] at this
  linarith

private theorem holeX_eq_holeInvRe (x y : ℝ) : holeX x y = holeInvRe x y := rfl

private theorem heightOne_eq_holeInvIm (x y : ℝ) : heightOne x y = holeInvIm x y := rfl

private theorem det_fderiv_hole_ne_zero {ang : ℝ → ℝ → ℝ} {F : ℂ → ℂ} {z : ℂ} (hz : 0 < z.im)
    (hang : ContDiffAt ℝ ∞ (fun w : ℂ => ang w.re w.im) z)
    (hder : ∃ D : ℝ, D < 0 ∧ HasDerivAt (fun t => ang (holeInvRe t (heightOne z.re z.im))
      (holeInvIm t (heightOne z.re z.im))) D (holeX z.re z.im))
    (hF : ∀ᶠ u in 𝓝 z, F u = 3 / 2 + (bridgeSigma (heightOne u.re u.im) : ℂ) *
      Complex.exp (Complex.I * (ang u.re u.im : ℂ))) :
    (fderiv ℝ F z).det ≠ 0 := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hφφ : ∀ u : ℂ, u ≠ 0 → -1 / (4 * (-1 / (4 * u))) = u := by
    intro u hu
    field_simp
  have hφd : ∀ u : ℂ, u ≠ 0 → DifferentiableAt ℝ (fun w : ℂ => -1 / (4 * w)) u := by
    intro u hu
    have h4 : (4 : ℂ) * u ≠ 0 := mul_ne_zero (by norm_num) hu
    exact ((differentiableAt_const (-1 : ℂ)).div
      ((differentiableAt_id).const_mul (4 : ℂ)) h4).restrictScalars ℝ
  have hw₀ : 0 < (-1 / (4 * z)).im := by
    rw [coe_neg_inv_four_mul_im hz]
    exact heightOne_pos hz
  have hw₀0 : -1 / (4 * z) ≠ 0 := fun h => by simp [h] at hw₀
  have hAd : DifferentiableAt ℝ (fun u : ℂ => ang (-1 / (4 * u)).re (-1 / (4 * u)).im)
      (-1 / (4 * z)) := by
    have h1 : DifferentiableAt ℝ (fun w : ℂ => ang w.re w.im) (-1 / (4 * (-1 / (4 * z)))) := by
      rw [hφφ z hz0]
      exact hang.differentiableAt (by simp)
    exact h1.comp (-1 / (4 * z)) (hφd _ hw₀0)
  have hGd : DifferentiableAt ℝ (fun u : ℂ => 3 / 2 + (bridgeSigma u.im : ℂ) *
      Complex.exp (Complex.I * (ang (-1 / (4 * u)).re (-1 / (4 * u)).im : ℂ))) (-1 / (4 * z)) := by
    have h1 : DifferentiableAt ℝ (fun u : ℂ => ((bridgeSigma u.im : ℝ) : ℂ)) (-1 / (4 * z)) :=
      Complex.ofRealCLM.differentiableAt.comp _
        ((hasDerivAt_bridgeSigma _).differentiableAt.comp _ Complex.imCLM.differentiableAt)
    have h2 : DifferentiableAt ℝ
        (fun u : ℂ => ((ang (-1 / (4 * u)).re (-1 / (4 * u)).im : ℝ) : ℂ)) (-1 / (4 * z)) :=
      Complex.ofRealCLM.differentiableAt.comp _ hAd
    fun_prop
  have heq : F =ᶠ[𝓝 z] (fun u : ℂ => 3 / 2 + (bridgeSigma u.im : ℂ) *
      Complex.exp (Complex.I * (ang (-1 / (4 * u)).re (-1 / (4 * u)).im : ℂ))) ∘
        (fun w : ℂ => -1 / (4 * w)) := by
    filter_upwards [hF, (Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds hz]
      with u hu hu'
    have hu0 : u ≠ 0 := fun h => by simp [h] at hu'
    rw [hu, Function.comp_apply, hφφ u hu0, coe_neg_inv_four_mul_im hu']
  rw [heq.fderiv_eq, fderiv_comp z hGd (hφd z hz0), ContinuousLinearMap.det,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
  obtain ⟨D, hD, hDd⟩ := hder
  have ha : HasDerivAt (fun t : ℝ => ang (-1 / (4 * (-1 / (4 * z) + t))).re
      (-1 / (4 * (-1 / (4 * z) + t))).im) D 0 := by
    have e : (fun t : ℝ => ang (-1 / (4 * (-1 / (4 * z) + t))).re
        (-1 / (4 * (-1 / (4 * z) + t))).im) = fun t : ℝ =>
          ang (holeInvRe (holeX z.re z.im + t) (heightOne z.re z.im))
            (holeInvIm (holeX z.re z.im + t) (heightOne z.re z.im)) := by
      funext t
      have him : 0 < (-1 / (4 * z) + t).im := by simpa using hw₀
      rw [coe_neg_inv_four_mul_re him, coe_neg_inv_four_mul_im him, holeX_eq_holeInvRe,
        heightOne_eq_holeInvIm]
      simp [coe_neg_inv_four_mul_re hz, coe_neg_inv_four_mul_im hz]
    rw [e]
    exact HasDerivAt.comp_const_add (holeX z.re z.im) 0 (by rwa [add_zero])
  have hG := det_fderiv_polar (c := 3 / 2) hAd (hasDerivAt_bridgeSigma _) ha
  have hφ := det_fderiv_neg_inv_pos hz0
  have hG' : LinearMap.det ((fderiv ℝ (fun u : ℂ => 3 / 2 + (bridgeSigma u.im : ℂ) *
      Complex.exp (Complex.I * (ang (-1 / (4 * u)).re (-1 / (4 * u)).im : ℂ)))
        (-1 / (4 * z)) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) < 0 := by
    rw [← ContinuousLinearMap.det, hG]
    set s := (-1 / (4 * z)).im
    have hσ := half_lt_bridgeSigma s
    have hd : -(16 * s) / (1 + 4 * s ^ 2) ^ 2 < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by positivity)
    have : 0 < bridgeSigma s * (-(16 * s) / (1 + 4 * s ^ 2) ^ 2) * D :=
      mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (by linarith) hd) hD
    linarith
  exact (mul_neg_of_neg_of_pos hG' hφ).ne

theorem det_fderiv_cornerZero_ne_zero {z : ℂ} (hz : 0 < z.im)
    (h : 599 / 1000 < heightOne z.re z.im) : (fderiv ℝ cornerZero z).det ≠ 0 :=
  det_fderiv_hole_ne_zero hz (contDiffAt_angleHole hz h) (exists_hasDerivAt_angleHole h)
    (Filter.Eventually.of_forall fun u => (rfl : cornerZero u = _))

theorem det_fderiv_bridgeTwo_ne_zero {z : ℂ} (hz : 0 < z.im) : (fderiv ℝ bridgeTwo z).det ≠ 0 := by
  refine det_fderiv_hole_ne_zero hz (contDiffAt_angleTwoHole hz)
    (exists_hasDerivAt_angleTwoHole (heightOne_pos hz)) ?_
  filter_upwards [(Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds hz] with u hu
  rw [← bridgeTwo_sub_eq_polar hu]
  ring

theorem cornerZero_eq_bridgeZero {z : ℂ} (hz : 0 < z.im) (h : 599 / 1000 < heightOne z.re z.im)
    (hX : -(31 / 100) ≤ holeX z.re z.im) : cornerZero z = bridgeZero z := by
  have hp := bridgeZero_sub_eq_polar hz (three_halves_lt_bridgeRe0 hz h)
  have ha : angleHole z.re z.im = angleZeroHole z.re z.im := by
    rw [angleHole, foldMu_eq_zero hX]
    ring
  rw [cornerZero, ha, ← hp]
  ring

theorem cornerZero_eq_bridgeTwo {z : ℂ} (hz : 0 < z.im) (hX : holeX z.re z.im ≤ -(35 / 100)) :
    cornerZero z = bridgeTwo z := by
  have hp := bridgeTwo_sub_eq_polar hz
  have ha : angleHole z.re z.im = angleTwoHole z.re z.im := by
    rw [angleHole, foldMu_eq_one hX]
    ring
  rw [cornerZero, ha, ← hp]
  ring

private theorem exp_I_mul_ofReal (A : ℝ) :
    Complex.exp (Complex.I * (A : ℂ)) = ⟨Real.cos A, Real.sin A⟩ := by
  rw [mul_comm, Complex.exp_mul_I]
  apply Complex.ext <;> simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]

private theorem cornerZero_re (z : ℂ) : (cornerZero z).re =
    3 / 2 + bridgeSigma (heightOne z.re z.im) * Real.cos (angleHole z.re z.im) := by
  simp [cornerZero, exp_I_mul_ofReal]

private theorem cornerZero_im (z : ℂ) : (cornerZero z).im =
    bridgeSigma (heightOne z.re z.im) * Real.sin (angleHole z.re z.im) := by
  simp [cornerZero, exp_I_mul_ofReal]

private theorem norm_polar_sub (c : ℂ) {r : ℝ} (A : ℝ) (hr : 0 < r) :
    ‖c + (r : ℂ) * Complex.exp (Complex.I * (A : ℂ)) - c‖ = r := by
  rw [add_sub_cancel_left, norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

theorem norm_cornerZero_sub (z : ℂ) : ‖cornerZero z - 3 / 2‖ = bridgeSigma (heightOne z.re z.im) :=
  norm_polar_sub _ _ (by linarith [half_lt_bridgeSigma (heightOne z.re z.im)])

theorem angleHole_holeInv_zero {Y : ℝ} (hY : 599 / 1000 < Y) :
    angleHole (holeInvRe 0 Y) (holeInvIm 0 Y) = 0 := by
  have hY0 : 0 < Y := by linarith
  rw [angleHole, holeX_holeInv hY0, foldMu_eq_zero (by norm_num)]
  have h0 : holeInvRe 0 Y = 0 := by simp [holeInvRe]
  simp [angleZeroHole, bridgeIm0, h0]

private theorem wallTwo_holeInv {t Y : ℝ} (hY : 0 < Y) :
    wallTwo (holeInvRe t Y) (holeInvIm t Y) = (1 + 2 * t) / (16 * (t ^ 2 + Y ^ 2)) := by
  have hs : 0 < t ^ 2 + Y ^ 2 := by positivity
  unfold wallTwo holeInvRe holeInvIm
  field_simp
  ring

theorem angleHole_holeInv_neg_half {Y : ℝ} (hY : 0 < Y) :
    angleHole (holeInvRe (-(1 / 2)) Y) (holeInvIm (-(1 / 2)) Y) = Real.pi := by
  rw [angleHole, holeX_holeInv hY, foldMu_eq_one (by norm_num)]
  have hw : wallTwo (holeInvRe (-(1 / 2)) Y) (holeInvIm (-(1 / 2)) Y) = 0 := by
    rw [wallTwo_holeInv hY]
    norm_num
  rw [angleTwoHole, bridgeIm2, hw]
  simp

private theorem strictAnti_angleHole {Y : ℝ} (hY : 599 / 1000 < Y) :
    StrictAnti (fun t => angleHole (holeInvRe t Y) (holeInvIm t Y)) := by
  apply strictAnti_of_deriv_neg
  intro t
  obtain ⟨D, hD, hd⟩ := exists_hasDerivAt_angleHole (X := t) hY
  rw [hd.deriv]
  exact hD

theorem angleHole_mem_Icc {X Y : ℝ} (hY : 599 / 1000 < Y) (h0 : -(1 / 2) ≤ X) (h1 : X ≤ 0) :
    angleHole (holeInvRe X Y) (holeInvIm X Y) ∈ Set.Icc 0 Real.pi := by
  have hA := (strictAnti_angleHole hY).antitone
  constructor
  · have := hA h1
    simp only at this
    rwa [angleHole_holeInv_zero hY] at this
  · have := hA h0
    simp only at this
    rwa [angleHole_holeInv_neg_half (by linarith)] at this

theorem angleHole_mem_Ioo {X Y : ℝ} (hY : 599 / 1000 < Y) (h0 : -(1 / 2) < X) (h1 : X < 0) :
    angleHole (holeInvRe X Y) (holeInvIm X Y) ∈ Set.Ioo 0 Real.pi := by
  have hA := strictAnti_angleHole hY
  constructor
  · have := hA h1
    simp only at this
    rwa [angleHole_holeInv_zero hY] at this
  · have := hA h0
    simp only at this
    rwa [angleHole_holeInv_neg_half (by linarith)] at this

private theorem angleHole_eq_holeInv {z : ℂ} (hz : 0 < z.im) :
    angleHole z.re z.im = angleHole (holeInvRe (holeX z.re z.im) (heightOne z.re z.im))
      (holeInvIm (holeX z.re z.im) (heightOne z.re z.im)) := by
  rw [(holeInv_holeX hz).1, (holeInv_holeX hz).2]

private theorem bridgeSigma_inj {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : bridgeSigma a = bridgeSigma b) : a = b := by
  unfold bridgeSigma at h
  have hpa : 0 < 1 + 4 * a ^ 2 := by positivity
  have hpb : 0 < 1 + 4 * b ^ 2 := by positivity
  have h2 : a ^ 2 = b ^ 2 := by
    field_simp at h
    linarith
  exact (pow_left_inj₀ ha.le hb.le two_ne_zero).1 h2

theorem cornerZero_injOn : Set.InjOn cornerZero {z : ℂ | 0 < z.im ∧
    599 / 1000 < heightOne z.re z.im ∧ -(1 / 2) ≤ holeX z.re z.im ∧ holeX z.re z.im ≤ 0} := by
  rintro z ⟨hz, h, h0, h1⟩ w ⟨hw, h', h0', h1'⟩ he
  have hn := norm_cornerZero_sub z
  rw [he, norm_cornerZero_sub w] at hn
  have hh : heightOne w.re w.im = heightOne z.re z.im :=
    bridgeSigma_inj (heightOne_pos hw) (heightOne_pos hz) hn
  have hre := congrArg Complex.re he
  rw [cornerZero_re, cornerZero_re, hh] at hre
  have hσ := half_lt_bridgeSigma (heightOne z.re z.im)
  have hcos : Real.cos (angleHole z.re z.im) = Real.cos (angleHole w.re w.im) := by
    have : bridgeSigma (heightOne z.re z.im) * (Real.cos (angleHole z.re z.im) -
        Real.cos (angleHole w.re w.im)) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left (by linarith)
    linarith
  have hz' := angleHole_mem_Icc (X := holeX z.re z.im) h h0 h1
  have hw' := angleHole_mem_Icc (X := holeX w.re w.im) h' h0' h1'
  rw [← angleHole_eq_holeInv hz] at hz'
  rw [← angleHole_eq_holeInv hw] at hw'
  have hang := Real.injOn_cos hz' hw' hcos
  rw [angleHole_eq_holeInv hz, angleHole_eq_holeInv hw, hh] at hang
  have hX := (strictAnti_angleHole h).injective hang
  apply Complex.ext
  · rw [← (holeInv_holeX (x := z.re) hz).1, ← (holeInv_holeX (x := w.re) hw).1, hX, hh]
  · rw [← (holeInv_holeX (x := z.re) hz).2, ← (holeInv_holeX (x := w.re) hw).2, hX, hh]

theorem cornerZero_im_nonneg {z : ℂ} (hz : 0 < z.im) (h : 599 / 1000 < heightOne z.re z.im)
    (h0 : -(1 / 2) ≤ holeX z.re z.im) (h1 : holeX z.re z.im ≤ 0) : 0 ≤ (cornerZero z).im := by
  have hA := angleHole_mem_Icc h h0 h1
  rw [← angleHole_eq_holeInv hz] at hA
  rw [cornerZero_im]
  have hσ := half_lt_bridgeSigma (heightOne z.re z.im)
  exact mul_nonneg (by linarith) (Real.sin_nonneg_of_nonneg_of_le_pi hA.1 hA.2)

theorem cornerZero_im_pos {z : ℂ} (hz : 0 < z.im) (h : 599 / 1000 < heightOne z.re z.im)
    (h0 : -(1 / 2) < holeX z.re z.im) (h1 : holeX z.re z.im < 0) : 0 < (cornerZero z).im := by
  have hA := angleHole_mem_Ioo h h0 h1
  rw [← angleHole_eq_holeInv hz] at hA
  rw [cornerZero_im]
  have hσ := half_lt_bridgeSigma (heightOne z.re z.im)
  exact mul_pos (by linarith) (Real.sin_pos_of_pos_of_lt_pi hA.1 hA.2)

theorem cornerZero_neg_conj {z : ℂ} (hz : 0 < z.im) (h : 599 / 1000 < heightOne z.re z.im)
    (hX : |holeX z.re z.im| ≤ 31 / 100) :
    cornerZero (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (cornerZero z) := by
  have hX' := abs_le.1 hX
  have hre : (-(starRingEnd ℂ) z).re = -z.re := by simp
  have him : (-(starRingEnd ℂ) z).im = z.im := by simp
  have hh : heightOne (-z.re) z.im = heightOne z.re z.im := by simp [heightOne]
  have hxn : holeX (-z.re) z.im = -holeX z.re z.im := by
    simp only [holeX, neg_sq]
    ring
  rw [cornerZero_eq_bridgeZero hz h hX'.1, cornerZero_eq_bridgeZero (by rwa [him])
    (by rwa [hre, him, hh]) (by rw [hre, him, hxn]; linarith), bridgeZero_neg_conj]

theorem cornerZero_wall_zero {y : ℝ} (hy : 0 < y) (h : 599 / 1000 < heightOne 0 y) :
    cornerZero ⟨0, y⟩ = (bridgeRho y : ℂ) := by
  rw [cornerZero_eq_bridgeZero (z := ⟨0, y⟩) hy h (by norm_num [holeX])]
  have hI := bridge_identity_zero (x := 0) hy
  have hs : bridgeSigma (heightOne 0 y) = bridgeRho y - 3 / 2 := by
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hI
    linarith
  apply Complex.ext
  · simp only [bridgeZero_re, Complex.ofReal_re]
    rw [bridgeRe0, hs]
    ring
  · simp [bridgeZero_im, bridgeIm0]

theorem bridgeTwo_of_wallTwo_eq_zero {z : ℂ} (hz : 0 < z.im) (hw : wallTwo z.re z.im = 0) :
    bridgeTwo z = ((3 / 2 - bridgeSigma (heightOne z.re z.im) : ℝ) : ℂ) := by
  have hI := bridge_identity_two (x := z.re) hz
  rw [hw] at hI
  have hs : bridgeSigma (heightOne (1 / 2 - z.re) z.im) =
      3 - bridgeSigma (heightOne z.re z.im) := by
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hI
    linarith
  apply Complex.ext
  · simp only [bridgeTwo_re, Complex.ofReal_re]
    rw [bridgeRe2, hs]
    ring
  · simp [bridgeTwo_im, bridgeIm2, hw]

private theorem hasFDerivAt_foldMirror (z : ℂ) :
    HasFDerivAt foldMirror (-(Complex.conjCLE : ℂ →L[ℝ] ℂ)) z :=
  ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt (x := z)).const_sub (1 / 2 : ℂ)

private theorem hasFDerivAt_neg_conj (z : ℂ) :
    HasFDerivAt (fun u : ℂ => -(starRingEnd ℂ) u) (-(Complex.conjCLE : ℂ →L[ℝ] ℂ)) z :=
  ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt (x := z)).neg

theorem contDiffAt_cornerHalf {z : ℂ} (hz : 0 < z.im)
    (h : 599 / 1000 < heightOne (1 / 2 - z.re) z.im) : ContDiffAt ℝ ∞ cornerHalf z := by
  have hC := contDiffAt_cornerZero (z := foldMirror z) (by rwa [foldMirror_im])
    (by rwa [foldMirror_re, foldMirror_im])
  have hM : ContDiffAt ℝ ∞ foldMirror z :=
    contDiffAt_const.sub (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.contDiffAt
  exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.contDiffAt.comp z (hC.comp z hM)).neg

private theorem det_neg_conj :
    LinearMap.det ((-(Complex.conjCLE : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = -1 := by
  rw [LinearMap.det_complex]
  simp

theorem det_fderiv_cornerHalf_ne_zero {z : ℂ} (hz : 0 < z.im)
    (h : 599 / 1000 < heightOne (1 / 2 - z.re) z.im) : (fderiv ℝ cornerHalf z).det ≠ 0 := by
  have hz' : 0 < (foldMirror z).im := by rwa [foldMirror_im]
  have h' : 599 / 1000 < heightOne (foldMirror z).re (foldMirror z).im := by
    rwa [foldMirror_re, foldMirror_im]
  have hC := ((contDiffAt_cornerZero hz' h').differentiableAt (by simp)).hasFDerivAt
  have hH := (hasFDerivAt_neg_conj (cornerZero (foldMirror z))).comp z
    (hC.comp z (hasFDerivAt_foldMirror z))
  have he : ((fun u : ℂ => -(starRingEnd ℂ) u) ∘ cornerZero ∘ foldMirror) = cornerHalf := rfl
  rw [he] at hH
  have hd := det_fderiv_cornerZero_ne_zero hz' h'
  rw [hH.fderiv, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.det_comp, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, det_neg_conj]
  rw [ContinuousLinearMap.det] at hd
  simpa using hd

end GC.Seifert

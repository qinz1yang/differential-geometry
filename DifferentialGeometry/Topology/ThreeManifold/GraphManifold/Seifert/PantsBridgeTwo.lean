import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsBridges
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsCollars

/-!
# The bridge between the cusps `0` and `1/2` of the pants map

Packet K16f, tier 3. Properties of `bridgeTwo` and `angleTwoHole` from
`Seifert/PantsBridges.lean` on the upper half-plane. Both are smooth where `Im z > 0`
(`contDiffAt_bridgeTwo`, `contDiffAt_angleTwoHole`): the radicand `bridgeQ2` is positive and
`3/2 - bridgeRe2` does not vanish. The mirror `z ↦ 1/2 - z̄` fixes `wallTwo` and `bridgeQ2` and
reverses `bridgeRe2` (`bridgeTwo_mirror`). The reflection in the semicircle wall preserves the
heights of the cusps `0` and `1/2` and reverses the sign of `wallTwo`, so it conjugates the
bridge (`bridgeTwo_wallReflection`) and reflects the angle (`angleTwoHole_wallReflection`).
`bridgeTwo z - 3/2` has modulus `bridgeSigma (heightOne z.re z.im)` and argument `angleTwoHole`
(`bridgeTwo_sub_eq_polar`). Along the horocycle `t ↦ (holeInvRe t Y, holeInvIm t Y)` of the
cusp `0` this modulus is constant and the angle strictly decreases
(`exists_hasDerivAt_angleTwoHole`).
-/

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped ContDiff

namespace GC.Seifert

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

private theorem contDiffAt_sigmaPair_comp {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ ∞ f z)
    (hg : ContDiffAt ℝ ∞ g z) (hz : 0 < g z) :
    ContDiffAt ℝ ∞ (fun w => bridgeSigma (heightOne (1 / 2 - f w) (g w))) z ∧
      ContDiffAt ℝ ∞ (fun w => bridgeSigma (heightOne (f w) (g w))) z :=
  ⟨contDiffAt_bridgeSigma_comp (contDiffAt_heightOne_comp (by fun_prop) hg hz),
    contDiffAt_bridgeSigma_comp (contDiffAt_heightOne_comp hf hg hz)⟩

private theorem contDiffAt_bridgeRe2_comp {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ ∞ f z)
    (hg : ContDiffAt ℝ ∞ g z) (hz : 0 < g z) :
    ContDiffAt ℝ ∞ (fun w => bridgeRe2 (f w) (g w)) z := by
  obtain ⟨h1, h2⟩ := contDiffAt_sigmaPair_comp hf hg hz
  unfold bridgeRe2
  fun_prop

private theorem contDiffAt_bridgeQ2_comp {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ ∞ f z)
    (hg : ContDiffAt ℝ ∞ g z) (hz : 0 < g z) :
    ContDiffAt ℝ ∞ (fun w => bridgeQ2 (f w) (g w)) z := by
  obtain ⟨h1, h2⟩ := contDiffAt_sigmaPair_comp hf hg hz
  have h0 : ContDiffAt ℝ ∞ (fun w => bridgeP2 (f w) (g w)) z := by
    unfold bridgeP2
    fun_prop (disch := positivity)
  unfold bridgeQ2
  fun_prop

private theorem contDiffAt_bridgeIm2_comp {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ ∞ f z)
    (hg : ContDiffAt ℝ ∞ g z) (hz : 0 < g z) :
    ContDiffAt ℝ ∞ (fun w => bridgeIm2 (f w) (g w)) z := by
  have hq := (contDiffAt_bridgeQ2_comp hf hg hz).sqrt (bridgeQ2_pos hz).ne'
  have hw : ContDiffAt ℝ ∞ (fun w => wallTwo (f w) (g w)) z := by
    unfold wallTwo
    fun_prop
  exact hw.mul hq

end Smooth

private theorem contDiffAt_re {z : ℂ} : ContDiffAt ℝ ∞ (fun w : ℂ => w.re) z :=
  Complex.reCLM.contDiff.contDiffAt

private theorem contDiffAt_im {z : ℂ} : ContDiffAt ℝ ∞ (fun w : ℂ => w.im) z :=
  Complex.imCLM.contDiff.contDiffAt

theorem contDiffAt_bridgeRe2 {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (fun w : ℂ => bridgeRe2 w.re w.im) z :=
  contDiffAt_bridgeRe2_comp contDiffAt_re contDiffAt_im hz

theorem contDiffAt_bridgeIm2 {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (fun w : ℂ => bridgeIm2 w.re w.im) z :=
  contDiffAt_bridgeIm2_comp contDiffAt_re contDiffAt_im hz

theorem contDiffAt_bridgeTwo {z : ℂ} (hz : 0 < z.im) : ContDiffAt ℝ ∞ bridgeTwo z := by
  have h : bridgeTwo = fun w : ℂ =>
      Complex.equivRealProdCLM.symm (bridgeRe2 w.re w.im, bridgeIm2 w.re w.im) := by
    funext w
    apply Complex.ext <;> simp [bridgeTwo_re, bridgeTwo_im]
  rw [h]
  exact Complex.equivRealProdCLM.symm.contDiff.contDiffAt.comp z
    ((contDiffAt_bridgeRe2 hz).prodMk (contDiffAt_bridgeIm2 hz))

private theorem bridgeRe2_half_sub (x y : ℝ) : bridgeRe2 (1 / 2 - x) y = -bridgeRe2 x y := by
  unfold bridgeRe2
  rw [sub_sub_cancel]
  ring

private theorem bridgeIm2_half_sub (x y : ℝ) : bridgeIm2 (1 / 2 - x) y = bridgeIm2 x y := by
  have hP : bridgeP2 (1 / 2 - x) y = bridgeP2 x y := by
    unfold bridgeP2
    rw [sub_sub_cancel]
    ring
  have hW : wallTwo (1 / 2 - x) y = wallTwo x y := by
    unfold wallTwo
    ring
  unfold bridgeIm2 bridgeQ2
  rw [hP, hW, sub_sub_cancel]
  ring_nf

theorem bridgeTwo_mirror (z : ℂ) :
    bridgeTwo (1 / 2 - (starRingEnd ℂ) z) = -(starRingEnd ℂ) (bridgeTwo z) := by
  have hre : (1 / 2 - (starRingEnd ℂ) z).re = 1 / 2 - z.re := by simp
  have him : (1 / 2 - (starRingEnd ℂ) z).im = z.im := by simp
  apply Complex.ext
  · rw [bridgeTwo_re, hre, him, bridgeRe2_half_sub]
    simp [bridgeTwo_re]
  · rw [bridgeTwo_im, hre, him, bridgeIm2_half_sub]
    simp [bridgeTwo_im]

theorem bridgeTwo_wallReflection (z : ℍ) :
    bridgeTwo ((wallReflection 2 • z : ℍ) : ℂ) = (starRingEnd ℂ) (bridgeTwo z) := by
  have hw := (wallReflection 2 • z).im_pos
  have hz := z.im_pos
  have h1 : heightOne (wallReflection 2 • z).re (wallReflection 2 • z).im =
      heightOne z.re z.im := by
    have h := cuspHeight_wallReflection (i := 2) (j := 1) (by decide) z
    rw [cuspHeight_one_eq, cuspHeight_one_eq] at h
    exact h
  have h0 : heightOne (1 / 2 - (wallReflection 2 • z).re) (wallReflection 2 • z).im =
      heightOne (1 / 2 - z.re) z.im := by
    have h := cuspHeight_wallReflection (i := 2) (j := 0) (by decide) z
    rw [cuspHeight_zero_eq, cuspHeight_zero_eq] at h
    unfold heightOne
    convert h using 3 <;> simp only [coe_re, coe_im] <;> ring
  have hRe : bridgeRe2 (wallReflection 2 • z).re (wallReflection 2 • z).im =
      bridgeRe2 z.re z.im := by
    unfold bridgeRe2
    rw [h0, h1]
  have hsq : bridgeIm2 (wallReflection 2 • z).re (wallReflection 2 • z).im ^ 2 =
      bridgeIm2 z.re z.im ^ 2 := by
    have a := bridgeRe2_sub_sq_add_bridgeIm2_sq (x := (wallReflection 2 • z).re) hw
    have b := bridgeRe2_sub_sq_add_bridgeIm2_sq (x := z.re) hz
    rw [hRe, h1] at a
    linarith
  obtain ⟨c, hc, hW⟩ := wallSide_wallReflection_smul 2 z
  rw [wallSide_two, wallSide_two] at hW
  have hWw : wallTwo (wallReflection 2 • z).re (wallReflection 2 • z).im =
      -(c * wallTwo z.re z.im) := hW
  have hIm : bridgeIm2 (wallReflection 2 • z).re (wallReflection 2 • z).im =
      -bridgeIm2 z.re z.im := by
    have qw := Real.sqrt_pos.2 (bridgeQ2_pos (x := (wallReflection 2 • z).re) hw)
    have qz := Real.sqrt_pos.2 (bridgeQ2_pos (x := z.re) hz)
    unfold bridgeIm2 at hsq ⊢
    rw [hWw] at hsq ⊢
    rcases eq_or_ne (wallTwo z.re z.im) 0 with ha | ha
    · simp [ha]
    · have hm : (c * Real.sqrt (bridgeQ2 (wallReflection 2 • z).re (wallReflection 2 • z).im) -
          Real.sqrt (bridgeQ2 z.re z.im)) *
          (c * Real.sqrt (bridgeQ2 (wallReflection 2 • z).re (wallReflection 2 • z).im) +
          Real.sqrt (bridgeQ2 z.re z.im)) = 0 := by
        have h2 : wallTwo z.re z.im ^ 2 *
            ((c * Real.sqrt (bridgeQ2 (wallReflection 2 • z).re (wallReflection 2 • z).im) -
              Real.sqrt (bridgeQ2 z.re z.im)) *
            (c * Real.sqrt (bridgeQ2 (wallReflection 2 • z).re (wallReflection 2 • z).im) +
              Real.sqrt (bridgeQ2 z.re z.im))) = 0 := by
          linear_combination hsq
        exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero 2 ha)
      have hcs := (mul_eq_zero.1 hm).resolve_right (by positivity)
      linear_combination (-wallTwo z.re z.im) * hcs
  apply Complex.ext
  · simp only [bridgeTwo_re, Complex.conj_re, coe_re, coe_im]
    exact hRe
  · simp only [bridgeTwo_im, Complex.conj_im, coe_re, coe_im]
    exact hIm

theorem angleTwoHole_wallReflection (z : ℍ) :
    angleTwoHole (wallReflection 2 • z).re (wallReflection 2 • z).im =
      2 * Real.pi - angleTwoHole z.re z.im := by
  have h := bridgeTwo_wallReflection z
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [bridgeTwo_re, bridgeTwo_im, Complex.conj_re, Complex.conj_im, coe_re,
    coe_im] at hre him
  unfold angleTwoHole
  rw [hre, him, neg_div, Real.arctan_neg]
  ring

theorem contDiffAt_angleTwoHole {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (fun w : ℂ => angleTwoHole w.re w.im) z := by
  have h1 := contDiffAt_bridgeRe2 hz
  have h2 := contDiffAt_bridgeIm2 hz
  have hne : 3 / 2 - bridgeRe2 z.re z.im ≠ 0 := by linarith [bridgeRe2_lt z.re z.im]
  unfold angleTwoHole
  exact contDiffAt_const.sub ((h2.div (contDiffAt_const.sub h1) hne).arctan)

private theorem eq_polar_of_re_neg {a b r : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hn : a ^ 2 + b ^ 2 = r ^ 2) :
    (⟨-a, b⟩ : ℂ) =
      (r : ℂ) * Complex.exp (Complex.I * ((Real.pi - Real.arctan (b / a) : ℝ) : ℂ)) := by
  have hs : Real.sqrt (1 + (b / a) ^ 2) = r / a := by
    rw [show 1 + (b / a) ^ 2 = (r / a) ^ 2 by field_simp; linarith]
    exact Real.sqrt_sq (by positivity)
  apply Complex.ext
  · simp [Complex.exp_re, Real.cos_arctan, hs]
    field_simp
  · simp [Complex.exp_im, Real.sin_arctan, hs]
    field_simp

theorem bridgeTwo_sub_eq_polar {z : ℂ} (hz : 0 < z.im) :
    bridgeTwo z - 3 / 2 = (bridgeSigma (heightOne z.re z.im) : ℂ) *
      Complex.exp (Complex.I * (angleTwoHole z.re z.im : ℂ)) := by
  have he : bridgeTwo z - 3 / 2 = ⟨-(3 / 2 - bridgeRe2 z.re z.im), bridgeIm2 z.re z.im⟩ := by
    apply Complex.ext <;> simp [bridgeTwo_re, bridgeTwo_im]
  rw [he]
  exact eq_polar_of_re_neg (by linarith [half_lt_bridgeSigma (heightOne z.re z.im)])
    (by linarith [bridgeRe2_lt z.re z.im])
    (by rw [← bridgeRe2_sub_sq_add_bridgeIm2_sq hz]; ring)

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

private theorem heightOne_half_sub_holeInv {t Y : ℝ} (hY : 0 < Y) :
    heightOne (1 / 2 - holeInvRe t Y) (holeInvIm t Y) = Y / ((1 + 2 * t) ^ 2 + 4 * Y ^ 2) := by
  have hs : 0 < t ^ 2 + Y ^ 2 := by positivity
  have hd : 0 < (1 + 2 * t) ^ 2 + 4 * Y ^ 2 := by positivity
  unfold heightOne holeInvRe holeInvIm
  field_simp
  ring

private theorem wallTwo_holeInv {t Y : ℝ} (hY : 0 < Y) :
    wallTwo (holeInvRe t Y) (holeInvIm t Y) = (1 + 2 * t) / (16 * (t ^ 2 + Y ^ 2)) := by
  have hs : 0 < t ^ 2 + Y ^ 2 := by positivity
  unfold wallTwo holeInvRe holeInvIm
  field_simp
  ring

theorem exists_hasDerivAt_angleTwoHole {X Y : ℝ} (hY : 0 < Y) :
    ∃ D : ℝ, D < 0 ∧ HasDerivAt (fun t => angleTwoHole (holeInvRe t Y) (holeInvIm t Y)) D X := by
  have hDp : 0 < (1 + 2 * X) ^ 2 + 4 * Y ^ 2 := by positivity
  have hS : 0 < X ^ 2 + Y ^ 2 := by positivity
  have hY0 : HasDerivAt (fun t => Y / ((1 + 2 * t) ^ 2 + 4 * Y ^ 2))
      (-(4 * Y / ((1 + 2 * X) ^ 2 + 4 * Y ^ 2) ^ 2 * (1 + 2 * X))) X := by
    have h1 : HasDerivAt (fun t : ℝ => (1 + 2 * t) ^ 2 + 4 * Y ^ 2) (4 * (1 + 2 * X)) X := by
      have h := ((((hasDerivAt_id' X).const_mul 2).const_add 1).fun_pow 2).add_const (4 * Y ^ 2)
      convert h using 1
      push_cast
      ring
    convert (hasDerivAt_const X Y).div h1 hDp.ne' using 1
    field_simp
    ring
  have hy0p : 0 < Y / ((1 + 2 * X) ^ 2 + 4 * Y ^ 2) := by positivity
  have hσ : 0 < bridgeSigma (Y / ((1 + 2 * X) ^ 2 + 4 * Y ^ 2)) := by
    linarith [half_lt_bridgeSigma (Y / ((1 + 2 * X) ^ 2 + 4 * Y ^ 2))]
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = bridgeSigma (Y / ((1 + 2 * X) ^ 2 + 4 * Y ^ 2)) *
      (16 * (Y / ((1 + 2 * X) ^ 2 + 4 * Y ^ 2)) /
        (1 + 4 * (Y / ((1 + 2 * X) ^ 2 + 4 * Y ^ 2)) ^ 2) ^ 2) *
      (4 * Y / ((1 + 2 * X) ^ 2 + 4 * Y ^ 2) ^ 2) / 3 := ⟨_, rfl⟩
  have hkp : 0 < k := by
    rw [hk]
    positivity
  have hR : HasDerivAt (fun t => 3 / 2 - bridgeRe2 (holeInvRe t Y) (holeInvIm t Y))
      (-(k * (1 + 2 * X))) X := by
    have e : (fun t => 3 / 2 - bridgeRe2 (holeInvRe t Y) (holeInvIm t Y)) = fun t =>
        3 / 2 - (bridgeSigma (Y / ((1 + 2 * t) ^ 2 + 4 * Y ^ 2)) ^ 2 - bridgeSigma Y ^ 2) / 6 := by
      funext t
      rw [bridgeRe2, heightOne_half_sub_holeInv hY, heightOne_holeInv hY]
    rw [e]
    have h := ((((hasDerivAt_bridgeSigma _).comp X hY0).fun_pow 2).sub_const
      (bridgeSigma Y ^ 2)).div_const 6 |>.const_sub (3 / 2)
    simp only [Function.comp_def] at h
    convert h using 1
    rw [hk]
    push_cast
    ring
  have hfr : ContDiffAt ℝ ∞ (fun t => holeInvRe t Y) X := by
    unfold holeInvRe
    fun_prop (disch := positivity)
  have hfi : ContDiffAt ℝ ∞ (fun t => holeInvIm t Y) X := by
    unfold holeInvIm
    fun_prop (disch := positivity)
  have hqd : DifferentiableAt ℝ (fun t => Real.sqrt (bridgeQ2 (holeInvRe t Y) (holeInvIm t Y))) X :=
    ((contDiffAt_bridgeQ2_comp hfr hfi (holeInvIm_pos hY)).sqrt
      (bridgeQ2_pos (holeInvIm_pos hY)).ne').differentiableAt (by simp)
  have hW : HasDerivAt (fun t => (1 + 2 * t) / (16 * (t ^ 2 + Y ^ 2)))
      ((2 * (16 * (X ^ 2 + Y ^ 2)) - (1 + 2 * X) * (32 * X)) / (16 * (X ^ 2 + Y ^ 2)) ^ 2) X := by
    have h1 : HasDerivAt (fun t : ℝ => 1 + 2 * t) 2 X := by
      simpa using ((hasDerivAt_id X).const_mul 2).const_add 1
    have h2 : HasDerivAt (fun t : ℝ => 16 * (t ^ 2 + Y ^ 2)) (32 * X) X := by
      convert ((hasDerivAt_pow 2 X).add_const (Y ^ 2)).const_mul 16 using 1
      push_cast
      ring
    convert h1.div h2 (by positivity) using 1
  have eI : (fun t => bridgeIm2 (holeInvRe t Y) (holeInvIm t Y)) = fun t =>
      (1 + 2 * t) / (16 * (t ^ 2 + Y ^ 2)) *
        Real.sqrt (bridgeQ2 (holeInvRe t Y) (holeInvIm t Y)) := by
    funext t
    rw [bridgeIm2, wallTwo_holeInv hY]
  have hI : HasDerivAt (fun t => bridgeIm2 (holeInvRe t Y) (holeInvIm t Y))
      ((2 * (16 * (X ^ 2 + Y ^ 2)) - (1 + 2 * X) * (32 * X)) / (16 * (X ^ 2 + Y ^ 2)) ^ 2 *
          Real.sqrt (bridgeQ2 (holeInvRe X Y) (holeInvIm X Y)) +
        (1 + 2 * X) / (16 * (X ^ 2 + Y ^ 2)) *
          deriv (fun t => Real.sqrt (bridgeQ2 (holeInvRe t Y) (holeInvIm t Y))) X) X := by
    rw [eI]
    exact hW.mul hqd.hasDerivAt
  have hRp : 0 < 3 / 2 - bridgeRe2 (holeInvRe X Y) (holeInvIm X Y) :=
    sub_pos.2 (bridgeRe2_lt _ _)
  have hqp : 0 < Real.sqrt (bridgeQ2 (holeInvRe X Y) (holeInvIm X Y)) :=
    Real.sqrt_pos.2 (bridgeQ2_pos (holeInvIm_pos hY))
  refine ⟨_, ?_, (hasDerivAt_arctan_div hR hI hRp.ne').const_sub Real.pi⟩
  rw [neg_lt_zero]
  rcases eq_or_ne (1 + 2 * X) 0 with hx | hx
  · have hI0 : bridgeIm2 (holeInvRe X Y) (holeInvIm X Y) = 0 := by
      rw [bridgeIm2, wallTwo_holeInv hY, hx, zero_div, zero_mul]
    rw [hI0, hx]
    have hX : X = -1 / 2 := by linarith
    subst hX
    apply div_pos _ (by positivity)
    simp only [zero_mul, sub_zero, zero_div, add_zero, mul_zero]
    apply mul_pos hRp
    apply mul_pos _ hqp
    apply div_pos _ (by positivity)
    nlinarith
  · have hK : ∀ s, (3 / 2 - bridgeRe2 (holeInvRe s Y) (holeInvIm s Y)) ^ 2 +
        bridgeIm2 (holeInvRe s Y) (holeInvIm s Y) ^ 2 = bridgeSigma Y ^ 2 := by
      intro s
      have h := bridgeRe2_sub_sq_add_bridgeIm2_sq (x := holeInvRe s Y) (holeInvIm_pos (X := s) hY)
      rw [heightOne_holeInv hY] at h
      linear_combination h
    have hI0 : bridgeIm2 (holeInvRe X Y) (holeInvIm X Y) ≠ 0 := by
      rw [bridgeIm2, wallTwo_holeInv hY]
      exact mul_ne_zero (div_ne_zero hx (by positivity)) hqp.ne'
    rw [arctan_div_deriv_eq hR hI hK hI0, bridgeIm2, wallTwo_holeInv hY, neg_neg]
    rw [show k * (1 + 2 * X) / ((1 + 2 * X) / (16 * (X ^ 2 + Y ^ 2)) *
        Real.sqrt (bridgeQ2 (holeInvRe X Y) (holeInvIm X Y))) =
        16 * (X ^ 2 + Y ^ 2) * k / Real.sqrt (bridgeQ2 (holeInvRe X Y) (holeInvIm X Y)) by
      field_simp]
    positivity

end GC.Seifert

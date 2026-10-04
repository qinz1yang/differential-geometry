import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsCornerMaps

/-!
# The corner map `cornerInf` of the K16f fold

Packet K16f, tier 3 (design `docs/geometrization/handoffs/20261004-design-k16f-fold.md`, §2, §5,
§6). The outer profile `foldRho` equals `bridgeRho` for `y ≤ 12/25`, is smooth, lies in `(2, 3)` for
`y > 0`, is strictly increasing there with positive derivative (the bend term
`foldTau' · (3 - 1/(50(1 + 4y²)) - bridgeRho y)` is nonnegative because the bracket is for
`y ≤ 247/500` and `foldTau` is constant beyond `49/100`), and takes every value of `(2, 3)`. The
weight `foldNu` is a smooth monotone step with `foldNu (1/2 - x) = 1 - foldNu x`. The angle
`angleInf` is smooth on the upper half-plane and strictly increasing in `x` (its derivative is a
convex combination of derivatives of `angleZero` plus `foldNu'` times `π - angleZero - angleZero`,
positive since `angleZero` is an arctangent), runs from `0` at `x = 0` to `π` at `x = 1/2`, and is
odd near the wall `x = 0`. Hence `cornerInf` is smooth with nonzero Jacobian `-(ρ ρ' ∂ₓA)`
(`polar_partials_det`), has modulus `foldRho y`, agrees with `bridgeZero` on the corner
`x ≤ 23/100, y ≤ 12/25`, is equivariant for the mirror `z ↦ 1/2 - z̄` and the reflection
`z ↦ -z̄`, and is injective on the strip `0 ≤ x ≤ 1/2` with values in the closed upper half-plane.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace GC.Seifert

private def foldG (y : ℝ) : ℝ := 3 - 1 / (50 * (1 + 4 * y ^ 2))

private theorem foldRho_eq_foldG (y : ℝ) :
    foldRho y = (1 - foldTau y) * bridgeRho y + foldTau y * foldG y := rfl

private theorem convex_pos {t a b : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    0 < (1 - t) * a + t * b := by
  rcases lt_or_eq_of_le h1 with h | h
  · have : 0 < (1 - t) * a := mul_pos (by linarith) ha
    nlinarith
  · subst h
    simpa using hb

theorem foldTau_eq_zero {y : ℝ} (hy : y ≤ 12 / 25) : foldTau y = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num))

private theorem foldTau_eq_one {y : ℝ} (hy : 49 / 100 ≤ y) : foldTau y = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith)

private theorem foldTau_nonneg (y : ℝ) : 0 ≤ foldTau y := Real.smoothTransition.nonneg _

private theorem foldTau_le_one (y : ℝ) : foldTau y ≤ 1 := Real.smoothTransition.le_one _

private theorem monotone_foldTau : Monotone foldTau := fun a b hab =>
  Real.smoothTransition.monotone (by gcongr)

private theorem contDiff_foldTau : ContDiff ℝ ∞ foldTau :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem foldRho_eq_bridgeRho {y : ℝ} (hy : y ≤ 12 / 25) : foldRho y = bridgeRho y := by
  rw [foldRho, foldTau_eq_zero hy]
  ring

private theorem foldRho_eq_of_le {y : ℝ} (hy : 49 / 100 ≤ y) : foldRho y = foldG y := by
  rw [foldRho_eq_foldG, foldTau_eq_one hy]
  ring

private theorem contDiff_bridgeRho : ContDiff ℝ ∞ bridgeRho := by
  unfold bridgeRho
  exact contDiff_const.sub (contDiff_const.div (by fun_prop) (fun x => by positivity))

private theorem contDiff_foldG : ContDiff ℝ ∞ foldG := by
  unfold foldG
  exact contDiff_const.sub (contDiff_const.div (by fun_prop) (fun x => by positivity))

theorem contDiff_foldRho : ContDiff ℝ ∞ foldRho := by
  have h1 := contDiff_foldTau
  have h2 := contDiff_bridgeRho
  have h3 := contDiff_foldG
  have h : foldRho = fun y => (1 - foldTau y) * bridgeRho y + foldTau y * foldG y := rfl
  rw [h]
  fun_prop

private theorem foldG_lt_three (y : ℝ) : foldG y < 3 := by
  unfold foldG
  have : 0 < 1 / (50 * (1 + 4 * y ^ 2)) := by positivity
  linarith

private theorem two_lt_foldG (y : ℝ) : 2 < foldG y := by
  unfold foldG
  have : 1 / (50 * (1 + 4 * y ^ 2)) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  linarith

theorem foldRho_lt_three {y : ℝ} (hy : 0 ≤ y) : foldRho y < 3 := by
  rcases lt_or_ge y (1 / 2) with h | h
  · have h1 : bridgeRho y < 3 := by
      unfold bridgeRho
      have : 1 < 2 / (1 + 4 * y ^ 2) := by
        rw [lt_div_iff₀ (by positivity)]
        nlinarith
      linarith
    have h2 := convex_pos (foldTau_nonneg y) (foldTau_le_one y) (sub_pos.2 h1)
      (sub_pos.2 (foldG_lt_three y))
    rw [foldRho_eq_foldG]
    linarith
  · rw [foldRho_eq_of_le (by linarith)]
    exact foldG_lt_three y

theorem two_lt_foldRho {y : ℝ} (hy : 0 < y) : 2 < foldRho y := by
  have h2 := convex_pos (foldTau_nonneg y) (foldTau_le_one y) (sub_pos.2 (two_lt_bridgeRho hy.ne'))
    (sub_pos.2 (two_lt_foldG y))
  rw [foldRho_eq_foldG]
  linarith

private theorem hasDerivAt_bridgeRho' (s : ℝ) :
    HasDerivAt bridgeRho (16 * s / (1 + 4 * s ^ 2) ^ 2) s := by
  have h1 : HasDerivAt (fun s : ℝ => 1 + 4 * s ^ 2) (8 * s) s := by
    convert ((hasDerivAt_pow 2 s).const_mul 4).const_add 1 using 1
    push_cast
    ring
  have hne : (1 + 4 * s ^ 2) ≠ 0 := by positivity
  have h2 := ((hasDerivAt_const s (2 : ℝ)).div h1 hne).const_sub 4
  change HasDerivAt (fun t => 4 - 2 / (1 + 4 * t ^ 2)) _ s
  convert h2 using 1
  field_simp
  ring

private theorem hasDerivAt_foldG (s : ℝ) :
    HasDerivAt foldG (8 * s / (50 * (1 + 4 * s ^ 2) ^ 2)) s := by
  have h1 : HasDerivAt (fun s : ℝ => 50 * (1 + 4 * s ^ 2)) (400 * s) s := by
    convert (((hasDerivAt_pow 2 s).const_mul 4).const_add 1).const_mul 50 using 1
    push_cast
    ring
  have hne : 50 * (1 + 4 * s ^ 2) ≠ 0 := by positivity
  have h2 := ((hasDerivAt_const s (1 : ℝ)).div h1 hne).const_sub 3
  change HasDerivAt (fun t => 3 - 1 / (50 * (1 + 4 * t ^ 2))) _ s
  convert h2 using 1
  field_simp
  ring

theorem exists_hasDerivAt_foldRho {y : ℝ} (hy : 0 < y) :
    ∃ D : ℝ, 0 < D ∧ HasDerivAt foldRho D y := by
  rcases le_or_gt y (247 / 500) with h | h
  · have hτ : HasDerivAt foldTau (deriv foldTau y) y :=
      (contDiff_foldTau.differentiable (by simp) y).hasDerivAt
    have hτ0 : 0 ≤ deriv foldTau y := monotone_foldTau.deriv_nonneg
    have hd := (((hasDerivAt_const y (1 : ℝ)).sub hτ).mul (hasDerivAt_bridgeRho' y)).add
      (hτ.mul (hasDerivAt_foldG y))
    refine ⟨_, ?_, hd⟩
    have hgr : 0 ≤ foldG y - bridgeRho y := by
      have he : foldG y - bridgeRho y = (49 / 50 - 4 * y ^ 2) / (1 + 4 * y ^ 2) := by
        unfold foldG bridgeRho
        field_simp
        ring
      rw [he]
      apply div_nonneg _ (by positivity)
      nlinarith
    have hc := convex_pos (foldTau_nonneg y) (foldTau_le_one y)
      (show 0 < 16 * y / (1 + 4 * y ^ 2) ^ 2 by positivity)
      (show 0 < 8 * y / (50 * (1 + 4 * y ^ 2) ^ 2) by positivity)
    have hm : 0 ≤ deriv foldTau y * (foldG y - bridgeRho y) := mul_nonneg hτ0 hgr
    simp only [Pi.sub_apply]
    nlinarith
  · refine ⟨_, by positivity, (hasDerivAt_foldG y).congr_of_eventuallyEq ?_⟩
    filter_upwards [Ioi_mem_nhds (show (49 / 100 : ℝ) < y by linarith)] with t ht
    exact foldRho_eq_of_le (le_of_lt ht)

theorem strictMonoOn_foldRho : StrictMonoOn foldRho (Set.Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) contDiff_foldRho.continuous.continuousOn ?_
  intro x hx
  rw [interior_Ioi] at hx
  obtain ⟨D, hD, h⟩ := exists_hasDerivAt_foldRho hx
  rw [h.deriv]
  exact hD

theorem exists_lt_foldRho {m : ℝ} (hm : m < 3) : ∃ H : ℝ, 0 < H ∧ ∀ y, H ≤ y → m < foldRho y := by
  refine ⟨max 1 (1 / (3 - m)), lt_max_of_lt_left one_pos, fun y hy => ?_⟩
  have hy1 : 1 ≤ y := le_trans (le_max_left _ _) hy
  have hy2 : 1 / (3 - m) ≤ y := le_trans (le_max_right _ _) hy
  have h3 : 0 < 3 - m := by linarith
  rw [foldRho_eq_of_le (by linarith)]
  unfold foldG
  have h4 : y < 50 * (1 + 4 * y ^ 2) := by nlinarith
  have h5 : 1 ≤ (3 - m) * y := by
    rw [div_le_iff₀ h3] at hy2
    linarith
  have : 1 / (50 * (1 + 4 * y ^ 2)) < 3 - m := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left h4 h3]
  linarith

theorem exists_foldRho_eq {s : ℝ} (h1 : 2 < s) (h2 : s < 3) : ∃ y : ℝ, 0 < y ∧ foldRho y = s := by
  have hc := contDiff_foldRho.continuous
  have h0 : foldRho 0 = 2 := by
    rw [foldRho_eq_bridgeRho (by norm_num)]
    norm_num [bridgeRho]
  have hev : ∀ᶠ y in nhds (0 : ℝ), foldRho y < s :=
    (hc.tendsto 0).eventually_lt_const (by rw [h0]; exact h1)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨H, -, hHy⟩ := exists_lt_foldRho h2
  have ha : 0 < ε / 2 := by positivity
  have hfa : foldRho (ε / 2) < s :=
    hball (by rw [Real.dist_eq, sub_zero, abs_of_pos ha]; linarith)
  have hfb : s < foldRho (max H (ε / 2)) := hHy _ (le_max_left _ _)
  obtain ⟨y, hy, hys⟩ := intermediate_value_Icc (le_max_right H (ε / 2)) hc.continuousOn
    ⟨hfa.le, hfb.le⟩
  exact ⟨y, lt_of_lt_of_le ha hy.1, hys⟩

theorem foldNu_eq_zero {x : ℝ} (hx : x ≤ 23 / 100) : foldNu x = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num))

theorem foldNu_eq_one {x : ℝ} (hx : 27 / 100 ≤ x) : foldNu x = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith)

private theorem smoothTransition_one_sub (t : ℝ) :
    Real.smoothTransition (1 - t) = 1 - Real.smoothTransition t := by
  have h1 := Real.smoothTransition.pos_denom t
  have h2 := Real.smoothTransition.pos_denom (1 - t)
  simp only [Real.smoothTransition, sub_sub_cancel] at h2 ⊢
  rw [eq_sub_iff_add_eq, add_comm (expNegInvGlue (1 - t)), ← add_div,
    add_comm (expNegInvGlue (1 - t)), div_self h1.ne']

theorem foldNu_mirror (x : ℝ) : foldNu (1 / 2 - x) = 1 - foldNu x := by
  have h : (1 / 2 - x - 23 / 100) / (1 / 25) = 1 - (x - 23 / 100) / (1 / 25) := by ring
  rw [foldNu, foldNu, h, smoothTransition_one_sub]

theorem contDiff_foldNu : ContDiff ℝ ∞ foldNu :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

private theorem foldNu_nonneg (x : ℝ) : 0 ≤ foldNu x := Real.smoothTransition.nonneg _

private theorem foldNu_le_one (x : ℝ) : foldNu x ≤ 1 := Real.smoothTransition.le_one _

private theorem monotone_foldNu : Monotone foldNu := fun a b hab =>
  Real.smoothTransition.monotone (by gcongr)

theorem exists_hasDerivAt_foldNu (x : ℝ) : ∃ D : ℝ, 0 ≤ D ∧ HasDerivAt foldNu D x :=
  ⟨deriv foldNu x, monotone_foldNu.deriv_nonneg,
    (contDiff_foldNu.differentiable (by simp) x).hasDerivAt⟩

private theorem contDiff_foldMirror : ContDiff ℝ ∞ foldMirror := by
  have h : foldMirror = fun w => 1 / 2 - Complex.conjCLE w := by
    funext w
    simp [foldMirror]
  rw [h]
  exact contDiff_const.sub Complex.conjCLE.contDiff

theorem contDiffAt_angleInf {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (fun w : ℂ => angleInf w.re w.im) z := by
  have h1 : ContDiffAt ℝ ∞ (fun w : ℂ => foldNu w.re) z :=
    contDiff_foldNu.contDiffAt.comp z Complex.reCLM.contDiff.contDiffAt
  have h2 := contDiffAt_angleZero hz
  have h3 : ContDiffAt ℝ ∞ (fun w : ℂ => angleZero (1 / 2 - w.re) w.im) z := by
    have hz' : 0 < (foldMirror z).im := by rwa [foldMirror_im]
    have h := (contDiffAt_angleZero hz').comp z contDiff_foldMirror.contDiffAt
    convert h using 1
    funext w
    simp [foldMirror_re, foldMirror_im]
  exact ((contDiffAt_const.sub h1).mul h2).add (h1.mul (contDiffAt_const.sub h3))

private theorem angleZero_zero (y : ℝ) : angleZero 0 y = 0 := by
  simp [angleZero, bridgeIm0]

theorem exists_hasDerivAt_angleInf {x y : ℝ} (hy : 0 < y) :
    ∃ D : ℝ, 0 < D ∧ HasDerivAt (fun t => angleInf t y) D x := by
  obtain ⟨N, hN, hNd⟩ := exists_hasDerivAt_foldNu x
  obtain ⟨a, ha, had⟩ := exists_hasDerivAt_angleZero (x := x) hy
  obtain ⟨b, hb, hbd⟩ := exists_hasDerivAt_angleZero (x := 1 / 2 - x) hy
  have hbd' : HasDerivAt (fun t => angleZero (1 / 2 - t) y) (b * -1) x :=
    hbd.comp x ((hasDerivAt_id' x).const_sub (1 / 2))
  have h := (((hasDerivAt_const x (1 : ℝ)).sub hNd).mul had).add
    (hNd.mul ((hasDerivAt_const x Real.pi).sub hbd'))
  refine ⟨_, ?_, h⟩
  have hc := convex_pos (foldNu_nonneg x) (foldNu_le_one x) ha hb
  have h1 := Real.arctan_lt_pi_div_two (bridgeIm0 x y / bridgeRe0 x y)
  have h2 := Real.arctan_lt_pi_div_two (bridgeIm0 (1 / 2 - x) y / bridgeRe0 (1 / 2 - x) y)
  have hbr : 0 ≤ N * (Real.pi - angleZero (1 / 2 - x) y - angleZero x y) :=
    mul_nonneg hN (by unfold angleZero; linarith)
  simp only [Pi.sub_apply]
  nlinarith

theorem strictMono_angleInf {y : ℝ} (hy : 0 < y) : StrictMono (fun t => angleInf t y) := by
  refine strictMono_of_deriv_pos fun x => ?_
  obtain ⟨D, hD, h⟩ := exists_hasDerivAt_angleInf (x := x) hy
  rw [h.deriv]
  exact hD

theorem angleInf_zero (y : ℝ) : angleInf 0 y = 0 := by
  rw [angleInf, foldNu_eq_zero (by norm_num), angleZero_zero]
  ring

theorem angleInf_half (y : ℝ) : angleInf (1 / 2) y = Real.pi := by
  have h : (1 : ℝ) / 2 - 1 / 2 = 0 := by norm_num
  rw [angleInf, foldNu_eq_one (by norm_num), h, angleZero_zero]
  ring

theorem angleInf_mirror (x y : ℝ) : angleInf (1 / 2 - x) y = Real.pi - angleInf x y := by
  rw [angleInf, angleInf, foldNu_mirror, sub_sub_cancel (1 / 2 : ℝ) x]
  ring

theorem angleInf_neg {x y : ℝ} (hx : |x| ≤ 23 / 100) : angleInf (-x) y = -angleInf x y := by
  have h1 : x ≤ 23 / 100 := le_trans (le_abs_self x) hx
  have h2 : -x ≤ 23 / 100 := le_trans (neg_le_abs x) hx
  rw [angleInf, angleInf, foldNu_eq_zero h1, foldNu_eq_zero h2, angleZero_neg]
  ring

theorem contDiffAt_cornerInf {z : ℂ} (hz : 0 < z.im) : ContDiffAt ℝ ∞ cornerInf z := by
  have h1 : ContDiffAt ℝ ∞ (fun w : ℂ => (foldRho w.im : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z
      (contDiff_foldRho.contDiffAt.comp z Complex.imCLM.contDiff.contDiffAt)
  have h2 : ContDiffAt ℝ ∞ (fun w : ℂ => (angleInf w.re w.im : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_angleInf hz)
  have h3 : ContDiffAt ℝ ∞ (fun w : ℂ => Complex.exp (Complex.I * (angleInf w.re w.im : ℂ))) z :=
    (Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp z (contDiffAt_const.mul h2)
  exact h1.mul h3

private theorem exp_I_mul (A : ℝ) :
    Complex.exp (Complex.I * A) = ⟨Real.cos A, Real.sin A⟩ := by
  rw [mul_comm, Complex.exp_mul_I]
  apply Complex.ext <;> simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]

private theorem cornerInf_eq_mk (z : ℂ) : cornerInf z =
    ⟨foldRho z.im * Real.cos (angleInf z.re z.im),
      foldRho z.im * Real.sin (angleInf z.re z.im)⟩ := by
  rw [cornerInf, exp_I_mul]
  apply Complex.ext <;> simp

private theorem foldRho_pos {y : ℝ} (hy : 0 < y) : 0 < foldRho y := by
  linarith [two_lt_foldRho hy]

theorem det_fderiv_cornerInf_ne_zero {z : ℂ} (hz : 0 < z.im) : (fderiv ℝ cornerInf z).det ≠ 0 := by
  obtain ⟨R, hR, hRd⟩ := exists_hasDerivAt_foldRho hz
  obtain ⟨a, ha, had⟩ := exists_hasDerivAt_angleInf (x := z.re) hz
  have hAx : HasDerivAt (fun t : ℝ => angleInf (z.re + t) z.im) a 0 :=
    HasDerivAt.comp_const_add z.re 0 (by rwa [add_zero])
  have hRy : HasDerivAt (fun t : ℝ => foldRho (z.im + t)) R 0 :=
    HasDerivAt.comp_const_add z.im 0 (by rwa [add_zero])
  have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ) * Complex.I) Complex.I 0 := by
    simpa using (((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I).const_add z)
  have hg : HasFDerivAt (fun w : ℂ => angleInf w.re w.im)
      (fderiv ℝ (fun w : ℂ => angleInf w.re w.im) z) (z + ((0 : ℝ) : ℂ) * Complex.I) := by
    simpa using ((contDiffAt_angleInf hz).differentiableAt (by simp)).hasFDerivAt
  have hAy : HasDerivAt (fun t : ℝ => angleInf z.re (z.im + t))
      (fderiv ℝ (fun w : ℂ => angleInf w.re w.im) z Complex.I) 0 := by
    have h := hg.comp_hasDerivAt (0 : ℝ) hl
    convert h using 1
    funext t
    simp
  have hx : HasDerivAt (fun t : ℝ => cornerInf (z + t))
      ((foldRho z.im : ℂ) * a * Complex.I *
        Complex.exp (Complex.I * (angleInf z.re z.im : ℂ))) 0 := by
    have hf : (fun t : ℝ => cornerInf (z + t)) = fun t : ℝ =>
        (foldRho z.im : ℂ) * Complex.exp (Complex.I * (angleInf (z.re + t) z.im : ℂ)) := by
      funext t
      simp [cornerInf]
    rw [hf]
    have h := ((hAx.ofReal_comp.const_mul Complex.I).cexp).const_mul (foldRho z.im : ℂ)
    convert h using 1
    simp only [add_zero]
    ring
  have hy : HasDerivAt (fun t : ℝ => cornerInf (z + t * Complex.I))
      (((R : ℂ) + Complex.I * (foldRho z.im : ℂ) *
        (fderiv ℝ (fun w : ℂ => angleInf w.re w.im) z Complex.I : ℂ)) *
        Complex.exp (Complex.I * (angleInf z.re z.im : ℂ))) 0 := by
    have hf : (fun t : ℝ => cornerInf (z + t * Complex.I)) = fun t : ℝ =>
        (foldRho (z.im + t) : ℂ) * Complex.exp (Complex.I * (angleInf z.re (z.im + t) : ℂ)) := by
      funext t
      simp [cornerInf]
    rw [hf]
    have h := hRy.ofReal_comp.mul ((hAy.ofReal_comp.const_mul Complex.I).cexp)
    convert h using 1
    simp only [add_zero]
    ring
  have hdiff : DifferentiableAt ℝ cornerInf z :=
    (contDiffAt_cornerInf hz).differentiableAt (by simp)
  rw [det_fderiv_eq_of_partials hdiff hx hy, polar_partials_det]
  have : 0 < foldRho z.im * R * a := by
    have := foldRho_pos hz
    positivity
  exact neg_ne_zero.2 this.ne'

theorem norm_cornerInf {z : ℂ} (hz : 0 < z.im) : ‖cornerInf z‖ = foldRho z.im := by
  rw [cornerInf, norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (foldRho_pos hz)]

theorem cornerInf_eq_bridgeZero {z : ℂ} (hz : 0 < z.im) (hx : z.re ≤ 23 / 100)
    (hy : z.im ≤ 12 / 25) : cornerInf z = bridgeZero z := by
  have hA : angleInf z.re z.im = angleZero z.re z.im := by
    rw [angleInf, foldNu_eq_zero hx]
    ring
  rw [cornerInf, bridgeZero_eq_polar hz, foldRho_eq_bridgeRho hy, hA]

private theorem cornerInf_foldMirror_eq_mk (z : ℂ) : cornerInf (foldMirror z) =
    ⟨-(foldRho z.im * Real.cos (angleInf z.re z.im)),
      foldRho z.im * Real.sin (angleInf z.re z.im)⟩ := by
  rw [cornerInf_eq_mk, foldMirror_re, foldMirror_im, angleInf_mirror, Real.cos_pi_sub,
    Real.sin_pi_sub, mul_neg]

theorem cornerInf_foldMirror (z : ℂ) : cornerInf (foldMirror z) = -(starRingEnd ℂ) (cornerInf z) :=
  (cornerInf_foldMirror_eq_mk z).trans (by rw [cornerInf_eq_mk]; apply Complex.ext <;> simp)

theorem cornerInf_neg_conj {z : ℂ} (hx : |z.re| ≤ 23 / 100) :
    cornerInf (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (cornerInf z) := by
  have hre : (-(starRingEnd ℂ) z).re = -z.re := by simp
  have him : (-(starRingEnd ℂ) z).im = z.im := by simp
  rw [cornerInf_eq_mk, cornerInf_eq_mk, hre, him, angleInf_neg hx]
  apply Complex.ext <;> simp [Real.cos_neg, Real.sin_neg]

private theorem angleInf_mem_Icc {x y : ℝ} (hy : 0 < y) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    angleInf x y ∈ Set.Icc 0 Real.pi := by
  have hm := (strictMono_angleInf hy).monotone
  have ha := hm h0
  have hb := hm h1
  simp only [angleInf_zero, angleInf_half] at ha hb
  exact ⟨ha, hb⟩

private theorem angleInf_mem_Ioo {x y : ℝ} (hy : 0 < y) (h0 : 0 < x) (h1 : x < 1 / 2) :
    angleInf x y ∈ Set.Ioo 0 Real.pi := by
  have hm := strictMono_angleInf hy
  have ha := hm h0
  have hb := hm h1
  simp only [angleInf_zero, angleInf_half] at ha hb
  exact ⟨ha, hb⟩

theorem cornerInf_injOn : Set.InjOn cornerInf {z : ℂ | 0 < z.im ∧ 0 ≤ z.re ∧ z.re ≤ 1 / 2} := by
  rintro z ⟨hz, hz0, hz1⟩ w ⟨hw, hw0, hw1⟩ h
  have hy : z.im = w.im := by
    have hn := congrArg norm h
    rw [norm_cornerInf hz, norm_cornerInf hw] at hn
    exact strictMonoOn_foldRho.injOn hz hw hn
  have hρ := foldRho_pos hz
  rw [cornerInf_eq_mk, cornerInf_eq_mk, ← hy] at h
  have hc : Real.cos (angleInf z.re z.im) = Real.cos (angleInf w.re z.im) :=
    mul_left_cancel₀ hρ.ne' (congrArg Complex.re h)
  have hA := Real.injOn_cos (angleInf_mem_Icc hz hz0 hz1) (angleInf_mem_Icc hz hw0 hw1) hc
  exact Complex.ext ((strictMono_angleInf hz).injective hA) hy

theorem cornerInf_im_nonneg {z : ℂ} (hz : 0 < z.im) (h0 : 0 ≤ z.re) (h1 : z.re ≤ 1 / 2) :
    0 ≤ (cornerInf z).im := by
  have hA := angleInf_mem_Icc hz h0 h1
  rw [cornerInf_eq_mk]
  exact mul_nonneg (foldRho_pos hz).le (Real.sin_nonneg_of_nonneg_of_le_pi hA.1 hA.2)

theorem cornerInf_im_pos {z : ℂ} (hz : 0 < z.im) (h0 : 0 < z.re) (h1 : z.re < 1 / 2) :
    0 < (cornerInf z).im := by
  have hA := angleInf_mem_Ioo hz h0 h1
  rw [cornerInf_eq_mk]
  exact mul_pos (foldRho_pos hz) (Real.sin_pos_of_pos_of_lt_pi hA.1 hA.2)

theorem cornerInf_wall_zero {y : ℝ} (hy : 0 < y) : cornerInf ⟨0, y⟩ = (foldRho y : ℂ) := by
  have := foldRho_pos hy
  rw [cornerInf_eq_mk]
  apply Complex.ext <;> simp [angleInf_zero]

end GC.Seifert

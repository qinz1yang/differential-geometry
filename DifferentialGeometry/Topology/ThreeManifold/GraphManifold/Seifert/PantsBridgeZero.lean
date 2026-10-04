import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsBridges

/-!
# Smoothness, symmetry and monotonicity of the bridge at the cusp `0`

Packet K16f, tier 3. On the upper half-plane the bridge `bridgeZero` and its angles `angleZero`,
`angleZeroHole` are smooth (`angleZeroHole` where `bridgeRe0 > 3/2`), `bridgeZero` commutes with
the reflection `z ↦ -conj z`, and both angles are odd in `x`. `bridgeZero` is written in polar
form about `0` (modulus `bridgeRho y`) and about `3/2` (modulus `bridgeSigma (heightOne x y)`).
Along a horizontal line `angleZero` is strictly increasing; along a horocycle of the cusp `0`,
parametrised by `holeInvRe`, `holeInvIm`, `angleZeroHole` is strictly decreasing. Both
derivatives come from `hasDerivAt_arctan_div` and `arctan_div_deriv_eq`, the modulus being
constant along the curve.
-/

set_option autoImplicit false

open scoped ContDiff

namespace GC.Seifert

private theorem eq_polar_of_re_pos {a b r : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hn : a ^ 2 + b ^ 2 = r ^ 2) :
    (⟨a, b⟩ : ℂ) = (r : ℂ) * Complex.exp (Complex.I * (Real.arctan (b / a) : ℂ)) := by
  have hs : Real.sqrt (1 + (b / a) ^ 2) = r / a := by
    rw [show 1 + (b / a) ^ 2 = (r / a) ^ 2 by field_simp; linarith]
    exact Real.sqrt_sq (by positivity)
  apply Complex.ext
  · simp [Complex.exp_re, Real.cos_arctan, hs]
    field_simp
  · simp [Complex.exp_im, Real.sin_arctan, hs]
    field_simp

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

private theorem hasDerivAt_bridgeRho (s : ℝ) :
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

private theorem hasDerivAt_heightOne {x y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => heightOne t y) (-(x * y) / (2 * (x ^ 2 + y ^ 2) ^ 2)) x := by
  have h1 : HasDerivAt (fun t : ℝ => 4 * (t ^ 2 + y ^ 2)) (8 * x) x := by
    convert ((hasDerivAt_pow 2 x).add_const (y ^ 2)).const_mul 4 using 1
    push_cast
    ring
  have hne : 4 * (x ^ 2 + y ^ 2) ≠ 0 := by positivity
  have h2 := (hasDerivAt_const x y).div h1 hne
  change HasDerivAt (fun t => y / (4 * (t ^ 2 + y ^ 2))) _ x
  convert h2 using 1
  field_simp
  ring

private theorem hasDerivAt_holeInvRe {X Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun t => holeInvRe t Y) ((X ^ 2 - Y ^ 2) / (4 * (X ^ 2 + Y ^ 2) ^ 2)) X := by
  have h1 : HasDerivAt (fun t : ℝ => 4 * (t ^ 2 + Y ^ 2)) (8 * X) X := by
    convert ((hasDerivAt_pow 2 X).add_const (Y ^ 2)).const_mul 4 using 1
    push_cast
    ring
  have hne : 4 * (X ^ 2 + Y ^ 2) ≠ 0 := by positivity
  have h2 := (hasDerivAt_neg' X).div h1 hne
  change HasDerivAt (fun t => -t / (4 * (t ^ 2 + Y ^ 2))) _ X
  convert h2 using 1
  field_simp
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem contDiffAt_bridgeSigma_comp {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (fun w => bridgeSigma (f w)) z := by
  unfold bridgeSigma
  fun_prop (disch := positivity)

private theorem contDiffAt_bridgeRho_comp {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (fun w => bridgeRho (f w)) z := by
  unfold bridgeRho
  fun_prop (disch := positivity)

private theorem contDiffAt_heightOne_comp {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ ∞ f z)
    (hg : ContDiffAt ℝ ∞ g z) (hz : 0 < g z) :
    ContDiffAt ℝ ∞ (fun w => heightOne (f w) (g w)) z := by
  unfold heightOne
  fun_prop (disch := positivity)

private theorem contDiffAt_bridgeQ0_comp {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ ∞ f z)
    (hg : ContDiffAt ℝ ∞ g z) (hz : 0 < g z) :
    ContDiffAt ℝ ∞ (fun w => bridgeQ0 (f w) (g w)) z := by
  have h1 : ContDiffAt ℝ ∞ (fun w => bridgeP0 (f w) (g w)) z := by
    unfold bridgeP0
    fun_prop (disch := positivity)
  have h2 := contDiffAt_bridgeRho_comp hg
  have h3 := contDiffAt_bridgeSigma_comp (contDiffAt_heightOne_comp hf hg hz)
  unfold bridgeQ0
  fun_prop

private theorem contDiffAt_sqrtQ0_comp {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ ∞ f z)
    (hg : ContDiffAt ℝ ∞ g z) (hz : 0 < g z) :
    ContDiffAt ℝ ∞ (fun w => Real.sqrt (bridgeQ0 (f w) (g w))) z :=
  (contDiffAt_bridgeQ0_comp hf hg hz).sqrt (bridgeQ0_pos hz).ne'

private theorem contDiffAt_bridgeRe0_comp {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ ∞ f z)
    (hg : ContDiffAt ℝ ∞ g z) (hz : 0 < g z) :
    ContDiffAt ℝ ∞ (fun w => bridgeRe0 (f w) (g w)) z := by
  have h2 := contDiffAt_bridgeRho_comp hg
  have h3 := contDiffAt_bridgeSigma_comp (contDiffAt_heightOne_comp hf hg hz)
  unfold bridgeRe0
  fun_prop

private theorem contDiffAt_bridgeIm0_comp {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ ∞ f z)
    (hg : ContDiffAt ℝ ∞ g z) (hz : 0 < g z) :
    ContDiffAt ℝ ∞ (fun w => bridgeIm0 (f w) (g w)) z :=
  hf.mul (contDiffAt_sqrtQ0_comp hf hg hz)

private theorem contDiffAt_re (z : ℂ) : ContDiffAt ℝ ∞ (fun w : ℂ => w.re) z :=
  Complex.reCLM.contDiff.contDiffAt

private theorem contDiffAt_im (z : ℂ) : ContDiffAt ℝ ∞ (fun w : ℂ => w.im) z :=
  Complex.imCLM.contDiff.contDiffAt

theorem contDiffAt_bridgeRe0 {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (fun w : ℂ => bridgeRe0 w.re w.im) z :=
  contDiffAt_bridgeRe0_comp (contDiffAt_re z) (contDiffAt_im z) hz

theorem contDiffAt_bridgeIm0 {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (fun w : ℂ => bridgeIm0 w.re w.im) z :=
  contDiffAt_bridgeIm0_comp (contDiffAt_re z) (contDiffAt_im z) hz

theorem contDiffAt_bridgeZero {z : ℂ} (hz : 0 < z.im) : ContDiffAt ℝ ∞ bridgeZero z :=
  Complex.equivRealProdCLM.symm.contDiff.contDiffAt.comp z
    ((contDiffAt_bridgeRe0 hz).prodMk (contDiffAt_bridgeIm0 hz))

private theorem heightOne_neg (x y : ℝ) : heightOne (-x) y = heightOne x y := by
  simp only [heightOne, neg_sq]

private theorem bridgeRe0_neg (x y : ℝ) : bridgeRe0 (-x) y = bridgeRe0 x y := by
  simp only [bridgeRe0, heightOne_neg]

private theorem bridgeQ0_neg (x y : ℝ) : bridgeQ0 (-x) y = bridgeQ0 x y := by
  simp only [bridgeQ0, bridgeP0, heightOne_neg, neg_sq]

private theorem bridgeIm0_neg (x y : ℝ) : bridgeIm0 (-x) y = -bridgeIm0 x y := by
  rw [bridgeIm0, bridgeIm0, bridgeQ0_neg, neg_mul]

theorem bridgeZero_neg_conj (z : ℂ) :
    bridgeZero (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (bridgeZero z) := by
  apply Complex.ext
  · simp only [bridgeZero_re, Complex.conj_re, Complex.neg_re, Complex.neg_im, Complex.conj_im,
      neg_neg]
    exact bridgeRe0_neg z.re z.im
  · simp only [bridgeZero_im, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.conj_re,
      neg_neg]
    exact bridgeIm0_neg z.re z.im

theorem angleZero_neg (x y : ℝ) : angleZero (-x) y = -angleZero x y := by
  rw [angleZero, angleZero, bridgeRe0_neg, bridgeIm0_neg, neg_div, Real.arctan_neg]

theorem angleZeroHole_neg (x y : ℝ) : angleZeroHole (-x) y = -angleZeroHole x y := by
  rw [angleZeroHole, angleZeroHole, bridgeRe0_neg, bridgeIm0_neg, neg_div, Real.arctan_neg]

theorem contDiffAt_angleZero {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (fun w : ℂ => angleZero w.re w.im) z :=
  Real.contDiff_arctan.contDiffAt.comp z
    ((contDiffAt_bridgeIm0 hz).div (contDiffAt_bridgeRe0 hz) (bridgeRe0_pos hz).ne')

theorem exists_hasDerivAt_angleZero {x y : ℝ} (hy : 0 < y) :
    ∃ D : ℝ, 0 < D ∧ HasDerivAt (fun t => angleZero t y) D x := by
  have hY1pos : 0 < heightOne x y := heightOne_pos hy
  have hσpos : 0 < bridgeSigma (heightOne x y) := by
    linarith [half_lt_bridgeSigma (heightOne x y)]
  have hS := (hasDerivAt_bridgeSigma (heightOne x y)).comp x (hasDerivAt_heightOne (x := x) hy)
  have hR : HasDerivAt (fun t => bridgeRe0 t y)
      (-(x * ((2 / 3) * bridgeSigma (heightOne x y) *
        (16 * heightOne x y / (1 + 4 * heightOne x y ^ 2) ^ 2) *
        (y / (2 * (x ^ 2 + y ^ 2) ^ 2))))) x := by
    have h := (((hasDerivAt_const x (bridgeRho y ^ 2)).sub (hS.pow 2)).add_const
      (9 / 4)).div_const 3
    convert h using 1
    · funext t
      simp only [bridgeRe0, Pi.sub_apply, Pi.pow_apply, Function.comp_apply]
    · simp only [Function.comp_apply]
      norm_num
      ring
  have hgd : DifferentiableAt ℝ (fun t => Real.sqrt (bridgeQ0 t y)) x :=
    (contDiffAt_sqrtQ0_comp (f := fun t => t) (g := Function.const ℝ y) contDiffAt_id
      contDiffAt_const hy).differentiableAt (by simp)
  have hI : HasDerivAt (fun t => bridgeIm0 t y)
      (1 * Real.sqrt (bridgeQ0 x y) + x * deriv (fun t => Real.sqrt (bridgeQ0 t y)) x) x :=
    (hasDerivAt_id' x).mul hgd.hasDerivAt
  have hR0 : bridgeRe0 x y ≠ 0 := (bridgeRe0_pos hy).ne'
  refine ⟨_, ?_, hasDerivAt_arctan_div hR hI hR0⟩
  have hsq : 0 < Real.sqrt (bridgeQ0 x y) := Real.sqrt_pos.2 (bridgeQ0_pos hy)
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    have hI0 : bridgeIm0 0 y = 0 := by simp [bridgeIm0]
    have hRpos := bridgeRe0_pos (x := 0) hy
    simp only [hI0, zero_mul, add_zero, one_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    positivity
  · have hK : ∀ s, (fun t => bridgeRe0 t y) s ^ 2 + (fun t => bridgeIm0 t y) s ^ 2 =
        bridgeRho y ^ 2 := fun s => bridgeRe0_sq_add_bridgeIm0_sq hy
    have hI0 : (fun t => bridgeIm0 t y) x ≠ 0 := mul_ne_zero hx hsq.ne'
    rw [arctan_div_deriv_eq hR hI hK hI0]
    simp only [bridgeIm0, neg_neg]
    rw [mul_div_mul_left _ _ hx]
    positivity

theorem bridgeZero_eq_polar {z : ℂ} (hz : 0 < z.im) :
    bridgeZero z = (bridgeRho z.im : ℂ) * Complex.exp (Complex.I * (angleZero z.re z.im : ℂ)) :=
  eq_polar_of_re_pos (by linarith [two_le_bridgeRho z.im]) (bridgeRe0_pos hz)
    (bridgeRe0_sq_add_bridgeIm0_sq hz)

theorem contDiffAt_angleZeroHole {z : ℂ} (hz : 0 < z.im) (h : 3 / 2 < bridgeRe0 z.re z.im) :
    ContDiffAt ℝ ∞ (fun w : ℂ => angleZeroHole w.re w.im) z :=
  Real.contDiff_arctan.contDiffAt.comp z
    ((contDiffAt_bridgeIm0 hz).div ((contDiffAt_bridgeRe0 hz).sub contDiffAt_const)
      (sub_pos.2 h).ne')

private theorem div_neg_aux {X P s c : ℝ} (hX : X ≠ 0) (hP : 0 < P) (hs : 0 < s) (hc : 0 < c) :
    X * P / (-X / c * s) < 0 := by
  have hs' := hs.ne'
  have hc' := hc.ne'
  rw [show X * P / (-X / c * s) = -(c * P / s) by field_simp]
  exact neg_neg_of_pos (by positivity)

theorem exists_hasDerivAt_angleZeroHole {X Y : ℝ} (hY : 0 < Y)
    (h : 3 / 2 < bridgeRe0 (holeInvRe X Y) (holeInvIm X Y)) :
    ∃ D : ℝ, D < 0 ∧ HasDerivAt (fun t => angleZeroHole (holeInvRe t Y) (holeInvIm t Y)) D X := by
  have ha : 0 < holeInvIm X Y := holeInvIm_pos hY
  have hρ : 0 < bridgeRho (holeInvIm X Y) := by linarith [two_le_bridgeRho (holeInvIm X Y)]
  have hR : ∃ P : ℝ, 0 < P ∧ HasDerivAt
      (fun t => bridgeRe0 (holeInvRe t Y) (holeInvIm t Y) - 3 / 2) (-(X * P)) X := by
    have hfun : (fun t => bridgeRe0 (holeInvRe t Y) (holeInvIm t Y) - 3 / 2) =
        fun t => (bridgeRho (holeInvIm t Y) ^ 2 - bridgeSigma Y ^ 2 + 9 / 4) / 3 - 3 / 2 := by
      funext t
      rw [bridgeRe0, heightOne_holeInv hY]
    have hA : HasDerivAt (fun t => holeInvIm t Y) (-(X * Y) / (2 * (X ^ 2 + Y ^ 2) ^ 2)) X :=
      hasDerivAt_heightOne hY
    have hS := (hasDerivAt_bridgeRho (holeInvIm X Y)).comp X hA
    refine ⟨(2 / 3) * bridgeRho (holeInvIm X Y) *
        (16 * holeInvIm X Y / (1 + 4 * holeInvIm X Y ^ 2) ^ 2) *
        (Y / (2 * (X ^ 2 + Y ^ 2) ^ 2)), by positivity, ?_⟩
    rw [hfun]
    have h2 := ((((hS.pow 2).sub (hasDerivAt_const X (bridgeSigma Y ^ 2))).add_const
      (9 / 4)).div_const 3).sub_const (3 / 2)
    convert h2 using 1
    · funext t
      simp only [Pi.sub_apply, Pi.pow_apply, Function.comp_apply]
    · simp only [Function.comp_apply]
      norm_num
      ring
  obtain ⟨P, hP, hR⟩ := hR
  have hsq : 0 < Real.sqrt (bridgeQ0 (holeInvRe X Y) (holeInvIm X Y)) :=
    Real.sqrt_pos.2 (bridgeQ0_pos ha)
  have hf : ContDiffAt ℝ ∞ (fun t => holeInvRe t Y) X := by
    unfold holeInvRe
    fun_prop (disch := positivity)
  have hg : ContDiffAt ℝ ∞ (fun t => holeInvIm t Y) X := by
    unfold holeInvIm
    fun_prop (disch := positivity)
  have hgd : DifferentiableAt ℝ
      (fun t => Real.sqrt (bridgeQ0 (holeInvRe t Y) (holeInvIm t Y))) X :=
    (contDiffAt_sqrtQ0_comp hf hg ha).differentiableAt (by simp)
  have hI : HasDerivAt (fun t => bridgeIm0 (holeInvRe t Y) (holeInvIm t Y))
      ((X ^ 2 - Y ^ 2) / (4 * (X ^ 2 + Y ^ 2) ^ 2) *
          Real.sqrt (bridgeQ0 (holeInvRe X Y) (holeInvIm X Y)) +
        holeInvRe X Y * deriv (fun t => Real.sqrt (bridgeQ0 (holeInvRe t Y) (holeInvIm t Y))) X)
      X :=
    (hasDerivAt_holeInvRe hY).mul hgd.hasDerivAt
  have hR0 : bridgeRe0 (holeInvRe X Y) (holeInvIm X Y) - 3 / 2 ≠ 0 := (sub_pos.2 h).ne'
  refine ⟨_, ?_, hasDerivAt_arctan_div hR hI hR0⟩
  rcases eq_or_ne X 0 with hX | hX
  · subst hX
    have h0 : holeInvRe 0 Y = 0 := by simp [holeInvRe]
    have hd : ∀ d : ℝ, holeInvRe 0 Y * d = 0 := fun d => by rw [h0, zero_mul]
    have hI0 : bridgeIm0 (holeInvRe 0 Y) (holeInvIm 0 Y) = 0 := hd _
    have hRpos : 0 < bridgeRe0 (holeInvRe 0 Y) (holeInvIm 0 Y) - 3 / 2 := sub_pos.2 h
    have hc : ((0 : ℝ) ^ 2 - Y ^ 2) / (4 * (0 ^ 2 + Y ^ 2) ^ 2) < 0 :=
      div_neg_of_neg_of_pos (by nlinarith) (by positivity)
    apply div_neg_of_neg_of_pos
    · simp only [hI0, hd, zero_mul, add_zero, sub_zero]
      exact mul_neg_of_pos_of_neg hRpos (mul_neg_of_neg_of_pos hc hsq)
    · simp only [hI0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
      positivity
  · have hK : ∀ s, (fun t => bridgeRe0 (holeInvRe t Y) (holeInvIm t Y) - 3 / 2) s ^ 2 +
        (fun t => bridgeIm0 (holeInvRe t Y) (holeInvIm t Y)) s ^ 2 = bridgeSigma Y ^ 2 := by
      intro s
      have := bridgeRe0_sub_sq_add_bridgeIm0_sq (x := holeInvRe s Y) (holeInvIm_pos (X := s) hY)
      rwa [heightOne_holeInv hY] at this
    have hI0 : (fun t => bridgeIm0 (holeInvRe t Y) (holeInvIm t Y)) X ≠ 0 := by
      refine mul_ne_zero ?_ hsq.ne'
      have : 0 < 4 * (X ^ 2 + Y ^ 2) := by positivity
      exact div_ne_zero (neg_ne_zero.2 hX) this.ne'
    rw [arctan_div_deriv_eq hR hI hK hI0]
    simp only [bridgeIm0, neg_neg]
    exact div_neg_aux (c := 4 * (X ^ 2 + Y ^ 2)) hX hP hsq (by positivity)

theorem bridgeZero_sub_eq_polar {z : ℂ} (hz : 0 < z.im) (h : 3 / 2 < bridgeRe0 z.re z.im) :
    bridgeZero z - 3 / 2 = (bridgeSigma (heightOne z.re z.im) : ℂ) *
      Complex.exp (Complex.I * (angleZeroHole z.re z.im : ℂ)) := by
  have he : bridgeZero z - 3 / 2 = ⟨bridgeRe0 z.re z.im - 3 / 2, bridgeIm0 z.re z.im⟩ := by
    apply Complex.ext <;> simp [bridgeZero_re, bridgeZero_im]
  rw [he]
  exact eq_polar_of_re_pos (by linarith [half_lt_bridgeSigma (heightOne z.re z.im)])
    (by linarith) (bridgeRe0_sub_sq_add_bridgeIm0_sq hz)

end GC.Seifert

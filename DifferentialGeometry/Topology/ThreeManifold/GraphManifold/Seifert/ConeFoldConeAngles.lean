import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldCornerZero

/-!
# Angles of the bridges about `-3/2` along circles at the cone vertex

Lane A4, tier 2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5).
The hyperbolic circles about a point `v` of the upper half-plane are the curves
`circleCurve v ω₀ t = (v - v̄ ω₀ e^{it})/(1 - ω₀ e^{it})`, on which the disc coordinate is
`ω₀ e^{it}` (`coneDisc_circleCurve`); through `z` (with `ω₀ = coneDisc v z`) the velocity is
`(z - v)(z - v̄)/(2 Im v)` (`hasDerivAt_circleCurve`, `circle_velocity`). Along the circles about
the cone vertex `v₁` the virtual height `η₁` is constant, the height `y` has derivative
`-y |z - v̄₁|² wallOne/(2 (Im v₁)²)` and, for the `(p, ⊤, ⊤)` shapes, `η₀` has derivative
`-(1 + cos θ₁) |z - v̄₁|² wallTwo/(sin²θ₁ y)` (`circle_eta_zero_identity`). The circles about
`-3/2` of radius `G(η₁)` carry both bridges of the cone corner; their angles about `-3/2`,
`angleOneCone` (wall-1 bridge) and `angleTwoCone` (wall-2 bridge), strictly decrease along the
circles about `v₁` oriented from wall 1 to wall 2 (`exists_hasDerivAt_angleOneCone`,
`exists_hasDerivAt_angleTwoCone`): this is the angular monotonicity of the cone corner.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

def circleCurve (v ω₀ : ℂ) (t : ℝ) : ℂ :=
  (v - conj v * (ω₀ * exp ((t : ℂ) * I))) / (1 - ω₀ * exp ((t : ℂ) * I))

theorem norm_mul_exp_mul_I' (ω₀ : ℂ) (t : ℝ) : ‖ω₀ * exp ((t : ℂ) * I)‖ = ‖ω₀‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem one_sub_ne_of_norm_lt {w : ℂ} (h : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h0
  have : w = 1 := by linear_combination -h0
  rw [this] at h
  simp at h

theorem sub_conj_self_ne {v : ℂ} (hv : 0 < v.im) : v - conj v ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem coneDisc_circleCurve {v ω₀ : ℂ} (hv : 0 < v.im) (hω : ‖ω₀‖ < 1) (t : ℝ) :
    coneDisc v (circleCurve v ω₀ t) = ω₀ * exp ((t : ℂ) * I) := by
  set w := ω₀ * exp ((t : ℂ) * I) with hwdef
  have h1 : 1 - w ≠ 0 := one_sub_ne_of_norm_lt (by rw [hwdef, norm_mul_exp_mul_I']; exact hω)
  have hvv := sub_conj_self_ne hv
  have e1 : circleCurve v ω₀ t - v = (v - conj v) * w / (1 - w) := by
    rw [circleCurve, ← hwdef]
    field_simp
    ring
  have e2 : circleCurve v ω₀ t - conj v = (v - conj v) / (1 - w) := by
    rw [circleCurve, ← hwdef]
    field_simp
    ring
  rw [coneDisc, e1, e2]
  field_simp

theorem circleCurve_zero {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) :
    circleCurve v (coneDisc v z) 0 = z := by
  have h1 : 1 - coneDisc v z ≠ 0 := one_sub_ne_of_norm_lt (norm_coneDisc_lt_one hv hz)
  have e := mul_one_sub_coneDisc hv hz
  simp only [circleCurve, ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [div_eq_iff h1]
  exact e.symm

theorem circleCurve_im_mul {v ω₀ : ℂ} (hω : ‖ω₀‖ < 1) (t : ℝ) :
    (circleCurve v ω₀ t).im * normSq (1 - ω₀ * exp ((t : ℂ) * I)) =
      v.im * (1 - normSq (ω₀ * exp ((t : ℂ) * I))) := by
  set w := ω₀ * exp ((t : ℂ) * I) with hwdef
  have h1 : 1 - w ≠ 0 := one_sub_ne_of_norm_lt (by rw [hwdef, norm_mul_exp_mul_I']; exact hω)
  have hn : normSq (1 - w) ≠ 0 := normSq_eq_zero.not.2 h1
  rw [circleCurve, ← hwdef, div_im]
  field_simp
  simp only [normSq_apply, sub_re, sub_im, one_re, one_im, mul_re, mul_im, conj_re, conj_im]
  ring

theorem circleCurve_im_pos {v ω₀ : ℂ} (hv : 0 < v.im) (hω : ‖ω₀‖ < 1) (t : ℝ) :
    0 < (circleCurve v ω₀ t).im := by
  have h := circleCurve_im_mul (v := v) hω t
  have hn : 0 < normSq (1 - ω₀ * exp ((t : ℂ) * I)) :=
    normSq_pos.2 (one_sub_ne_of_norm_lt (by rw [norm_mul_exp_mul_I']; exact hω))
  have hlt : normSq (ω₀ * exp ((t : ℂ) * I)) < 1 := by
    rw [← Complex.sq_norm, norm_mul_exp_mul_I']
    nlinarith [norm_nonneg ω₀]
  have : 0 < v.im * (1 - normSq (ω₀ * exp ((t : ℂ) * I))) := mul_pos hv (by linarith)
  rw [← h] at this
  exact pos_of_mul_pos_left this hn.le

theorem hasDerivAt_rot (ω₀ : ℂ) :
    HasDerivAt (fun t : ℝ => ω₀ * exp ((t : ℂ) * I)) (ω₀ * I) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I
  have h2 := (h1.cexp).const_mul ω₀
  refine h2.congr_deriv ?_
  simp

theorem hasDerivAt_circleCurve {v ω₀ : ℂ} (hω : ‖ω₀‖ < 1) :
    HasDerivAt (circleCurve v ω₀) ((v - conj v) * (ω₀ * I) / (1 - ω₀) ^ 2) 0 := by
  have hr := hasDerivAt_rot ω₀
  have hn := (hr.const_mul (conj v)).const_sub v
  have hd := hr.const_sub 1
  have hne : (fun t : ℝ => 1 - ω₀ * exp ((t : ℂ) * I)) 0 ≠ 0 := by
    simpa using one_sub_ne_of_norm_lt hω
  have h := hn.div hd hne
  refine h.congr_deriv ?_
  have h1 : 1 - ω₀ ≠ 0 := one_sub_ne_of_norm_lt hω
  simp only [ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  field_simp
  ring

theorem circle_velocity {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) :
    (v - conj v) * (coneDisc v z * I) / (1 - coneDisc v z) ^ 2 =
      (z - v) * (z - conj v) / (2 * v.im) := by
  have h1 := sub_conj_ne_zero hv hz
  have hb : (v - conj v) = 2 * v.im * I := by
    rw [Complex.sub_conj]
    push_cast
    ring
  have hb0 : (v.im : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  rw [one_sub_coneDisc hv hz, coneDisc, hb]
  field_simp

theorem circle_velocity_im (v z : ℂ) (hv : 0 < v.im) :
    ((z - v) * (z - conj v) / (2 * v.im)).im = z.im * (z.re - v.re) / v.im := by
  have e : (z - v) * (z - conj v) / (2 * (v.im : ℂ)) =
      ((1 / (2 * v.im) : ℝ) : ℂ) * ((z - v) * (z - conj v)) := by
    push_cast
    ring
  rw [e, Complex.im_ofReal_mul]
  simp only [mul_im, sub_re, sub_im, conj_re, conj_im]
  field_simp
  ring

theorem circle_velocity_re (v z : ℂ) (hv : 0 < v.im) :
    ((z - v) * (z - conj v) / (2 * v.im)).re =
      ((z.re - v.re) ^ 2 - z.im ^ 2 + v.im ^ 2) / (2 * v.im) := by
  have e : (z - v) * (z - conj v) / (2 * (v.im : ℂ)) =
      ((1 / (2 * v.im) : ℝ) : ℂ) * ((z - v) * (z - conj v)) := by
    push_cast
    ring
  rw [e, Complex.re_ofReal_mul]
  simp only [mul_re, sub_re, sub_im, conj_re, conj_im]
  field_simp
  ring

theorem continuous_circleCurve {v ω₀ : ℂ} (hω : ‖ω₀‖ < 1) : Continuous (circleCurve v ω₀) := by
  have hc : Continuous fun t : ℝ => ω₀ * exp ((t : ℂ) * I) :=
    continuous_const.mul (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const))
  exact (continuous_const.sub (continuous_const.mul hc)).div (continuous_const.sub hc)
    (fun t => one_sub_ne_of_norm_lt (by rw [norm_mul_exp_mul_I']; exact hω))

namespace ConeShape

variable (σ : ConeShape)

def angleOneCone (z : ℂ) : ℝ :=
  negHalfArg (coneProfile σ.constK (σ.etaOne z)) ((σ.bridgeOne z).re + 3 / 2)
    (σ.bridgeOne z).im

def angleTwoCone (z : ℂ) : ℝ :=
  halfArg (coneProfile σ.constK (σ.etaOne z)) ((σ.bridgeTwo z).re + 3 / 2) (σ.bridgeTwo z).im

theorem circle_y_identity {z : ℂ} (hz : 0 < z.im) :
    ((z - σ.vertexOne) * (z - conj σ.vertexOne) / (2 * σ.vertexOne.im)).im =
      σ.wallOne z * (-(z.im * normSq (z - conj σ.vertexOne) / (2 * σ.vertexOne.im ^ 2))) := by
  have hv := σ.vertexOne_im_pos
  have hw := σ.im_coneDisc_vertexOne_mul z
  have hN := normSq_sub_conj_pos hv hz
  rw [circle_velocity_im _ _ hv]
  have hw' : σ.wallOne z = 2 * σ.vertexOne.im * σ.wallSide 1 z /
      normSq (z - conj σ.vertexOne) := by
    rw [eq_div_iff hN.ne', wallOne, discOne]
    exact hw
  rw [hw', vertexOne_re]
  simp only [wallSide]
  field_simp
  ring

theorem etaOne_circleCurve {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    σ.etaOne (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t) = σ.etaOne z := by
  have hv := σ.vertexOne_im_pos
  have hω := norm_coneDisc_lt_one hv hz
  simp only [etaOne, coneHeight]
  rw [coneDisc_circleCurve hv hω, norm_mul_exp_mul_I']

theorem wallOne_circleCurve {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    σ.wallOne (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t) =
      (coneDisc σ.vertexOne z * exp ((t : ℂ) * I)).im := by
  rw [wallOne, discOne, coneDisc_circleCurve σ.vertexOne_im_pos
    (norm_coneDisc_lt_one σ.vertexOne_im_pos hz)]

theorem wallTwo_circleCurve {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    σ.wallTwo (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t) =
      -(exp (-(σ.θ₁ * I)) * (coneDisc σ.vertexOne z * exp ((t : ℂ) * I))).im := by
  rw [wallTwo, discOne, coneDisc_circleCurve σ.vertexOne_im_pos
    (norm_coneDisc_lt_one σ.vertexOne_im_pos hz)]

theorem hasDerivAt_circle_velocity {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (circleCurve σ.vertexOne (coneDisc σ.vertexOne z))
      ((z - σ.vertexOne) * (z - conj σ.vertexOne) / (2 * σ.vertexOne.im)) 0 := by
  have hv := σ.vertexOne_im_pos
  have h := hasDerivAt_circleCurve (v := σ.vertexOne) (norm_coneDisc_lt_one hv hz)
  rwa [circle_velocity hv hz] at h

theorem re_pos_of_im_eq_zero {w : ℂ} (h : 0 < ‖w‖ + w.re) (hi : w.im = 0) : 0 < w.re := by
  have hn : ‖w‖ = |w.re| := by
    rw [← Complex.abs_re_eq_norm.2 hi]
  rw [hn] at h
  rcases le_or_gt w.re 0 with h' | h'
  · rw [abs_of_nonpos h'] at h
    linarith
  · exact h'

theorem bridgeOne_cone_pos {z : ℂ} (hz : z ∈ σ.domOne) :
    0 < coneProfile σ.constK (σ.etaOne z) - ((σ.bridgeOne z).re - -(3 / 2)) := by
  have hK := σ.constK_pos
  have e1 := sq_add_sq_eq_of_norm (σ.norm_bridgeOne_add hz)
  have e2 := sq_add_sq_eq_of_norm (σ.norm_bridgeOne hz)
  simp only [add_re, add_im, div_ofNat_re, div_ofNat_im] at e1
  have hG := half_lt_coneProfile hK (σ.etaOne_pos hz.1).ne'
  have hG' := coneProfile_lt hK (σ.etaOne z)
  have hR : 2 < 3 / 2 + coneProfile σ.constK z.im := by
    have := half_lt_coneProfile hK hz.1.ne'
    linarith
  by_contra hc
  have hle : coneProfile σ.constK (σ.etaOne z) ≤ (σ.bridgeOne z).re + 3 / 2 := by
    linarith [not_lt.1 hc]
  norm_num at e1
  nlinarith

theorem exists_hasDerivAt_angleOneCone {z : ℂ} (hz : z ∈ σ.domOne) :
    ∃ D : ℝ, D < 0 ∧ HasDerivAt
      (fun t : ℝ => σ.angleOneCone (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t)) D 0 := by
  have hK := σ.constK_pos
  have hv := σ.vertexOne_im_pos
  have hω := norm_coneDisc_lt_one hv hz.1
  have h0 : circleCurve σ.vertexOne (coneDisc σ.vertexOne z) 0 = z := circleCurve_zero hv hz.1
  have hγ := σ.hasDerivAt_circle_velocity hz.1
  have hev : ∀ᶠ t : ℝ in 𝓝 0, circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t ∈ σ.domOne := by
    have := (continuous_circleCurve (v := σ.vertexOne) hω).continuousAt (x := 0)
      |>.preimage_mem_nhds (σ.isOpen_domOne.mem_nhds (by rw [h0]; exact hz))
    exact this
  have hwc : ∀ t : ℝ, σ.wallOne (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t) =
      (coneDisc σ.vertexOne z * exp ((t : ℂ) * I)).im := fun t => σ.wallOne_circleCurve hz.1 t
  have hηc : ∀ t : ℝ, σ.etaOne (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t) =
      σ.etaOne z := fun t => σ.etaOne_circleCurve hz.1 t
  set K := σ.constK
  set ω₀ := coneDisc σ.vertexOne z with hω₀
  set γ := circleCurve σ.vertexOne ω₀ with hγdef
  set η₁ := σ.etaOne z with hη₁
  set A₀ := coneProfile K η₁ with hA₀
  have hA₀pos : 0 < A₀ := by have := half_le_coneProfile hK η₁; linarith
  set y : ℝ → ℝ := fun t => (γ t).im with hydef
  have hy0 : y 0 = z.im := by simp [hydef, h0]
  have hy' : HasDerivAt y (σ.wallOne z *
      (-(z.im * normSq (z - conj σ.vertexOne) / (2 * σ.vertexOne.im ^ 2)))) 0 := by
    have := (imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ)
    refine this.congr_deriv ?_
    simp only [imCLM_apply]
    exact σ.circle_y_identity hz.1
  set κy := -(z.im * normSq (z - conj σ.vertexOne) / (2 * σ.vertexOne.im ^ 2)) with hκy
  have hκyneg : κy < 0 := by
    have := normSq_sub_conj_pos hv hz.1
    have := hz.1
    rw [hκy, neg_lt_zero]
    positivity
  set κ := 4 * K * z.im / (z.im ^ 2 + K) ^ 2 * κy with hκ
  have hκneg : κ < 0 := by
    have : 0 < 4 * K * z.im / (z.im ^ 2 + K) ^ 2 := by have := hz.1; positivity
    exact mul_neg_of_pos_of_neg this hκyneg
  have hB : HasDerivAt (fun t => 3 / 2 + coneProfile K (y t)) (σ.wallOne (γ 0) * κ) 0 := by
    have := ((hasDerivAt_coneProfile hK (y 0)).comp 0 hy').const_add (3 / 2)
    refine this.congr_deriv ?_
    rw [hy0, h0, hκ]
    ring
  have hw : HasDerivAt (fun t => σ.wallOne (γ t)) ω₀.re 0 := by
    have e : (fun t => σ.wallOne (γ t)) = fun t : ℝ => (ω₀ * exp ((t : ℂ) * I)).im := funext hwc
    rw [e]
    have := imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_rot ω₀)
    refine this.congr_deriv ?_
    simp
  have hPc : ContDiffAt ℝ ∞ (fun u : ℂ => outerCofactor K (-(3 / 2)) u.im η₁ (σ.cofOne u)) z := by
    have h2 := σ.contDiffAt_cofOne hz
    have hi : ContDiffAt ℝ ∞ (fun u : ℂ => u.im) z := imCLM.contDiff.contDiffAt
    have hηz := σ.etaOne_pos hz.1
    unfold outerCofactor
    have hd : (η₁ ^ 2 + K) * (z.im ^ 2 + K) ≠ 0 := by positivity
    have hG' := (contDiff_coneProfile hK).contDiffAt (x := z.im)
    exact ((((contDiffAt_const.add (hG'.comp z hi)).add contDiffAt_const).pow 2).sub
      contDiffAt_const).mul (((contDiffAt_const.add (hG'.comp z hi)).sub
        contDiffAt_const)) |>.mul
      (h2.mul ((contDiffAt_const.mul (contDiffAt_const.add hi)).div
        (contDiffAt_const.mul (hi.pow 2 |>.add contDiffAt_const)) hd))
  have hPd : DifferentiableAt ℝ
      (fun t : ℝ => outerCofactor K (-(3 / 2)) (y t) η₁ (σ.cofOne (γ t))) 0 := by
    have := ((hPc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ
      h0.symm).differentiableAt
    simpa [Function.comp_def, hydef] using this
  have hP0 : ∀ᶠ t : ℝ in 𝓝 0, 0 < outerCofactor K (-(3 / 2)) (y t) η₁ (σ.cofOne (γ t)) := by
    filter_upwards [hev] with t ht
    exact outerCofactor_pos hK (Or.inr rfl) ht.1 (σ.etaOne_pos hz.1) (σ.cofOne_pos ht)
  have hH : ∀ᶠ t : ℝ in 𝓝 0, ((A₀ + (3 / 2 + coneProfile K (y t))) ^ 2 - (0 - -(3 / 2)) ^ 2) *
      ((0 - -(3 / 2)) ^ 2 - (A₀ - (3 / 2 + coneProfile K (y t))) ^ 2) =
      σ.wallOne (γ t) ^ 2 * outerCofactor K (-(3 / 2)) (y t) η₁ (σ.cofOne (γ t)) := by
    filter_upwards [hev] with t ht
    have hsub := σ.etaOne_sub_im ht
    rw [hηc t] at hsub
    have h := outerBridge_heron hK (Or.inr rfl) hsub
    rw [hA₀]
    linear_combination h
  have hbr : ∀ t, σ.bridgeOne (γ t) = twoCircle (-(3 / 2)) 0 A₀ (3 / 2 + coneProfile K (y t))
      (σ.wallOne (γ t)) (outerCofactor K (-(3 / 2)) (y t) η₁ (σ.cofOne (γ t))) := by
    intro t
    rw [bridgeOne, outerBridge, twoCircle_swap, hηc t]
  have hpos : 0 < A₀ - ((twoCircle (-(3 / 2)) 0 A₀ (3 / 2 + coneProfile K (y 0))
      (σ.wallOne (γ 0)) (outerCofactor K (-(3 / 2)) (y 0) η₁ (σ.cofOne (γ 0)))).re - -(3 / 2)) := by
    rw [← hbr 0, h0]
    exact σ.bridgeOne_cone_pos hz
  have h := hasDerivAt_negHalfArg_twoCircle' (a := -(3 / 2)) (b := 0) (by norm_num) hA₀pos hB hw
    hPd hP0 hH hpos
  have he : (fun t : ℝ => σ.angleOneCone (γ t)) = fun t : ℝ => negHalfArg A₀
      ((twoCircle (-(3 / 2)) 0 A₀ (3 / 2 + coneProfile K (y t)) (σ.wallOne (γ t))
        (outerCofactor K (-(3 / 2)) (y t) η₁ (σ.cofOne (γ t)))).re - -(3 / 2))
      (twoCircle (-(3 / 2)) 0 A₀ (3 / 2 + coneProfile K (y t)) (σ.wallOne (γ t))
        (outerCofactor K (-(3 / 2)) (y t) η₁ (σ.cofOne (γ t)))).im := by
    funext t
    rw [angleOneCone, hbr t, hηc t, sub_neg_eq_add]
  rw [he]
  refine ⟨_, ?_, h⟩
  have hsq := Real.sqrt_pos.2 (hP0.self_of_nhds)
  split_ifs with hw0
  · rw [h0] at hw0
    have hre : 0 < ω₀.re := re_pos_of_im_eq_zero hz.2 (by simpa [wallOne, discOne] using hw0)
    have h3 : (0 : ℝ) < 2 * |0 - -(3 / 2)| * A₀ := by positivity
    have : 0 < ω₀.re * Real.sqrt (outerCofactor K (-(3 / 2)) (y 0) η₁ (σ.cofOne (γ 0))) /
        (2 * |0 - -(3 / 2)| * A₀) := by positivity
    linarith
  · have hB0 : 0 < 3 / 2 + coneProfile K (y 0) := by
      have := half_le_coneProfile hK (y 0)
      linarith
    have e : 2 * |(0 : ℝ) - -(3 / 2)| * (3 / 2 + coneProfile K (y 0)) * κ /
        ((0 - -(3 / 2)) * Real.sqrt (outerCofactor K (-(3 / 2)) (y 0) η₁ (σ.cofOne (γ 0)))) =
        2 * (3 / 2 + coneProfile K (y 0)) * κ /
          Real.sqrt (outerCofactor K (-(3 / 2)) (y 0) η₁ (σ.cofOne (γ 0))) := by
      rw [show |(0 : ℝ) - -(3 / 2)| = 3 / 2 by norm_num]
      field_simp
      ring
    rw [e]
    have : 2 * (3 / 2 + coneProfile K (y 0)) * κ < 0 := by
      have : 0 < 2 * (3 / 2 + coneProfile K (y 0)) := by positivity
      exact mul_neg_of_pos_of_neg this hκneg
    exact div_neg_of_neg_of_pos this hsq

theorem circle_eta_zero_identity (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im) :
    (2 * (z.re * ((z - σ.vertexOne) * (z - conj σ.vertexOne) / (2 * σ.vertexOne.im)).re +
        z.im * ((z - σ.vertexOne) * (z - conj σ.vertexOne) / (2 * σ.vertexOne.im)).im) * z.im -
      normSq z * ((z - σ.vertexOne) * (z - conj σ.vertexOne) / (2 * σ.vertexOne.im)).im) /
        z.im ^ 2 =
      σ.wallTwo z * (-((1 + Real.cos σ.θ₁) * normSq (z - conj σ.vertexOne) /
        (Real.sin σ.θ₁ ^ 2 * z.im))) := by
  have hv := σ.vertexOne_im_pos
  have hs1 := σ.sin_θ₁_pos
  have hN := normSq_sub_conj_pos hv hz
  have hw := σ.wallTwo_mul hθ z
  have hs := Real.sin_sq_add_cos_sq σ.θ₁
  have hw' : σ.wallTwo z = Real.sin σ.θ₁ * ((z.re - 1 / 4) ^ 2 + z.im ^ 2 - 1 / 16) /
      normSq (z - conj σ.vertexOne) := by
    rw [eq_div_iff hN.ne']
    exact hw
  rw [circle_velocity_re _ _ hv, circle_velocity_im _ _ hv, hw', vertexOne_re, vertexOne_im,
    width, hθ, Real.cos_zero, normSq_apply]
  field_simp
  linear_combination (64 * z.re) * hs

theorem bridgeTwo_cone_pos (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.domTwo) :
    0 < coneProfile σ.constK (σ.etaOne z) + ((σ.bridgeTwo z).re - -(3 / 2)) := by
  have hK := σ.constK_pos
  have e1 := sq_add_sq_eq_of_norm (σ.norm_bridgeTwo_add hθ hz)
  simp only [add_re, add_im, div_ofNat_re, div_ofNat_im] at e1
  norm_num at e1
  have h2 := σ.norm_bridgeTwo_lt_two hθ hz
  have e2 : (σ.bridgeTwo z).re ^ 2 + (σ.bridgeTwo z).im ^ 2 < 4 := by
    have := sq_add_sq_eq_of_norm (u := σ.bridgeTwo z) rfl
    nlinarith [norm_nonneg (σ.bridgeTwo z)]
  have hG := half_lt_coneProfile hK (σ.etaOne_pos hz.1).ne'
  by_contra hc
  have hle : (σ.bridgeTwo z).re + 3 / 2 ≤ -coneProfile σ.constK (σ.etaOne z) := by
    linarith [not_lt.1 hc]
  nlinarith

theorem exists_hasDerivAt_angleTwoCone (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.domTwo) :
    ∃ D : ℝ, D < 0 ∧ HasDerivAt
      (fun t : ℝ => σ.angleTwoCone (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t)) D 0 := by
  have hK := σ.constK_pos
  have hv := σ.vertexOne_im_pos
  have hω := norm_coneDisc_lt_one hv hz.1
  have h0 : circleCurve σ.vertexOne (coneDisc σ.vertexOne z) 0 = z := circleCurve_zero hv hz.1
  have hγ := σ.hasDerivAt_circle_velocity hz.1
  have hev : ∀ᶠ t : ℝ in 𝓝 0, circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t ∈ σ.domTwo := by
    have := (continuous_circleCurve (v := σ.vertexOne) hω).continuousAt (x := 0)
      |>.preimage_mem_nhds (σ.isOpen_domTwo.mem_nhds (by rw [h0]; exact hz))
    exact this
  have hwc : ∀ t : ℝ, σ.wallTwo (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t) =
      -(exp (-(σ.θ₁ * I)) * (coneDisc σ.vertexOne z * exp ((t : ℂ) * I))).im :=
    fun t => σ.wallTwo_circleCurve hz.1 t
  have hηc : ∀ t : ℝ, σ.etaOne (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t) =
      σ.etaOne z := fun t => σ.etaOne_circleCurve hz.1 t
  have hid := σ.circle_eta_zero_identity hθ hz.1
  set K := σ.constK
  set ω₀ := coneDisc σ.vertexOne z with hω₀
  set γ := circleCurve σ.vertexOne ω₀ with hγdef
  set V := (z - σ.vertexOne) * (z - conj σ.vertexOne) / (2 * σ.vertexOne.im) with hV
  set η₁ := σ.etaOne z with hη₁
  set A₀ := coneProfile K η₁ with hA₀
  have hA₀pos : 0 < A₀ := by have := half_le_coneProfile hK η₁; linarith
  set e : ℝ → ℝ := fun t => cuspZeroHeight (γ t) with hedef
  have he0 : e 0 = cuspZeroHeight z := by simp [hedef, h0]
  set κ₀ := -((1 + Real.cos σ.θ₁) * normSq (z - conj σ.vertexOne) /
    (Real.sin σ.θ₁ ^ 2 * z.im)) with hκ₀
  have hκ₀neg : κ₀ < 0 := by
    have := normSq_sub_conj_pos hv hz.1
    have := σ.one_add_cos_θ₁_pos
    have := σ.sin_θ₁_pos
    have := hz.1
    rw [hκ₀, neg_lt_zero]
    positivity
  have he' : HasDerivAt e (σ.wallTwo z * κ₀) 0 := by
    have hn := hasDerivAt_normSq_curve hγ 0
    have hi : HasDerivAt (fun t => (γ t).im) V.im 0 := by
      refine (imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ).congr_deriv ?_
      simp
    have hne : (fun t => (γ t).im) 0 ≠ 0 := by
      dsimp only
      rw [h0]
      exact hz.1.ne'
    have h := hn.div hi hne
    have e1 : (fun t => normSq (γ t - 0)) / (fun t => (γ t).im) = e := by
      funext t
      simp [hedef, cuspZeroHeight]
    rw [e1] at h
    refine h.congr_deriv ?_
    rw [← hid]
    simp only [h0, sub_zero]
  set κ := 4 * K * e 0 / (e 0 ^ 2 + K) ^ 2 * κ₀ with hκ
  have hκneg : κ < 0 := by
    have : 0 < e 0 := by rw [he0]; exact cuspZeroHeight_pos hz.1
    have : 0 < 4 * K * e 0 / (e 0 ^ 2 + K) ^ 2 := by positivity
    exact mul_neg_of_pos_of_neg this hκ₀neg
  have hB : HasDerivAt (fun t => coneProfile K (e t)) (σ.wallTwo (γ 0) * κ) 0 := by
    refine ((hasDerivAt_coneProfile hK (e 0)).comp 0 he').congr_deriv ?_
    rw [h0, hκ]
    ring
  set c := exp (-(σ.θ₁ * I)) with hc
  have hw : HasDerivAt (fun t => σ.wallTwo (γ t)) (-(c * ω₀).re) 0 := by
    have e2 : (fun t => σ.wallTwo (γ t)) =
        fun t : ℝ => -(c * (ω₀ * exp ((t : ℂ) * I))).im := funext hwc
    rw [e2]
    have := (imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_rot ω₀).const_mul c)).neg
    refine this.congr_deriv ?_
    simp
    ring
  have hPc : ContDiffAt ℝ ∞
      (fun u : ℂ => innerCofactor K (cuspZeroHeight u) η₁ (σ.cofTwo u)) z := by
    have h1 := contDiffAt_cuspZeroHeight hz.1
    have h2 := σ.contDiffAt_cofTwo hz
    have hηz := σ.etaOne_pos hz.1
    have hcz := cuspZeroHeight_pos hz.1
    unfold innerCofactor
    have hd : (cuspZeroHeight z ^ 2 + K) * (η₁ ^ 2 + K) ≠ 0 := by positivity
    have hG' := (contDiff_coneProfile hK).contDiffAt (x := cuspZeroHeight z)
    exact ((((hG'.comp z h1).add contDiffAt_const).add contDiffAt_const).mul
      (contDiffAt_const.sub (((hG'.comp z h1).sub contDiffAt_const).pow 2))).mul
      (h2.mul ((contDiffAt_const.mul ((contDiffAt_const.mul h1).add contDiffAt_const)).div
        (((h1.pow 2).add contDiffAt_const).mul contDiffAt_const) hd))
  have hPd : DifferentiableAt ℝ
      (fun t : ℝ => innerCofactor K (e t) η₁ (σ.cofTwo (γ t))) 0 := by
    have := ((hPc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ
      h0.symm).differentiableAt
    simpa [Function.comp_def, hedef] using this
  have hP0 : ∀ᶠ t : ℝ in 𝓝 0, 0 < innerCofactor K (e t) η₁ (σ.cofTwo (γ t)) := by
    filter_upwards [hev] with t ht
    exact innerCofactor_pos hK (cuspZeroHeight_pos ht.1) (σ.etaOne_pos hz.1) (σ.cofTwo_pos ht)
  have hH : ∀ᶠ t : ℝ in 𝓝 0, ((A₀ + coneProfile K (e t)) ^ 2 - (3 / 2 - -(3 / 2)) ^ 2) *
      ((3 / 2 - -(3 / 2)) ^ 2 - (A₀ - coneProfile K (e t)) ^ 2) =
      σ.wallTwo (γ t) ^ 2 * innerCofactor K (e t) η₁ (σ.cofTwo (γ t)) := by
    filter_upwards [hev] with t ht
    have hd := σ.etaOne_mul_cuspZeroHeight_sub hθ ht
    rw [hηc t] at hd
    have h := innerBridge_heron hK hd
    rw [hA₀]
    linear_combination h
  have hbr : ∀ t, σ.bridgeTwo (γ t) = twoCircle (-(3 / 2)) (3 / 2) A₀ (coneProfile K (e t))
      (σ.wallTwo (γ t)) (innerCofactor K (e t) η₁ (σ.cofTwo (γ t))) := by
    intro t
    rw [bridgeTwo, innerBridge, twoCircle_swap, hηc t]
  have hpos : 0 < A₀ + ((twoCircle (-(3 / 2)) (3 / 2) A₀ (coneProfile K (e 0))
      (σ.wallTwo (γ 0)) (innerCofactor K (e 0) η₁ (σ.cofTwo (γ 0)))).re - -(3 / 2)) := by
    rw [← hbr 0, h0]
    exact σ.bridgeTwo_cone_pos hθ hz
  have h := hasDerivAt_halfArg_twoCircle' (a := -(3 / 2)) (b := 3 / 2) (by norm_num) hA₀pos hB
    hw hPd hP0 hH hpos
  have he2 : (fun t : ℝ => σ.angleTwoCone (γ t)) = fun t : ℝ => halfArg A₀
      ((twoCircle (-(3 / 2)) (3 / 2) A₀ (coneProfile K (e t)) (σ.wallTwo (γ t))
        (innerCofactor K (e t) η₁ (σ.cofTwo (γ t)))).re - -(3 / 2))
      (twoCircle (-(3 / 2)) (3 / 2) A₀ (coneProfile K (e t)) (σ.wallTwo (γ t))
        (innerCofactor K (e t) η₁ (σ.cofTwo (γ t)))).im := by
    funext t
    rw [angleTwoCone, hbr t, hηc t, sub_neg_eq_add]
  rw [he2]
  refine ⟨_, ?_, h⟩
  have hsq := Real.sqrt_pos.2 (hP0.self_of_nhds)
  split_ifs with hw0
  · rw [h0] at hw0
    have hnc : ‖c‖ = 1 := by
      rw [hc, Complex.norm_exp]
      simp
    have hre : 0 < (c * ω₀).re := by
      apply re_pos_of_im_eq_zero
      · rw [norm_mul, hnc, one_mul]
        exact hz.2
      · have := hwc 0
        rw [h0] at this
        simp only [ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at this
        linarith
    have h3 : (0 : ℝ) < 2 * |3 / 2 - -(3 / 2)| * A₀ := by positivity
    have : 0 < (c * ω₀).re *
        Real.sqrt (innerCofactor K (e 0) η₁ (σ.cofTwo (γ 0))) / (2 * |3 / 2 - -(3 / 2)| * A₀) := by
      positivity
    have e3 : -(c * ω₀).re * Real.sqrt (innerCofactor K (e 0) η₁ (σ.cofTwo (γ 0))) /
        (2 * |3 / 2 - -(3 / 2)| * A₀) = -((c * ω₀).re *
        Real.sqrt (innerCofactor K (e 0) η₁ (σ.cofTwo (γ 0))) / (2 * |3 / 2 - -(3 / 2)| * A₀)) := by
      ring
    rw [e3]
    linarith
  · have hB0 : 0 < coneProfile K (e 0) := by
      have := half_le_coneProfile hK (e 0)
      linarith
    have e3 : 2 * |(3 / 2 : ℝ) - -(3 / 2)| * coneProfile K (e 0) * κ /
        ((3 / 2 - -(3 / 2)) * Real.sqrt (innerCofactor K (e 0) η₁ (σ.cofTwo (γ 0)))) =
        2 * coneProfile K (e 0) * κ / Real.sqrt (innerCofactor K (e 0) η₁ (σ.cofTwo (γ 0))) := by
      rw [show |(3 / 2 : ℝ) - -(3 / 2)| = 3 by norm_num]
      field_simp
      ring
    rw [e3]
    have : 2 * coneProfile K (e 0) * κ < 0 := by
      have : 0 < 2 * coneProfile K (e 0) := by positivity
      exact mul_neg_of_pos_of_neg this hκneg
    exact div_neg_of_neg_of_pos this hsq

end ConeShape

end GC.Seifert

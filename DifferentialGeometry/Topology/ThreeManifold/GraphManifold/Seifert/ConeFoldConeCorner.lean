import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldConeAngles

/-!
# The corner at the cone vertex of the `(p, ⊤, ⊤)` fold

Lane A4, tier 2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5).
In the orientation before the final mirror the cone vertex `v₁` goes to `-3/2` and
`cornerCone p a b φa φb z = -3/2 + S e^{iΘ}` with
* radial profile `S = coneRadial p a b y₁ K η₁ = (1 - τ) ϖ^p/2 + τ G(η₁)`, `τ = coneStep a b η₁`,
  `ϖ = (η₁ - y₁)/(η₁ + y₁) = |ω₁|`, strictly increasing in `η₁ > y₁`
  (`exists_hasDerivAt_coneRadial`, since `G > 1/2 > ϖ^p/2`);
* angle `Θ = (1 - τ)(π - p φ) + τ ((1 - λ) Θ₁' + λ Θ₂')` with `φ = discAngle ω₁` the argument of
  the disc coordinate, `λ = coneStep φa φb φ`, and `Θ₁'`, `Θ₂'` the angles about `-3/2` of the
  wall-1 and wall-2 bridges (`SF/ConeFoldConeAngles`).
For `η₁ ≤ a` it is the apex model `-3/2 - conj(ω₁)^p/2` (`cornerCone_eq_apex`; after the mirror
`u ↦ -ū` this is `3/2 + ω₁^p/2`), for `η₁ ≥ b` it equals the wall-1 bridge where `φ ≤ φa` and the
wall-2 bridge where `φ ≥ φb` (`cornerCone_eq_bridgeOne`, `cornerCone_eq_bridgeTwo`). Off the apex
the Jacobian is nonzero (`det_fderiv_cornerCone_ne_zero`): along the circles about `v₁` the angle
strictly decreases (`exists_hasDerivAt_angleCone`: `-p` from the apex model, the bridge angles
decrease, `λ' (Θ₂' - Θ₁') ≤ 0` where `Θ₂' ≤ Θ₁'`), and `η₁` increases strictly in the direction
`(z - v₁)|z - v̄₁|² - (z - v̄₁)|z - v₁|²` (`radial_vector_ne`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

def coneRadial (p : ℕ) (a b y₁ K η : ℝ) : ℝ :=
  (1 - coneStep a b η) * ((η - y₁) / (η + y₁)) ^ p / 2 + coneStep a b η * coneProfile K η

def discAngle (w : ℂ) : ℝ := halfArg ‖w‖ w.re w.im

theorem halfArg_cos_sin {S x : ℝ} (hS : 0 < S) (hx1 : -Real.pi < x) (hx2 : x < Real.pi) :
    halfArg S (S * Real.cos x) (S * Real.sin x) = x := by
  have hc : 0 < Real.cos (x / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have e : S * Real.sin x / (S + S * Real.cos x) = Real.tan (x / 2) := by
    have h1 : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
      rw [← Real.sin_two_mul]; ring_nf
    have h2 : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
      rw [← Real.cos_two_mul]; ring_nf
    rw [h1, h2, Real.tan_eq_sin_div_cos]
    field_simp
    ring
  rw [halfArg, e, Real.arctan_tan (by linarith) (by linarith)]
  ring

theorem discAngle_mul_exp {w : ℂ} (hw0 : w ≠ 0) (hpos : 0 < ‖w‖ + w.re) {t : ℝ}
    (ht1 : -Real.pi < discAngle w + t) (ht2 : discAngle w + t < Real.pi) :
    discAngle (w * exp ((t : ℂ) * I)) = discAngle w + t := by
  have hS : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hsq : w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; ring
  have hp := halfArg_polar hS hpos hsq
  have hw0' : w = (‖w‖ : ℂ) * exp ((discAngle w : ℂ) * I) := by
    rw [discAngle, ← hp]
  have e : w * exp ((t : ℂ) * I) =
      (‖w‖ : ℂ) * exp (((discAngle w + t : ℝ) : ℂ) * I) := by
    conv_lhs => rw [hw0']
    rw [mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  have hre : (w * exp ((t : ℂ) * I)).re = ‖w‖ * Real.cos (discAngle w + t) := by
    rw [e, re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have him : (w * exp ((t : ℂ) * I)).im = ‖w‖ * Real.sin (discAngle w + t) := by
    rw [e, im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  rw [discAngle, norm_mul_exp_mul_I', hre, him, halfArg_cos_sin hS ht1 ht2]

theorem halfArg_polar_self {w : ℂ} (hw0 : w ≠ 0) (hpos : 0 < ‖w‖ + w.re) :
    w = (‖w‖ : ℂ) * exp ((discAngle w : ℂ) * I) := by
  have hS : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hsq : w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; ring
  rw [discAngle, ← halfArg_polar hS hpos hsq]

theorem exists_hasDerivAt_coneRadial {p : ℕ} (hp : 1 ≤ p) {a b y₁ K η : ℝ} (hab : a < b)
    (hy₁ : 0 < y₁) (hK : 0 < K) (hη : y₁ < η) :
    ∃ S' : ℝ, 0 < S' ∧ HasDerivAt (coneRadial p a b y₁ K) S' η := by
  have hη0 : 0 < η := by linarith
  have hd : η + y₁ ≠ 0 := by linarith
  set ϖ := (η - y₁) / (η + y₁) with hϖ
  have hϖ0 : 0 < ϖ := div_pos (by linarith) (by linarith)
  have hϖ1 : ϖ < 1 := by rw [hϖ, div_lt_one (by linarith)]; linarith
  have hw : HasDerivAt (fun s => (s - y₁) / (s + y₁)) (2 * y₁ / (η + y₁) ^ 2) η := by
    have := ((hasDerivAt_id η).sub_const y₁).div ((hasDerivAt_id η).add_const y₁) hd
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hτ := hasDerivAt_coneStep a b η
  have hG := hasDerivAt_coneProfile hK η
  have h := (((hasDerivAt_const η (1 : ℝ)).sub hτ).mul ((hw.pow p).div_const 2)).add
    (hτ.mul hG)
  have hτ0 := coneStep_nonneg a b η
  have hτ1 := coneStep_le_one a b η
  have hτ' := deriv_coneStep_nonneg hab η
  have h' : HasDerivAt (coneRadial p a b y₁ K)
      (deriv (coneStep a b) η * (coneProfile K η - ϖ ^ p / 2) +
        ((1 - coneStep a b η) * ((p : ℝ) * ϖ ^ (p - 1) * (2 * y₁ / (η + y₁) ^ 2) / 2) +
          coneStep a b η * (4 * K * η / (η ^ 2 + K) ^ 2))) η := by
    convert h using 1
    · funext s
      simp only [coneRadial, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
      ring
    · simp only [Pi.sub_apply, Pi.pow_apply, hϖ]
      ring
  refine ⟨_, ?_, h'⟩
  have hGh := half_lt_coneProfile hK hη0.ne'
  have hpow : ϖ ^ p / 2 < 1 / 2 := by
    have : ϖ ^ p < 1 := pow_lt_one₀ hϖ0.le hϖ1 (by omega)
    linarith
  have hG' : 0 < 4 * K * η / (η ^ 2 + K) ^ 2 := by positivity
  have hpw : 0 < (p : ℝ) * ϖ ^ (p - 1) * (2 * y₁ / (η + y₁) ^ 2) / 2 := by
    have : (0 : ℝ) < p := by exact_mod_cast hp
    positivity
  have h1 : 0 ≤ deriv (coneStep a b) η * (coneProfile K η - ϖ ^ p / 2) :=
    mul_nonneg hτ' (by linarith)
  have h2 := convex_comb_pos hτ0 hτ1 hpw hG'
  linarith

theorem radial_identity {y₁ r : ℝ} (hy : 0 < y₁) (hr : r < 1) (hr0 : 0 ≤ r) :
    (y₁ * (1 + r) / (1 - r) - y₁) / (y₁ * (1 + r) / (1 - r) + y₁) = r := by
  have h1 : 1 - r ≠ 0 := by linarith
  have h2 : y₁ * (1 + r) / (1 - r) + y₁ ≠ 0 := by
    have : 0 < y₁ * (1 + r) / (1 - r) := by
      apply div_pos (by nlinarith) (by linarith)
    linarith
  rw [div_eq_iff h2]
  field_simp
  ring

theorem coneHeight_gt {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) (hzv : z ≠ v) :
    v.im < coneHeight v z := by
  have hr1 := norm_coneDisc_lt_one hv hz
  have hr0 : 0 < ‖coneDisc v z‖ := norm_pos_iff.2 (coneDisc_ne_zero hv hz hzv)
  rw [coneHeight, lt_div_iff₀ (by linarith)]
  nlinarith

theorem radial_vector_ne {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) (hzv : z ≠ v) :
    (z - v) * (normSq (z - conj v) : ℂ) - (z - conj v) * (normSq (z - v) : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, conj_re, conj_im, sub_im, mul_im, mul_zero,
    sub_zero, zero_re, zero_im, normSq_apply] at hre him
  have hx : z.re = v.re := by
    have : (z.re - v.re) * (4 * z.im * v.im) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · nlinarith [mul_pos hz hv]
  rw [hx] at him
  have hy : z.im = v.im := by
    have : (z.im - v.im) * (z.im + v.im) * (2 * v.im) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · linarith
      · linarith
    · linarith
  exact hzv (Complex.ext hx hy)

namespace ConeShape

variable (σ : ConeShape)

def coneLambda (φa φb : ℝ) (z : ℂ) : ℝ := coneStep φa φb (discAngle (σ.discOne z))

def angleConeBlend (φa φb : ℝ) (z : ℂ) : ℝ :=
  (1 - σ.coneLambda φa φb z) * σ.angleOneCone z + σ.coneLambda φa φb z * σ.angleTwoCone z

def angleCone (p : ℕ) (a b φa φb : ℝ) (z : ℂ) : ℝ :=
  (1 - coneStep a b (σ.etaOne z)) * (Real.pi - p * discAngle (σ.discOne z)) +
    coneStep a b (σ.etaOne z) * σ.angleConeBlend φa φb z

def cornerCone (p : ℕ) (a b φa φb : ℝ) (z : ℂ) : ℂ :=
  -(3 / 2 : ℂ) + ((coneRadial p a b σ.vertexOne.im σ.constK (σ.etaOne z) : ℝ) : ℂ) *
    exp ((σ.angleCone p a b φa φb z : ℂ) * I)

theorem contDiffAt_discAngle {z : ℂ} (hz : z ∈ σ.domOne) :
    ContDiffAt ℝ ∞ (fun u => discAngle (σ.discOne u)) z :=
  contDiffAt_halfArg_comp (σ.contDiffAt_norm_discOne hz) (σ.contDiffAt_re_discOne hz.1)
    (σ.contDiffAt_im_discOne hz.1) hz.2

theorem contDiffAt_angleOneCone {z : ℂ} (hz : z ∈ σ.domOne) :
    ContDiffAt ℝ ∞ σ.angleOneCone z := by
  have hb := σ.contDiffAt_bridgeOne hz
  have hG : ContDiffAt ℝ ∞ (fun u => coneProfile σ.constK (σ.etaOne u)) z :=
    (contDiff_coneProfile σ.constK_pos).contDiffAt.comp z (σ.contDiffAt_etaOne hz)
  have hp := σ.bridgeOne_cone_pos hz
  rw [sub_neg_eq_add] at hp
  exact contDiffAt_negHalfArg_comp hG ((reCLM.contDiff.contDiffAt.comp z hb).add contDiffAt_const)
    (imCLM.contDiff.contDiffAt.comp z hb) hp

theorem contDiffAt_angleTwoCone (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.domTwo) :
    ContDiffAt ℝ ∞ σ.angleTwoCone z := by
  have hb := σ.contDiffAt_bridgeTwo hz
  have hG : ContDiffAt ℝ ∞ (fun u => coneProfile σ.constK (σ.etaOne u)) z :=
    (contDiff_coneProfile σ.constK_pos).contDiffAt.comp z (σ.contDiffAt_etaOne_of_domTwo hz)
  have hp := σ.bridgeTwo_cone_pos hθ hz
  rw [sub_neg_eq_add] at hp
  exact contDiffAt_halfArg_comp hG ((reCLM.contDiff.contDiffAt.comp z hb).add contDiffAt_const)
    (imCLM.contDiff.contDiffAt.comp z hb) hp

theorem contDiffAt_angleCone (hθ : σ.θ₂ = 0) (p : ℕ) (a b φa φb : ℝ) {z : ℂ}
    (hz1 : z ∈ σ.domOne) (hz2 : z ∈ σ.domTwo) :
    ContDiffAt ℝ ∞ (σ.angleCone p a b φa φb) z := by
  have hτ : ContDiffAt ℝ ∞ (fun u => coneStep a b (σ.etaOne u)) z :=
    (contDiff_coneStep a b).contDiffAt.comp z (σ.contDiffAt_etaOne hz1)
  have hφ := σ.contDiffAt_discAngle hz1
  have hl : ContDiffAt ℝ ∞ (σ.coneLambda φa φb) z :=
    (contDiff_coneStep φa φb).contDiffAt.comp z hφ
  have hB : ContDiffAt ℝ ∞ (σ.angleConeBlend φa φb) z :=
    ((contDiffAt_const.sub hl).mul (σ.contDiffAt_angleOneCone hz1)).add
      (hl.mul (σ.contDiffAt_angleTwoCone hθ hz2))
  exact ((contDiffAt_const.sub hτ).mul (contDiffAt_const.sub (contDiffAt_const.mul hφ))).add
    (hτ.mul hB)

theorem cornerCone_eq_apex {p : ℕ} (hp : 1 ≤ p) {a b φa φb : ℝ} (hab : a < b) {z : ℂ}
    (hz : 0 < z.im) (hpos : z = σ.vertexOne ∨ z ∈ σ.domOne) (hη : σ.etaOne z ≤ a) :
    σ.cornerCone p a b φa φb z = -(3 / 2) - conj (σ.discOne z) ^ p / 2 := by
  have hv := σ.vertexOne_im_pos
  have hr1 := norm_coneDisc_lt_one hv hz
  have hϖ : (σ.etaOne z - σ.vertexOne.im) / (σ.etaOne z + σ.vertexOne.im) = ‖σ.discOne z‖ :=
    radial_identity hv hr1 (norm_nonneg _)
  rw [cornerCone, angleCone, coneRadial, coneStep_eq_zero hab hη, hϖ]
  simp only [sub_zero, one_mul, zero_mul, add_zero]
  rcases hpos with h | h
  · subst h
    have h0 : σ.discOne σ.vertexOne = 0 := coneDisc_self _
    rw [h0, norm_zero, zero_pow (by omega), map_zero, zero_pow (by omega)]
    simp
  · have hp' := halfArg_polar_self (σ.discOne_ne_zero h) h.2
    conv_rhs => rw [hp']
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, mul_pow, ← Complex.exp_nat_mul]
    have e : conj ((discAngle (σ.discOne z) : ℂ) * I) = -((discAngle (σ.discOne z) : ℂ) * I) := by
      simp
    rw [e]
    have e2 : ((Real.pi - (p : ℝ) * discAngle (σ.discOne z) : ℝ) : ℂ) * I =
        (Real.pi : ℂ) * I + (p : ℂ) * -((discAngle (σ.discOne z) : ℂ) * I) := by
      push_cast
      ring
    rw [e2, Complex.exp_add, Complex.exp_pi_mul_I]
    push_cast
    ring

theorem cornerCone_eq_bridgeOne (p : ℕ) {a b φa φb : ℝ} (hab : a < b) (hφ : φa < φb) {z : ℂ}
    (hz : z ∈ σ.domOne) (hη : b ≤ σ.etaOne z) (hl : discAngle (σ.discOne z) ≤ φa) :
    σ.cornerCone p a b φa φb z = σ.bridgeOne z := by
  have hK := σ.constK_pos
  have hG : 0 < coneProfile σ.constK (σ.etaOne z) := by
    have := half_le_coneProfile hK (σ.etaOne z); linarith
  have hsq : ((σ.bridgeOne z).re + 3 / 2) ^ 2 + (σ.bridgeOne z).im ^ 2 =
      coneProfile σ.constK (σ.etaOne z) ^ 2 := by
    have := sq_add_sq_eq_of_norm (σ.norm_bridgeOne_add hz)
    simpa using this
  have hpos := σ.bridgeOne_cone_pos hz
  rw [sub_neg_eq_add] at hpos
  have hp := negHalfArg_polar hG hpos hsq
  rw [cornerCone, angleCone, angleConeBlend, coneLambda, coneRadial, coneStep_eq_one hab hη,
    coneStep_eq_zero hφ hl]
  simp only [sub_self, zero_mul, one_mul, zero_add, sub_zero, add_zero, zero_div]
  rw [angleOneCone, ← hp]
  apply Complex.ext <;> simp

theorem cornerCone_eq_bridgeTwo (hθ : σ.θ₂ = 0) (p : ℕ) {a b φa φb : ℝ} (hab : a < b)
    (hφ : φa < φb) {z : ℂ} (hz : z ∈ σ.domTwo) (hη : b ≤ σ.etaOne z)
    (hl : φb ≤ discAngle (σ.discOne z)) :
    σ.cornerCone p a b φa φb z = σ.bridgeTwo z := by
  have hK := σ.constK_pos
  have hG : 0 < coneProfile σ.constK (σ.etaOne z) := by
    have := half_le_coneProfile hK (σ.etaOne z); linarith
  have hsq : ((σ.bridgeTwo z).re + 3 / 2) ^ 2 + (σ.bridgeTwo z).im ^ 2 =
      coneProfile σ.constK (σ.etaOne z) ^ 2 := by
    have := sq_add_sq_eq_of_norm (σ.norm_bridgeTwo_add hθ hz)
    simpa using this
  have hpos := σ.bridgeTwo_cone_pos hθ hz
  rw [sub_neg_eq_add] at hpos
  have hp := halfArg_polar hG hpos hsq
  rw [cornerCone, angleCone, angleConeBlend, coneLambda, coneRadial, coneStep_eq_one hab hη,
    coneStep_eq_one hφ hl]
  simp only [sub_self, zero_mul, one_mul, zero_add, zero_div]
  rw [angleTwoCone, ← hp]
  apply Complex.ext <;> simp

theorem hasDerivAt_discAngle_circle {z : ℂ} (hz : z ∈ σ.domOne) :
    HasDerivAt (fun t : ℝ =>
      discAngle (σ.discOne (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t))) 1 0 := by
  have hv := σ.vertexOne_im_pos
  have hω := norm_coneDisc_lt_one hv hz.1
  have hm : discAngle (σ.discOne z) ∈ Set.Ioo (-Real.pi) Real.pi := halfArg_mem _ _ _
  have hc : ContinuousAt (fun t : ℝ => discAngle (σ.discOne z) + t) 0 :=
    (continuous_const.add continuous_id).continuousAt
  have h1 : ∀ᶠ t : ℝ in 𝓝 0, -Real.pi < discAngle (σ.discOne z) + t :=
    hc.eventually (lt_mem_nhds (by simpa using hm.1))
  have h2 : ∀ᶠ t : ℝ in 𝓝 0, discAngle (σ.discOne z) + t < Real.pi :=
    hc.eventually (gt_mem_nhds (by simpa using hm.2))
  have hev : ∀ᶠ t : ℝ in 𝓝 0, discAngle (σ.discOne z) + t =
      discAngle (σ.discOne (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t)) := by
    filter_upwards [h1, h2] with t ht1 ht2
    simp only [discOne]
    rw [coneDisc_circleCurve hv hω t]
    exact (discAngle_mul_exp (σ.discOne_ne_zero hz) hz.2 ht1 ht2).symm
  have hlin : HasDerivAt (fun t : ℝ => discAngle (σ.discOne z) + t) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).const_add (discAngle (σ.discOne z))
  exact hlin.congr_of_eventuallyEq (hev.mono fun t ht => ht.symm)

theorem exists_hasDerivAt_angleCone (hθ : σ.θ₂ = 0) {p : ℕ} (hp : 1 ≤ p) (a b : ℝ)
    {φa φb : ℝ} (hφ : φa < φb) {z : ℂ} (hz1 : z ∈ σ.domOne) (hz2 : z ∈ σ.domTwo)
    (hord : σ.angleTwoCone z ≤ σ.angleOneCone z) :
    ∃ D : ℝ, D < 0 ∧ HasDerivAt (fun t : ℝ =>
      σ.angleCone p a b φa φb (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t)) D 0 := by
  have hv := σ.vertexOne_im_pos
  have h0 : circleCurve σ.vertexOne (coneDisc σ.vertexOne z) 0 = z := circleCurve_zero hv hz1.1
  obtain ⟨d₁, hd₁, h₁⟩ := σ.exists_hasDerivAt_angleOneCone hz1
  obtain ⟨d₂, hd₂, h₂⟩ := σ.exists_hasDerivAt_angleTwoCone hθ hz2
  have hφd := σ.hasDerivAt_discAngle_circle hz1
  set τ₀ := coneStep a b (σ.etaOne z) with hτ₀
  have hlam := (hasDerivAt_coneStep φa φb (discAngle (σ.discOne
    (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) 0)))).comp (0 : ℝ) hφd
  have h := ((hasDerivAt_const (0 : ℝ) (1 - τ₀)).mul ((hasDerivAt_const (0 : ℝ) Real.pi).sub
    (hφd.const_mul (p : ℝ)))).add ((hasDerivAt_const (0 : ℝ) τ₀).mul
      ((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hlam).mul h₁).add (hlam.mul h₂)))
  have e : (fun t : ℝ =>
      σ.angleCone p a b φa φb (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t)) =
      ((fun _ => 1 - τ₀) * ((fun _ => Real.pi) - fun t => (p : ℝ) *
        discAngle (σ.discOne (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t)))) +
      (fun _ => τ₀) * ((((fun _ => (1 : ℝ)) - coneStep φa φb ∘ fun t =>
        discAngle (σ.discOne (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t))) *
          fun t => σ.angleOneCone (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t)) +
        (coneStep φa φb ∘ fun t =>
          discAngle (σ.discOne (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t))) *
          fun t => σ.angleTwoCone (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t)) := by
    funext t
    simp only [angleCone, angleConeBlend, coneLambda, σ.etaOne_circleCurve hz1.1 t, Pi.add_apply,
      Pi.mul_apply, Pi.sub_apply, Function.comp_apply, hτ₀]
  rw [e]
  refine ⟨_, ?_, h⟩
  simp only [h0, Function.comp_apply, Pi.sub_apply, mul_one, zero_sub]
  have hτ0 : 0 ≤ τ₀ := coneStep_nonneg a b (σ.etaOne z)
  have hτ1 : τ₀ ≤ 1 := coneStep_le_one a b (σ.etaOne z)
  have hl0 := coneStep_nonneg φa φb (discAngle (σ.discOne z))
  have hl1 := coneStep_le_one φa φb (discAngle (σ.discOne z))
  have hl' := deriv_coneStep_nonneg hφ (discAngle (σ.discOne z))
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hbr : (1 - coneStep φa φb (discAngle (σ.discOne z))) * d₁ +
      coneStep φa φb (discAngle (σ.discOne z)) * d₂ < 0 := by
    have := convex_comb_pos hl0 hl1 (neg_pos.2 hd₁) (neg_pos.2 hd₂)
    linarith
  have hlo : deriv (coneStep φa φb) (discAngle (σ.discOne z)) *
      (σ.angleTwoCone z - σ.angleOneCone z) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hl' (by linarith)
  have key : τ₀ * ((1 - coneStep φa φb (discAngle (σ.discOne z))) * d₁ +
      coneStep φa φb (discAngle (σ.discOne z)) * d₂ +
      deriv (coneStep φa φb) (discAngle (σ.discOne z)) * (σ.angleTwoCone z - σ.angleOneCone z)) +
      (1 - τ₀) * -(p : ℝ) < 0 := by
    rcases eq_or_lt_of_le hτ0 with h' | h'
    · rw [← h']
      linarith
    · have : τ₀ * ((1 - coneStep φa φb (discAngle (σ.discOne z))) * d₁ +
          coneStep φa φb (discAngle (σ.discOne z)) * d₂ + deriv (coneStep φa φb)
            (discAngle (σ.discOne z)) * (σ.angleTwoCone z - σ.angleOneCone z)) < 0 :=
        mul_neg_of_pos_of_neg h' (by linarith)
      have : (1 - τ₀) * -(p : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      linarith
  linarith [key]

theorem det_fderiv_cornerCone_ne_zero (hθ : σ.θ₂ = 0) {p : ℕ} (hp : 1 ≤ p) {a b φa φb : ℝ}
    (hab : a < b) (hφ : φa < φb) {z : ℂ} (hz1 : z ∈ σ.domOne) (hz2 : z ∈ σ.domTwo)
    (hord : σ.angleTwoCone z ≤ σ.angleOneCone z) :
    (fderiv ℝ (σ.cornerCone p a b φa φb) z).det ≠ 0 := by
  have hK := σ.constK_pos
  have hv := σ.vertexOne_im_pos
  have hzv := σ.vertexOne_ne_of_domOne hz1
  have hηgt := coneHeight_gt hv hz1.1 hzv
  obtain ⟨S', hS', hSd⟩ := exists_hasDerivAt_coneRadial hp hab hv hK hηgt
  obtain ⟨D, hD, hDd⟩ := σ.exists_hasDerivAt_angleCone hθ hp a b hφ hz1 hz2 hord
  have hρd : DifferentiableAt ℝ σ.etaOne z := (σ.contDiffAt_etaOne hz1).differentiableAt (by simp)
  have hΘd := (σ.contDiffAt_angleCone hθ p a b φa φb hz1 hz2).differentiableAt (by simp)
  have hγ := σ.hasDerivAt_circle_velocity hz1.1
  have h0 : circleCurve σ.vertexOne (coneDisc σ.vertexOne z) 0 = z := circleCurve_zero hv hz1.1
  have hργ : ∀ᶠ t : ℝ in 𝓝 0,
      σ.etaOne (circleCurve σ.vertexOne (coneDisc σ.vertexOne z) t) = σ.etaOne z :=
    Eventually.of_forall fun t => σ.etaOne_circleCurve hz1.1 t
  set Wv := (z - σ.vertexOne) * (normSq (z - conj σ.vertexOne) : ℂ) -
    (z - conj σ.vertexOne) * (normSq (z - σ.vertexOne) : ℂ) with hWv
  have hWne : Wv ≠ 0 := radial_vector_ne hv hz1.1 hzv
  have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ) * Wv) Wv 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Wv).const_add z
  have hρN0 := hasDerivAt_coneHeight_curve hv hl (by simpa using hz1.1) (by simpa using hzv)
  simp only [ofReal_zero, zero_mul, add_zero] at hρN0
  have hN := normSq_sub_conj_pos hv hz1.1
  have hr1 := norm_coneDisc_lt_one hv hz1.1
  have hr0 : 0 < ‖coneDisc σ.vertexOne z‖ := norm_pos_iff.2 (coneDisc_ne_zero hv hz1.1 hzv)
  have hbracket : 2 * ((z - σ.vertexOne).re * Wv.re + (z - σ.vertexOne).im * Wv.im) *
      normSq (z - conj σ.vertexOne) - normSq (z - σ.vertexOne) *
        (2 * ((z - conj σ.vertexOne).re * Wv.re + (z - conj σ.vertexOne).im * Wv.im)) =
      2 * normSq Wv := by
    have e1 : Wv.re = (z - σ.vertexOne).re * normSq (z - conj σ.vertexOne) -
        (z - conj σ.vertexOne).re * normSq (z - σ.vertexOne) := by
      simp [hWv]
    have e2 : Wv.im = (z - σ.vertexOne).im * normSq (z - conj σ.vertexOne) -
        (z - conj σ.vertexOne).im * normSq (z - σ.vertexOne) := by
      simp [hWv]
    rw [normSq_apply Wv, e1, e2]
    ring
  set bN := σ.vertexOne.im / ((1 - ‖coneDisc σ.vertexOne z‖) ^ 2 * ‖coneDisc σ.vertexOne z‖) *
    ((2 * ((z - σ.vertexOne).re * Wv.re + (z - σ.vertexOne).im * Wv.im) *
      normSq (z - conj σ.vertexOne) - normSq (z - σ.vertexOne) *
        (2 * ((z - conj σ.vertexOne).re * Wv.re + (z - conj σ.vertexOne).im * Wv.im))) /
      normSq (z - conj σ.vertexOne) ^ 2) with hbN
  have hbpos : 0 < bN := by
    rw [hbN, hbracket]
    have : 0 < normSq Wv := normSq_pos.2 hWne
    have : 0 < 1 - ‖coneDisc σ.vertexOne z‖ := by linarith
    positivity
  have hρN : HasDerivAt (fun t : ℝ => σ.etaOne (z + t * Wv)) bN 0 := hρN0
  have hΘN : HasDerivAt (fun t : ℝ => σ.angleCone p a b φa φb (z + t * Wv))
      (fderiv ℝ (σ.angleCone p a b φa φb) z Wv) 0 := by
    have hF' : HasFDerivAt (σ.angleCone p a b φa φb) (fderiv ℝ (σ.angleCone p a b φa φb) z)
        (z + ((0 : ℝ) : ℂ) * Wv) := by
      rw [ofReal_zero, zero_mul, add_zero]
      exact hΘd.hasFDerivAt
    exact hF'.comp_hasDerivAt 0 hl
  have hdet := det_fderiv_polar (c := -(3 / 2 : ℂ))
    (S := coneRadial p a b σ.vertexOne.im σ.constK) (ρ := σ.etaOne)
    (Θ := σ.angleCone p a b φa φb) hSd hρd hΘd hγ h0 hργ hDd hρN hΘN
  have hfun : (fun u => -(3 / 2 : ℂ) + ((coneRadial p a b σ.vertexOne.im σ.constK
      (σ.etaOne u) : ℝ) : ℂ) * exp ((σ.angleCone p a b φa φb u : ℂ) * I)) =
      σ.cornerCone p a b φa φb := rfl
  rw [hfun] at hdet
  intro h0'
  rw [h0', zero_mul] at hdet
  have hS0 : 0 < coneRadial p a b σ.vertexOne.im σ.constK (σ.etaOne z) := by
    have hτ0 := coneStep_nonneg a b (σ.etaOne z)
    have hτ1 := coneStep_le_one a b (σ.etaOne z)
    have hη' : σ.vertexOne.im < σ.etaOne z := hηgt
    have hϖ : 0 < (σ.etaOne z - σ.vertexOne.im) / (σ.etaOne z + σ.vertexOne.im) :=
      div_pos (by linarith) (by linarith)
    have hG : 0 < coneProfile σ.constK (σ.etaOne z) := by
      have := half_le_coneProfile hK (σ.etaOne z); linarith
    have := convex_comb_pos hτ0 hτ1 (by positivity : 0 <
      ((σ.etaOne z - σ.vertexOne.im) / (σ.etaOne z + σ.vertexOne.im)) ^ p / 2) hG
    simpa [coneRadial, mul_div_assoc] using this
  have : coneRadial p a b σ.vertexOne.im σ.constK (σ.etaOne z) * S' * D * bN < 0 := by
    have h1 : 0 < coneRadial p a b σ.vertexOne.im σ.constK (σ.etaOne z) * S' := by positivity
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h1 hD) hbpos
  linarith

theorem angleTwoCone_le_angleOneCone (hθ : σ.θ₂ = 0) {z : ℂ} (hz1 : z ∈ σ.domOne)
    (hz2 : z ∈ σ.domTwo) (hw1 : 0 ≤ σ.wallOne z) (hw2 : 0 ≤ σ.wallTwo z) :
    σ.angleTwoCone z ≤ σ.angleOneCone z := by
  have hK := σ.constK_pos
  set G := coneProfile σ.constK (σ.etaOne z)
  have hG : 0 < G := by have := half_le_coneProfile hK (σ.etaOne z); linarith
  have h1 : ((σ.bridgeOne z).re + 3 / 2) ^ 2 + (σ.bridgeOne z).im ^ 2 = G ^ 2 := by
    have := sq_add_sq_eq_of_norm (σ.norm_bridgeOne_add hz1)
    simpa using this
  have h2 : ((σ.bridgeTwo z).re + 3 / 2) ^ 2 + (σ.bridgeTwo z).im ^ 2 = G ^ 2 := by
    have := sq_add_sq_eq_of_norm (σ.norm_bridgeTwo_add hθ hz2)
    simpa using this
  have hp1 := σ.bridgeOne_cone_pos hz1
  rw [sub_neg_eq_add] at hp1
  have hp2 := σ.bridgeTwo_cone_pos hθ hz2
  rw [sub_neg_eq_add] at hp2
  have hI1 : 0 ≤ (σ.bridgeOne z).im := by
    rcases eq_or_lt_of_le hw1 with h | h
    · have : (σ.bridgeOne z).im = 0 := by
        simp [bridgeOne, outerBridge, ← h]
      rw [this]
    · exact (σ.bridgeOne_im_pos hz1 h).le
  have hI2 : 0 ≤ (σ.bridgeTwo z).im := by
    rcases eq_or_lt_of_le hw2 with h | h
    · have : (σ.bridgeTwo z).im = 0 := by
        simp [bridgeTwo, innerBridge, ← h]
      rw [this]
    · exact (innerBridge_im_pos σ.constK_pos (cuspZeroHeight_pos hz2.1) (σ.etaOne_pos hz2.1)
        (σ.cofTwo_pos hz2) h).le
  have hΘ1 : 0 ≤ σ.angleOneCone z := le_of_lt negHalfArg_mem.1
  have hΘ2π : σ.angleTwoCone z ≤ Real.pi := by
    unfold angleTwoCone halfArg
    have := Real.arctan_lt_pi_div_two ((σ.bridgeTwo z).im /
      (coneProfile σ.constK (σ.etaOne z) + ((σ.bridgeTwo z).re + 3 / 2)))
    linarith
  have hΘ1π : σ.angleOneCone z ≤ Real.pi := by
    unfold angleOneCone negHalfArg
    have := Real.arctan_nonneg.2 (div_nonneg hI1 hp1.le)
    linarith
  have hc1 := negHalfArg_cos hG hp1 h1
  have hc2 := halfArg_cos hG hp2 h2
  have hR : (σ.bridgeOne z).re < (σ.bridgeTwo z).re := by
    have n1 := sq_add_sq_eq_of_norm (σ.norm_bridgeOne hz1)
    have n2 : (σ.bridgeTwo z).re ^ 2 + (σ.bridgeTwo z).im ^ 2 < 4 := by
      have := sq_add_sq_eq_of_norm (u := σ.bridgeTwo z) rfl
      have := σ.norm_bridgeTwo_lt_two hθ hz2
      nlinarith [norm_nonneg (σ.bridgeTwo z)]
    have hR2 : 2 < 3 / 2 + coneProfile σ.constK z.im := by
      have := half_lt_coneProfile hK hz1.1.ne'
      linarith
    nlinarith
  by_contra hc
  have hlt : σ.angleOneCone z < σ.angleTwoCone z := not_le.1 hc
  have := Real.cos_le_cos_of_nonneg_of_le_pi hΘ1 hΘ2π hlt.le
  rw [angleOneCone, angleTwoCone, hc1, hc2] at this
  have : (σ.bridgeTwo z).re + 3 / 2 ≤ (σ.bridgeOne z).re + 3 / 2 := by
    rwa [div_le_div_iff_of_pos_right hG] at this
  linarith

end ConeShape

end GC.Seifert

import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypAngles
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldConeCorner
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldCornerInf

/-!
# The three corners of the hyperbolic compact fold

Lane CF-H, tier 2 (design
`docs/geometrization/handoffs/20261004-design-cf-compact-triangle-fold.md`, §4, curvature `-1`).
All three corners are polar maps `c + S(ϖ) e^{iΘ}` about the image of their vertex, with a radial
profile depending only on the pseudo-hyperbolic distance `ϖ = ‖mob vⱼ z‖` to the vertex and an
angle blending the apex angle with the bridge angles of `CompactFoldHypAngles`:
* at `v₁` (about `+3/2`): `S = hypInnerRadial p₁ a b τ₁ ϖ₁`, the blend of the apex modulus
  `ϖ^{p}/2` with `modOne = 3/2 + κ canonForm τ₁ ϖ₁`, and `Θ = (1 - τ) p₁ ψ₁ +
  τ (s angleOneAtOne + (1 - s) angleTwoAtOne)`, `ψ₁ = discAngle rotOne`, with the lens switch
  `s = coneStep β β' lensCoord`, where `lensCoord = 2 Im rotTwo/(1 - |rotTwo|²)` is the hyperbolic
  sine of the signed distance to the geodesic of wall 2 (`lensForm_mob`: it is invariant under
  the translations along that geodesic, so it is the same function in the coordinate at `v₁`);
* at `v₂` (about `-3/2`): the mirror, with `angleTwoAtTwo` (weight `1 - s`), `angleZeroAtTwo`;
* at `v₃ = 0` (about `0`): `S = hypOuterRadial p₃ a b τ₃ ‖z‖`, decreasing, the blend of the outer
  germ modulus `7/2 - ϖ^{p}/2` with `modThree`, and `Θ = (1 - τ)(π - p₃ ψ₃) +
  τ ((1 - ν) angleZeroAtThree + ν angleOneAtThree)`, `ν = coneStep (-w) w blendThree` with
  `blendThree = w (2ψ₃/θ₃ - 1) + (w/δ)(canon 1 - canon 0)`.
Near the vertex each corner is its apex model (`cornerOne_eq_apexOne`, `cornerTwo_eq_apexTwo`,
`cornerThree_eq_outerGerm`); where the radial weight is `1` and the angular weight `0` or `1` it
is the corresponding bridge (`cornerOne_eq_bridgeOne`, …). The Jacobian is positive off the
vertex (`det_fderiv_cornerOne_pos`, …) by A4's polar formula `det_fderiv_polar` with the
hyperbolic circle `hcirc vⱼ z` and the radial vector `hrad vⱼ z` (velocity `I · hrad`): the
profile is strictly monotone in `ϖ`, the angle strictly monotone along the circle (the bridge
angles are, the lens coordinate and the blend move in the right direction under the stated
sector conditions, and the bridge angles are ordered).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace HypFold

def canonForm (τ ϖ : ℝ) : ℝ := (ϖ - τ) / (1 - ϖ * τ)

def hypInnerRadial (p : ℕ) (a b τ ϖ : ℝ) : ℝ :=
  (1 - coneStep a b ϖ) * ϖ ^ p / 2 +
    coneStep a b ϖ * (3 / 2 + compactProfileSlope * canonForm τ ϖ)

def hypOuterRadial (p : ℕ) (a b τ ϖ : ℝ) : ℝ :=
  (1 - coneStep a b ϖ) * (7 / 2 - ϖ ^ p / 2) +
    coneStep a b ϖ * (3 - compactProfileSlope * canonForm τ ϖ)

theorem abs_canonForm_lt_one {τ ϖ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hϖ0 : 0 ≤ ϖ)
    (hϖ1 : ϖ < 1) : |canonForm τ ϖ| < 1 := by
  have hD : 0 < 1 - ϖ * τ := by nlinarith
  rw [canonForm, abs_lt, lt_div_iff₀ hD, div_lt_one hD]
  constructor <;> nlinarith

theorem hasDerivAt_canonForm' {τ ϖ : ℝ} (hD : 1 - ϖ * τ ≠ 0) :
    HasDerivAt (canonForm τ) ((1 - τ ^ 2) / (1 - ϖ * τ) ^ 2) ϖ := by
  have h := ((hasDerivAt_id' ϖ).sub_const τ).div (((hasDerivAt_id' ϖ).mul_const τ).const_sub 1) hD
  refine h.congr_deriv ?_
  field_simp
  ring

theorem contDiffAt_canonForm {τ ϖ : ℝ} (hD : 1 - ϖ * τ ≠ 0) :
    ContDiffAt ℝ ∞ (canonForm τ) ϖ :=
  (contDiffAt_id.sub contDiffAt_const).div (contDiffAt_const.sub (contDiffAt_id.mul
    contDiffAt_const)) hD

theorem hypInnerRadial_pos {p : ℕ} {a b τ ϖ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hϖ0 : 0 < ϖ)
    (hϖ1 : ϖ < 1) : 0 < hypInnerRadial p a b τ ϖ := by
  have hτ0' := coneStep_nonneg a b ϖ
  have hτ1' := coneStep_le_one a b ϖ
  have hc := abs_lt.1 (abs_canonForm_lt_one hτ0 hτ1 hϖ0.le hϖ1)
  have hR : 0 < 3 / 2 + compactProfileSlope * canonForm τ ϖ := by
    unfold compactProfileSlope
    linarith [hc.1]
  have hp : 0 < ϖ ^ p / 2 := by positivity
  have := convex_comb_pos hτ0' hτ1' hp hR
  unfold hypInnerRadial
  linarith [show (1 - coneStep a b ϖ) * ϖ ^ p / 2 = (1 - coneStep a b ϖ) * (ϖ ^ p / 2) by ring]

theorem exists_hasDerivAt_hypInnerRadial {p : ℕ} (hp : 1 ≤ p) {a b τ ϖ : ℝ} (hab : a < b)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hϖ0 : 0 < ϖ) (hϖ1 : ϖ < 1) :
    ∃ S' : ℝ, 0 < S' ∧ HasDerivAt (hypInnerRadial p a b τ) S' ϖ := by
  have hD : 0 < 1 - ϖ * τ := by nlinarith
  have hτ := hasDerivAt_coneStep a b ϖ
  have hc := hasDerivAt_canonForm' (τ := τ) hD.ne'
  have h := (((hasDerivAt_const ϖ (1 : ℝ)).sub hτ).mul ((hasDerivAt_pow p ϖ).div_const 2)).add
    (hτ.mul ((hasDerivAt_const ϖ (3 / 2 : ℝ)).add (hc.const_mul compactProfileSlope)))
  have h' : HasDerivAt (hypInnerRadial p a b τ)
      (deriv (coneStep a b) ϖ * (3 / 2 + compactProfileSlope * canonForm τ ϖ - ϖ ^ p / 2) +
        ((1 - coneStep a b ϖ) * ((p : ℝ) * ϖ ^ (p - 1) / 2) +
          coneStep a b ϖ * (compactProfileSlope * ((1 - τ ^ 2) / (1 - ϖ * τ) ^ 2)))) ϖ := by
    convert h using 1
    · funext s
      simp only [hypInnerRadial, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
      ring
    · simp only [Pi.sub_apply, Pi.add_apply]
      ring
  refine ⟨_, ?_, h'⟩
  have hτ0' := coneStep_nonneg a b ϖ
  have hτ1' := coneStep_le_one a b ϖ
  have hτ' := deriv_coneStep_nonneg hab ϖ
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hc1 := abs_lt.1 (abs_canonForm_lt_one hτ0 hτ1 hϖ0.le hϖ1)
  have hϖp : ϖ ^ p ≤ 1 := pow_le_one₀ hϖ0.le hϖ1.le
  have h1 : 0 ≤ deriv (coneStep a b) ϖ *
      (3 / 2 + compactProfileSlope * canonForm τ ϖ - ϖ ^ p / 2) := by
    apply mul_nonneg hτ'
    unfold compactProfileSlope
    linarith [hc1.1]
  have h2 : 0 < (p : ℝ) * ϖ ^ (p - 1) / 2 := by positivity
  have h3 : 0 < compactProfileSlope * ((1 - τ ^ 2) / (1 - ϖ * τ) ^ 2) := by
    have : 0 < 1 - τ ^ 2 := by nlinarith
    unfold compactProfileSlope
    positivity
  have := convex_comb_pos hτ0' hτ1' h2 h3
  linarith

theorem hypOuterRadial_pos {p : ℕ} {a b τ ϖ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hϖ0 : 0 ≤ ϖ)
    (hϖ1 : ϖ < 1) : 0 < hypOuterRadial p a b τ ϖ := by
  have hτ0' := coneStep_nonneg a b ϖ
  have hτ1' := coneStep_le_one a b ϖ
  have hc := abs_lt.1 (abs_canonForm_lt_one hτ0 hτ1 hϖ0 hϖ1)
  have hR : 0 < 3 - compactProfileSlope * canonForm τ ϖ := by
    unfold compactProfileSlope
    linarith [hc.2]
  have hϖp : ϖ ^ p ≤ 1 := pow_le_one₀ hϖ0 hϖ1.le
  have := convex_comb_pos hτ0' hτ1' (by linarith : (0 : ℝ) < 7 / 2 - ϖ ^ p / 2) hR
  unfold hypOuterRadial
  linarith

theorem exists_hasDerivAt_hypOuterRadial {p : ℕ} (hp : 1 ≤ p) {a b τ ϖ : ℝ} (hab : a < b)
    (hb : b ≤ 1 / 5) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hϖ0 : 0 < ϖ) (hϖ1 : ϖ < 1) :
    ∃ S' : ℝ, S' < 0 ∧ HasDerivAt (hypOuterRadial p a b τ) S' ϖ := by
  have hD : 0 < 1 - ϖ * τ := by nlinarith
  have hτ := hasDerivAt_coneStep a b ϖ
  have hc := hasDerivAt_canonForm' (τ := τ) hD.ne'
  have h := (((hasDerivAt_const ϖ (1 : ℝ)).sub hτ).mul ((hasDerivAt_const ϖ (7 / 2 : ℝ)).sub
    ((hasDerivAt_pow p ϖ).div_const 2))).add (hτ.mul ((hasDerivAt_const ϖ (3 : ℝ)).sub
      (hc.const_mul compactProfileSlope)))
  have h' : HasDerivAt (hypOuterRadial p a b τ)
      (deriv (coneStep a b) ϖ * ((3 - compactProfileSlope * canonForm τ ϖ) -
        (7 / 2 - ϖ ^ p / 2)) + ((1 - coneStep a b ϖ) * -((p : ℝ) * ϖ ^ (p - 1) / 2) +
          coneStep a b ϖ * -(compactProfileSlope * ((1 - τ ^ 2) / (1 - ϖ * τ) ^ 2)))) ϖ := by
    convert h using 1
    · funext s
      simp only [hypOuterRadial, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    · simp only [Pi.sub_apply]
      ring
  refine ⟨_, ?_, h'⟩
  have hτ0' := coneStep_nonneg a b ϖ
  have hτ1' := coneStep_le_one a b ϖ
  have hτ' := deriv_coneStep_nonneg hab ϖ
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hc1 := abs_lt.1 (abs_canonForm_lt_one hτ0 hτ1 hϖ0.le hϖ1)
  have h1 : deriv (coneStep a b) ϖ * ((3 - compactProfileSlope * canonForm τ ϖ) -
      (7 / 2 - ϖ ^ p / 2)) ≤ 0 := by
    rcases le_or_gt ϖ b with hdb | hdb
    · have hd1 : ϖ ^ p ≤ ϖ := pow_le_of_le_one hϖ0.le (by linarith) (by omega)
      apply mul_nonpos_of_nonneg_of_nonpos hτ'
      unfold compactProfileSlope
      linarith [hc1.1]
    · rw [deriv_coneStep_eq_zero_of_lt hab hdb, zero_mul]
  have h2 : 0 < (p : ℝ) * ϖ ^ (p - 1) / 2 := by positivity
  have h3 : 0 < compactProfileSlope * ((1 - τ ^ 2) / (1 - ϖ * τ) ^ 2) := by
    have : 0 < 1 - τ ^ 2 := by nlinarith
    unfold compactProfileSlope
    positivity
  have := convex_comb_pos hτ0' hτ1' h2 h3
  linarith

theorem contDiffAt_hypInnerRadial (p : ℕ) (a b : ℝ) {τ ϖ : ℝ} (hD : 1 - ϖ * τ ≠ 0) :
    ContDiffAt ℝ ∞ (hypInnerRadial p a b τ) ϖ := by
  unfold hypInnerRadial
  exact (((contDiffAt_const.sub (contDiff_coneStep a b).contDiffAt).mul
    (contDiffAt_id.pow _)).div_const _).add ((contDiff_coneStep a b).contDiffAt.mul
      (contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_canonForm hD))))

theorem contDiffAt_hypOuterRadial (p : ℕ) (a b : ℝ) {τ ϖ : ℝ} (hD : 1 - ϖ * τ ≠ 0) :
    ContDiffAt ℝ ∞ (hypOuterRadial p a b τ) ϖ := by
  unfold hypOuterRadial
  exact ((contDiffAt_const.sub (contDiff_coneStep a b).contDiffAt).mul
    (contDiffAt_const.sub ((contDiffAt_id.pow _).div_const _))).add
      ((contDiff_coneStep a b).contDiffAt.mul
        (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_canonForm hD))))

theorem hasDerivAt_norm_comp {f : ℝ → ℂ} {V : ℂ} (hf : HasDerivAt f V 0) (h0 : f 0 ≠ 0) :
    HasDerivAt (fun t => ‖f t‖) ((conj (f 0) * V).re / ‖f 0‖) 0 := by
  have hn : HasDerivAt (fun t => normSq (f t)) (2 * (conj (f 0) * V).re) 0 := by
    have hr := (reCLM.hasFDerivAt.comp_hasDerivAt 0 hf)
    have hi := (imCLM.hasFDerivAt.comp_hasDerivAt 0 hf)
    have h := (hr.mul hr).add (hi.mul hi)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    · simp only [Function.comp_apply, reCLM_apply, imCLM_apply, mul_re, conj_re, conj_im]
      ring
    · simp [normSq_apply]
  have h0' : normSq (f 0) ≠ 0 := normSq_eq_zero.not.2 h0
  have hs := hn.sqrt h0'
  have e : (fun t => ‖f t‖) = fun t => Real.sqrt (normSq (f t)) := by
    funext t
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [e]
  refine hs.congr_deriv ?_
  rw [Complex.normSq_eq_norm_sq (f 0), Real.sqrt_sq (norm_nonneg _)]
  have : ‖f 0‖ ≠ 0 := norm_ne_zero_iff.2 h0
  field_simp

theorem cross_I_mul (N : ℂ) : N.re * (I * N).im - (I * N).re * N.im = ‖N‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, normSq_apply]
  simp only [mul_im, mul_re, I_re, I_im]
  ring

theorem det_pos_of_polar' {D S S' A b n : ℝ} (hn : 0 < n)
    (h : D * n = S * S' * A * b) (hpos : 0 < S * S' * A * b) : 0 < D :=
  (mul_pos_iff_of_pos_right hn).1 (h ▸ hpos)

theorem hasDerivAt_comp_ray' {Θ : ℂ → ℝ} {z N : ℂ} (hΘ : DifferentiableAt ℝ Θ z) :
    HasDerivAt (fun t : ℝ => Θ (z + t * N)) (fderiv ℝ Θ z N) 0 := by
  have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ) * N) N 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const N).const_add z
  have hF' : HasFDerivAt Θ (fderiv ℝ Θ z) (z + ((0 : ℝ) : ℂ) * N) := by
    rw [ofReal_zero, zero_mul, add_zero]
    exact hΘ.hasFDerivAt
  exact hF'.comp_hasDerivAt 0 hl

theorem hasDerivAt_norm_mob_hrad {v z : ℂ} (hv : ‖v‖ < 1) (hz : ‖z‖ < 1)
    (hne : mob v z ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖mob v (z + t * hrad v z)‖) ‖mob v z‖ 0 := by
  have h := hasDerivAt_norm_comp (hasDerivAt_mob_hrad hv hz) (by simpa using hne)
  simp only [ofReal_zero, zero_mul, add_zero] at h
  refine h.congr_deriv ?_
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ofReal_re]
  have : ‖mob v z‖ ≠ 0 := norm_ne_zero_iff.2 hne
  field_simp

theorem hasDerivAt_discAngle_mul_exp' {w : ℂ} (h : 0 < ‖w‖ + w.re) :
    HasDerivAt (fun t : ℝ => discAngle (w * exp ((t : ℂ) * I))) 1 0 := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at h
  have hm : discAngle w ∈ Set.Ioo (-Real.pi) Real.pi := halfArg_mem _ _ _
  have hc : ContinuousAt (fun t : ℝ => discAngle w + t) 0 :=
    (continuous_const.add continuous_id).continuousAt
  have h1 : ∀ᶠ t : ℝ in 𝓝 0, -Real.pi < discAngle w + t :=
    hc.eventually (lt_mem_nhds (by simpa using hm.1))
  have h2 : ∀ᶠ t : ℝ in 𝓝 0, discAngle w + t < Real.pi :=
    hc.eventually (gt_mem_nhds (by simpa using hm.2))
  have hev : ∀ᶠ t : ℝ in 𝓝 0, discAngle w + t = discAngle (w * exp ((t : ℂ) * I)) := by
    filter_upwards [h1, h2] with t ht1 ht2
    exact (discAngle_mul_exp hw0 h ht1 ht2).symm
  have hlin : HasDerivAt (fun t : ℝ => discAngle w + t) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).const_add (discAngle w)
  exact hlin.congr_of_eventuallyEq (hev.mono fun t ht => ht.symm)

theorem contDiffAt_discAngle_comp' {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ ∞ f z)
    (h : 0 < ‖f z‖ + (f z).re) : ContDiffAt ℝ ∞ (fun u => discAngle (f u)) z := by
  have hw0 : f z ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  exact ConeShape.contDiffAt_halfArg_comp (hf.norm ℝ hw0)
    (reCLM.contDiff.contDiffAt.comp z hf) (imCLM.contDiff.contDiffAt.comp z hf) h

theorem lensForm_mob {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {W : ℂ} (hW : ‖W‖ < 1) :
    2 * (mob (t : ℂ) W).im / (1 - normSq (mob (t : ℂ) W)) = 2 * W.im / (1 - normSq W) := by
  have hne := one_sub_ofReal_mul_ne_zero ht0 ht1 hW
  have hN : 0 < normSq (1 - (t : ℂ) * W) := normSq_pos.2 hne
  have hne' : 1 - conj (t : ℂ) * W ≠ 0 := by rwa [Complex.conj_ofReal]
  have e1 := im_mob_ofReal t W
  have e2 := one_sub_normSq_mob hne'
  rw [Complex.conj_ofReal, normSq_ofReal] at e2
  have hW2 : 0 < 1 - normSq W := by have := normSq_lt_one_of_norm_lt hW; linarith
  have ht2 : 0 < 1 - t * t := by nlinarith
  rw [e2, eq_div_iff hW2.ne', div_mul_eq_mul_div, div_eq_iff (by positivity)]
  rw [show (mob (t : ℂ) W).im = (1 - t ^ 2) * W.im / normSq (1 - (t : ℂ) * W) by
    rw [eq_div_iff hN.ne', e1]]
  field_simp

variable (σ : CompactShape)

def lensCoord (z : ℂ) : ℝ := 2 * (σ.rotTwo z).im / (1 - normSq (σ.rotTwo z))

def lensSwitch (β β' : ℝ) (z : ℂ) : ℝ := coneStep β β' (lensCoord σ z)

def psiOne (z : ℂ) : ℝ := discAngle (σ.rotOne z)

def psiTwo (z : ℂ) : ℝ := discAngle (σ.rotTwo z)

def angleCornerOne (a b β β' : ℝ) (z : ℂ) : ℝ :=
  (1 - coneStep a b (hd σ 0 z)) * (σ.p₁ * psiOne σ z) +
    coneStep a b (hd σ 0 z) * (lensSwitch σ β β' z * angleOneAtOne σ z +
      (1 - lensSwitch σ β β' z) * angleTwoAtOne σ z)

def cornerOne (a b β β' : ℝ) (z : ℂ) : ℂ :=
  ((3 / 2 : ℝ) : ℂ) + (hypInnerRadial σ.p₁ a b (tauOne σ) (hd σ 0 z) : ℂ) *
    exp ((angleCornerOne σ a b β β' z : ℂ) * I)

def angleCornerTwo (a b β β' : ℝ) (z : ℂ) : ℝ :=
  (1 - coneStep a b (hd σ 1 z)) * (σ.p₂ * psiTwo σ z) +
    coneStep a b (hd σ 1 z) * ((1 - lensSwitch σ β β' z) * angleTwoAtTwo σ z +
      lensSwitch σ β β' z * angleZeroAtTwo σ z)

def cornerTwo (a b β β' : ℝ) (z : ℂ) : ℂ :=
  ((-(3 / 2) : ℝ) : ℂ) + (hypInnerRadial σ.p₂ a b (tauTwo σ) (hd σ 1 z) : ℂ) *
    exp ((angleCornerTwo σ a b β β' z : ℂ) * I)

def blendThree (w δ : ℝ) (z : ℂ) : ℝ :=
  w * (2 * discAngle z / σ.θ₃ - 1) + w / δ * (canon σ 1 z - canon σ 0 z)

def nuThree (w δ : ℝ) (z : ℂ) : ℝ := coneStep (-w) w (blendThree σ w δ z)

def angleCornerThree (a b w δ : ℝ) (z : ℂ) : ℝ :=
  (1 - coneStep a b ‖z‖) * (Real.pi - σ.p₃ * discAngle z) +
    coneStep a b ‖z‖ * ((1 - nuThree σ w δ z) * angleZeroAtThree σ z +
      nuThree σ w δ z * angleOneAtThree σ z)

def cornerThree (a b w δ : ℝ) (z : ℂ) : ℂ :=
  ((0 : ℝ) : ℂ) + (hypOuterRadial σ.p₃ a b (tauThree σ) ‖z‖ : ℂ) *
    exp ((angleCornerThree σ a b w δ z : ℂ) * I)

variable {σ}

section Hyp

variable (h : σ.curv = .hyperbolic)
include h

theorem contDiffAt_rotOne {z : ℂ} (hz : ‖z‖ < 1) : ContDiffAt ℝ ∞ σ.rotOne z := by
  have e : σ.rotOne = fun u => -exp (-((σ.θ₃ : ℂ) * I)) * mob σ.vertexOne u :=
    funext (rotOne_eq_mul_mob h)
  rw [e]
  exact contDiffAt_const.mul (contDiffAt_mob (one_sub_conj_mul_ne_zero
    (norm_vertexOne_lt_one h) hz))

theorem normSq_rotTwo_lt_one {z : ℂ} (hz : ‖z‖ < 1) : normSq (σ.rotTwo z) < 1 :=
  normSq_lt_one_of_norm_lt (norm_rotTwo_lt_one h hz)

theorem normSq_rotOne_lt_one {z : ℂ} (hz : ‖z‖ < 1) : normSq (σ.rotOne z) < 1 :=
  normSq_lt_one_of_norm_lt (norm_rotOne_lt_one h hz)

theorem lensCoord_eq_rotOne {z : ℂ} (hz : ‖z‖ < 1) :
    lensCoord σ z = -(2 * (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im /
      (1 - normSq (σ.rotOne z))) := by
  have e := exp_neg_mul_rotOne h hz
  have hn : normSq (σ.rotOne z) = normSq (mob (sideOneTwo σ : ℂ) (σ.rotTwo z)) := by
    rw [← normSq_neg (mob _ _), ← e, map_mul, Complex.normSq_eq_norm_sq (exp _),
      show -((σ.θ₁ : ℂ) * I) = ((-σ.θ₁ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
    ring
  rw [lensCoord, hn, e, neg_im, ← lensForm_mob (sideOneTwo_pos h) (sideOneTwo_lt_one h)
    (norm_rotTwo_lt_one h hz)]
  ring

theorem contDiffAt_lensCoord {z : ℂ} (hz : ‖z‖ < 1) : ContDiffAt ℝ ∞ (lensCoord σ) z := by
  have hr := contDiffAt_rotTwo h hz
  have hd : 1 - normSq (σ.rotTwo z) ≠ 0 := by linarith [normSq_rotTwo_lt_one h hz]
  exact (contDiffAt_const.mul (imCLM.contDiff.contDiffAt.comp z hr)).div
    (contDiffAt_const.sub (contDiffAt_normSq_comp hr)) hd

theorem hasDerivAt_lensCoord_hcircOne {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun t => lensCoord σ (hcirc σ.vertexOne z t))
      (-(2 * (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).re / (1 - normSq (σ.rotOne z)))) 0 := by
  have hv1 := norm_vertexOne_lt_one h
  have e : (fun t => lensCoord σ (hcirc σ.vertexOne z t)) = fun t : ℝ =>
      -(2 * (exp (-((σ.θ₁ : ℂ) * I)) * (σ.rotOne z * exp ((t : ℂ) * I))).im /
        (1 - normSq (σ.rotOne z))) := by
    funext t
    rw [lensCoord_eq_rotOne h (norm_hcirc_lt_one hv1 hz t), rotOne_hcirc h hz, map_mul,
      Complex.normSq_eq_norm_sq (exp _), Complex.norm_exp_ofReal_mul_I]
    ring
  rw [e]
  exact (((hasDerivAt_im_rot_circle _ _).const_mul 2).div_const _).neg

theorem hasDerivAt_lensCoord_hcircTwo {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (fun t => lensCoord σ (hcirc σ.vertexTwo z t))
      (2 * (σ.rotTwo z).re / (1 - normSq (σ.rotTwo z))) 0 := by
  have e : (fun t => lensCoord σ (hcirc σ.vertexTwo z t)) = fun t : ℝ =>
      2 * ((1 : ℂ) * (σ.rotTwo z * exp ((t : ℂ) * I))).im / (1 - normSq (σ.rotTwo z)) := by
    funext t
    rw [lensCoord, rotTwo_hcirc h hz, one_mul, map_mul, Complex.normSq_eq_norm_sq (exp _),
      Complex.norm_exp_ofReal_mul_I]
    ring
  rw [e]
  have := ((hasDerivAt_im_rot_circle 1 (σ.rotTwo z)).const_mul 2).div_const
    (1 - normSq (σ.rotTwo z))
  rwa [one_mul] at this

theorem hasDerivAt_psiOne_hcirc {z : ℂ} (hz : ‖z‖ < 1)
    (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re) :
    HasDerivAt (fun t => psiOne σ (hcirc σ.vertexOne z t)) 1 0 := by
  have e : (fun t => psiOne σ (hcirc σ.vertexOne z t)) =
      fun t : ℝ => discAngle (σ.rotOne z * exp ((t : ℂ) * I)) := by
    funext t
    rw [psiOne, rotOne_hcirc h hz]
  rw [e]
  exact hasDerivAt_discAngle_mul_exp' hψ

theorem hasDerivAt_psiTwo_hcirc {z : ℂ} (hz : ‖z‖ < 1)
    (hψ : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re) :
    HasDerivAt (fun t => psiTwo σ (hcirc σ.vertexTwo z t)) 1 0 := by
  have e : (fun t => psiTwo σ (hcirc σ.vertexTwo z t)) =
      fun t : ℝ => discAngle (σ.rotTwo z * exp ((t : ℂ) * I)) := by
    funext t
    rw [psiTwo, rotTwo_hcirc h hz]
  rw [e]
  exact hasDerivAt_discAngle_mul_exp' hψ

omit h in
theorem hasDerivAt_psiThree_hcirc {z : ℂ} (hψ : 0 < ‖z‖ + z.re) :
    HasDerivAt (fun t => discAngle (hcirc 0 z t)) 1 0 := by
  have e : (fun t => discAngle (hcirc 0 z t)) =
      fun t : ℝ => discAngle (z * exp ((t : ℂ) * I)) := by
    funext t
    rw [hcirc_zero_left]
  rw [e]
  exact hasDerivAt_discAngle_mul_exp' hψ

theorem contDiffAt_psiOne {z : ℂ} (hz : ‖z‖ < 1) (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re) :
    ContDiffAt ℝ ∞ (psiOne σ) z :=
  contDiffAt_discAngle_comp' (contDiffAt_rotOne h hz) hψ

theorem contDiffAt_psiTwo {z : ℂ} (hz : ‖z‖ < 1) (hψ : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re) :
    ContDiffAt ℝ ∞ (psiTwo σ) z :=
  contDiffAt_discAngle_comp' (contDiffAt_rotTwo h hz) hψ

theorem contDiffAt_modOne {z : ℂ} (hz : ‖z‖ < 1) (hne : hd σ 0 z ≠ 0) :
    ContDiffAt ℝ ∞ (modOne σ) z :=
  contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_canon h 0 hz hne))

theorem contDiffAt_modTwo {z : ℂ} (hz : ‖z‖ < 1) (hne : hd σ 1 z ≠ 0) :
    ContDiffAt ℝ ∞ (modTwo σ) z :=
  contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_canon h 1 hz hne))

theorem contDiffAt_modThree {z : ℂ} (hz : ‖z‖ < 1) (hne : hd σ 2 z ≠ 0) :
    ContDiffAt ℝ ∞ (modThree σ) z :=
  contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_canon h 2 hz hne))

theorem contDiffAt_angleOneAtOne {z : ℂ} (hz : z ∈ domOneThree σ)
    (hpos : 0 < modOne σ z + ((bridgeOne σ z).re - 3 / 2)) :
    ContDiffAt ℝ ∞ (angleOneAtOne σ) z := by
  have hz1 := norm_lt_one_of_domOneThree hz
  have hb := contDiffAt_bridgeOne h hz
  exact ConeShape.contDiffAt_halfArg_comp
    (contDiffAt_modOne h hz1 (hd_ne_zero_of_domOneThree h hz).2)
    ((reCLM.contDiff.contDiffAt.comp z hb).sub contDiffAt_const)
    (imCLM.contDiff.contDiffAt.comp z hb) hpos

theorem contDiffAt_angleTwoAtOne {z : ℂ} (hz : z ∈ domOneTwo σ)
    (hpos : 0 < modOne σ z - ((bridgeTwo σ z).re - 3 / 2)) :
    ContDiffAt ℝ ∞ (angleTwoAtOne σ) z := by
  have hz1 := norm_lt_one_of_domOneTwo hz
  have hb := contDiffAt_bridgeTwo h hz
  exact ConeShape.contDiffAt_negHalfArg_comp
    (contDiffAt_modOne h hz1 (hd_ne_zero_of_domOneTwo h hz).2)
    ((reCLM.contDiff.contDiffAt.comp z hb).sub contDiffAt_const)
    (imCLM.contDiff.contDiffAt.comp z hb) hpos

theorem contDiffAt_angleTwoAtTwo {z : ℂ} (hz : z ∈ domOneTwo σ)
    (hpos : 0 < modTwo σ z + ((bridgeTwo σ z).re + 3 / 2)) :
    ContDiffAt ℝ ∞ (angleTwoAtTwo σ) z := by
  have hz1 := norm_lt_one_of_domOneTwo hz
  have hb := contDiffAt_bridgeTwo h hz
  exact ConeShape.contDiffAt_halfArg_comp
    (contDiffAt_modTwo h hz1 (hd_ne_zero_of_domOneTwo h hz).1)
    ((reCLM.contDiff.contDiffAt.comp z hb).add contDiffAt_const)
    (imCLM.contDiff.contDiffAt.comp z hb) hpos

theorem contDiffAt_angleZeroAtTwo {z : ℂ} (hz : z ∈ domZeroThree σ)
    (hpos : 0 < modTwo σ z - ((bridgeZero σ z).re + 3 / 2)) :
    ContDiffAt ℝ ∞ (angleZeroAtTwo σ) z := by
  have hz1 := norm_lt_one_of_domZeroThree hz
  have hb := contDiffAt_bridgeZero h hz
  exact ConeShape.contDiffAt_negHalfArg_comp
    (contDiffAt_modTwo h hz1 (hd_ne_zero_of_domZeroThree h hz).2)
    ((reCLM.contDiff.contDiffAt.comp z hb).add contDiffAt_const)
    (imCLM.contDiff.contDiffAt.comp z hb) hpos

theorem contDiffAt_angleOneAtThree {z : ℂ} (hz : z ∈ domOneThree σ)
    (hpos : 0 < modThree σ z + (bridgeOne σ z).re) :
    ContDiffAt ℝ ∞ (angleOneAtThree σ) z := by
  have hz1 := norm_lt_one_of_domOneThree hz
  have hb := contDiffAt_bridgeOne h hz
  exact ConeShape.contDiffAt_halfArg_comp
    (contDiffAt_modThree h hz1 (hd_ne_zero_of_domOneThree h hz).1)
    (reCLM.contDiff.contDiffAt.comp z hb) (imCLM.contDiff.contDiffAt.comp z hb) hpos

theorem contDiffAt_angleZeroAtThree {z : ℂ} (hz : z ∈ domZeroThree σ)
    (hpos : 0 < modThree σ z - (bridgeZero σ z).re) :
    ContDiffAt ℝ ∞ (angleZeroAtThree σ) z := by
  have hz1 := norm_lt_one_of_domZeroThree hz
  have hb := contDiffAt_bridgeZero h hz
  exact ConeShape.contDiffAt_negHalfArg_comp
    (contDiffAt_modThree h hz1 (hd_ne_zero_of_domZeroThree h hz).1)
    (reCLM.contDiff.contDiffAt.comp z hb) (imCLM.contDiff.contDiffAt.comp z hb) hpos

omit h in
theorem one_le_p₁ : 1 ≤ σ.p₁ := le_trans (by norm_num) σ.two_le_p₁

omit h in
theorem lensSwitch_deriv_nonpos' {β β' : ℝ} (hβ : β < β') {x y : ℝ}
    (hy : y ≤ 0 ∨ β' < x ∨ x < β) : deriv (coneStep β β') x * y ≤ 0 := by
  rcases hy with hy | hy | hy
  · exact mul_nonpos_of_nonneg_of_nonpos (deriv_coneStep_nonneg hβ x) hy
  · rw [deriv_coneStep_eq_zero_of_lt hβ hy, zero_mul]
  · rw [deriv_coneStep_eq_zero_of_gt hβ hy, zero_mul]

omit h in
theorem lensSwitch_deriv_nonneg' {β β' : ℝ} (hβ : β < β') {x y : ℝ}
    (hy : 0 ≤ y ∨ β' < x ∨ x < β) : 0 ≤ deriv (coneStep β β') x * y := by
  rcases hy with hy | hy | hy
  · exact mul_nonneg (deriv_coneStep_nonneg hβ x) hy
  · rw [deriv_coneStep_eq_zero_of_lt hβ hy, zero_mul]
  · rw [deriv_coneStep_eq_zero_of_gt hβ hy, zero_mul]

theorem hd_hcirc (j : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) (t : ℝ) :
    hd σ j (hcirc (vtx σ j) z t) = hd σ j z := by
  rw [hd_eq, hd_eq, norm_mob_hcirc (norm_vtx_lt_one h j) hz]

theorem contDiffAt_angleCornerOne (a b β β' : ℝ) {z : ℂ} (hz1 : z ∈ domOneThree σ)
    (hz2 : z ∈ domOneTwo σ) (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (hpos1 : 0 < modOne σ z + ((bridgeOne σ z).re - 3 / 2))
    (hpos2 : 0 < modOne σ z - ((bridgeTwo σ z).re - 3 / 2)) :
    ContDiffAt ℝ ∞ (angleCornerOne σ a b β β') z := by
  have hz := norm_lt_one_of_domOneThree hz1
  have hτ : ContDiffAt ℝ ∞ (fun u => coneStep a b (hd σ 0 u)) z :=
    (contDiff_coneStep a b).contDiffAt.comp z
      (contDiffAt_hd h 0 hz (hd_ne_zero_of_domOneThree h hz1).2)
  have hs : ContDiffAt ℝ ∞ (lensSwitch σ β β') z :=
    (contDiff_coneStep β β').contDiffAt.comp z (contDiffAt_lensCoord h hz)
  exact ((contDiffAt_const.sub hτ).mul (contDiffAt_const.mul (contDiffAt_psiOne h hz hψ))).add
    (hτ.mul ((hs.mul (contDiffAt_angleOneAtOne h hz1 hpos1)).add
      ((contDiffAt_const.sub hs).mul (contDiffAt_angleTwoAtOne h hz2 hpos2))))

theorem contDiffAt_cornerOne (a b β β' : ℝ) {z : ℂ} (hz1 : z ∈ domOneThree σ)
    (hz2 : z ∈ domOneTwo σ) (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (hpos1 : 0 < modOne σ z + ((bridgeOne σ z).re - 3 / 2))
    (hpos2 : 0 < modOne σ z - ((bridgeTwo σ z).re - 3 / 2)) :
    ContDiffAt ℝ ∞ (cornerOne σ a b β β') z := by
  have hz := norm_lt_one_of_domOneThree hz1
  have hdc := contDiffAt_hd h 0 hz (hd_ne_zero_of_domOneThree h hz1).2
  have hD : 1 - hd σ 0 z * tauOne σ ≠ 0 := by
    have := hd_lt_one h 0 hz
    have := hd_nonneg (σ := σ) 0 z
    have := tauOne_lt_one (σ := σ)
    nlinarith [tauOne_pos h]
  have hS : ContDiffAt ℝ ∞ (fun u => hypInnerRadial σ.p₁ a b (tauOne σ) (hd σ 0 u)) z :=
    (contDiffAt_hypInnerRadial σ.p₁ a b hD).comp z hdc
  have hΘ := contDiffAt_angleCornerOne h a b β β' hz1 hz2 hψ hpos1 hpos2
  have hof : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := ofRealCLM.contDiff
  exact contDiffAt_const.add ((hof.contDiffAt.comp z hS).mul
    (((hof.contDiffAt.comp z hΘ).mul contDiffAt_const).cexp))

theorem exists_hasDerivAt_angleCornerOne {a b β β' : ℝ} (hβ : β < β') {z : ℂ}
    (hz1 : z ∈ domOneThree σ) (hz2 : z ∈ domOneTwo σ)
    (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (hψ' : 0 < ‖exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z‖ +
      (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).re)
    (hpos1 : 0 < modOne σ z + ((bridgeOne σ z).re - 3 / 2))
    (hpos2 : 0 < modOne σ z - ((bridgeTwo σ z).re - 3 / 2))
    (hord : angleOneAtOne σ z ≤ angleTwoAtOne σ z)
    (hlam : 0 ≤ (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).re ∨ β' < lensCoord σ z ∨
      lensCoord σ z < β) :
    ∃ D : ℝ, 0 < D ∧
      HasDerivAt (fun t => angleCornerOne σ a b β β' (hcirc σ.vertexOne z t)) D 0 := by
  have hz := norm_lt_one_of_domOneThree hz1
  have hv1 := norm_vertexOne_lt_one h
  obtain ⟨d₁, hd₁, h₁⟩ := exists_hasDerivAt_angleOneAtOne h hz1 hpos1 hψ
  obtain ⟨d₂, hd₂, h₂⟩ := exists_hasDerivAt_angleTwoAtOne h hz2 hpos2 hψ'
  have hψd := hasDerivAt_psiOne_hcirc h hz hψ
  have hL := hasDerivAt_lensCoord_hcircOne h hz
  have hsw := (hasDerivAt_coneStep β β' (lensCoord σ (hcirc σ.vertexOne z 0))).comp
    (0 : ℝ) hL
  rw [hcirc_zero hv1 hz] at hsw
  have hden : 0 < 1 - normSq (σ.rotOne z) := by linarith [normSq_rotOne_lt_one h hz]
  set sw' := deriv (coneStep β β') (lensCoord σ z) *
    -(2 * (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).re / (1 - normSq (σ.rotOne z))) with hsw'
  have hsw0 : sw' ≤ 0 := by
    apply lensSwitch_deriv_nonpos' hβ
    rcases hlam with hl | hl | hl
    · left
      have : 0 ≤ 2 * (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).re / (1 - normSq (σ.rotOne z)) :=
        div_nonneg (by linarith) hden.le
      linarith
    · exact Or.inr (Or.inl hl)
    · exact Or.inr (Or.inr hl)
  set τ₀ := coneStep a b (hd σ 0 z) with hτ₀
  have hΘγ : HasDerivAt (fun t => angleCornerOne σ a b β β' (hcirc σ.vertexOne z t))
      ((1 - τ₀) * (σ.p₁ * 1) + τ₀ * ((sw' * angleOneAtOne σ z + lensSwitch σ β β' z * d₁) +
        ((0 - sw') * angleTwoAtOne σ z + (1 - lensSwitch σ β β' z) * d₂))) 0 := by
    have hh := ((hasDerivAt_const (0 : ℝ) (1 - τ₀)).mul (hψd.const_mul (σ.p₁ : ℝ))).add
      ((hasDerivAt_const (0 : ℝ) τ₀).mul ((hsw.mul h₁).add
        (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hsw).mul h₂)))
    have e : (fun t => angleCornerOne σ a b β β' (hcirc σ.vertexOne z t)) =
        (fun _ => 1 - τ₀) * (fun t => (σ.p₁ : ℝ) * psiOne σ (hcirc σ.vertexOne z t)) +
        (fun _ => τ₀) * ((fun t => lensSwitch σ β β' (hcirc σ.vertexOne z t)) *
          (fun t => angleOneAtOne σ (hcirc σ.vertexOne z t)) +
          ((fun _ => (1 : ℝ)) - fun t => lensSwitch σ β β' (hcirc σ.vertexOne z t)) *
          (fun t => angleTwoAtOne σ (hcirc σ.vertexOne z t))) := by
      funext t
      have : hd σ 0 (hcirc σ.vertexOne z t) = hd σ 0 z := hd_hcirc h 0 hz t
      simp only [angleCornerOne, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, this, hτ₀]
    rw [e]
    convert hh using 1
    · rfl
    · simp only [Function.comp_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply,
        hcirc_zero hv1 hz, zero_mul, zero_add, lensSwitch]
  have hpR : (0 : ℝ) < σ.p₁ := by exact_mod_cast one_le_p₁ (σ := σ)
  have hτ0 : 0 ≤ τ₀ := coneStep_nonneg _ _ _
  have hτ1 : τ₀ ≤ 1 := coneStep_le_one _ _ _
  have hs0 : 0 ≤ lensSwitch σ β β' z := coneStep_nonneg _ _ _
  have hs1 : lensSwitch σ β β' z ≤ 1 := coneStep_le_one _ _ _
  have hD : 0 < (1 - τ₀) * (σ.p₁ * 1) + τ₀ * ((sw' * angleOneAtOne σ z +
      lensSwitch σ β β' z * d₁) + ((0 - sw') * angleTwoAtOne σ z +
        (1 - lensSwitch σ β β' z) * d₂)) := by
    have hb : 0 < lensSwitch σ β β' z * d₁ + (1 - lensSwitch σ β β' z) * d₂ := by
      have := convex_comb_pos hs0 hs1 hd₂ hd₁
      linarith
    have hx : 0 ≤ sw' * (angleOneAtOne σ z - angleTwoAtOne σ z) :=
      mul_nonneg_of_nonpos_of_nonpos hsw0 (by linarith)
    have hin : 0 < (sw' * angleOneAtOne σ z + lensSwitch σ β β' z * d₁) +
        ((0 - sw') * angleTwoAtOne σ z + (1 - lensSwitch σ β β' z) * d₂) := by nlinarith
    have := convex_comb_pos hτ0 hτ1 (by linarith : (0 : ℝ) < σ.p₁ * 1) hin
    linarith
  exact ⟨_, hD, hΘγ⟩

theorem det_fderiv_cornerOne_pos {a b β β' : ℝ} (hab : a < b) (hβ : β < β') {z : ℂ}
    (hz1 : z ∈ domOneThree σ) (hz2 : z ∈ domOneTwo σ)
    (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (hψ' : 0 < ‖exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z‖ +
      (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).re)
    (hpos1 : 0 < modOne σ z + ((bridgeOne σ z).re - 3 / 2))
    (hpos2 : 0 < modOne σ z - ((bridgeTwo σ z).re - 3 / 2))
    (hord : angleOneAtOne σ z ≤ angleTwoAtOne σ z)
    (hlam : 0 ≤ (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).re ∨ β' < lensCoord σ z ∨
      lensCoord σ z < β) :
    0 < (fderiv ℝ (cornerOne σ a b β β') z).det := by
  have hz := norm_lt_one_of_domOneThree hz1
  have hv1 := norm_vertexOne_lt_one h
  have hne := (hd_ne_zero_of_domOneThree h hz1).2
  have hd0 : 0 < hd σ 0 z := lt_of_le_of_ne (hd_nonneg 0 z) (Ne.symm hne)
  have hd1 := hd_lt_one h 0 hz
  obtain ⟨S', hS', hSd⟩ := exists_hasDerivAt_hypInnerRadial (one_le_p₁ (σ := σ)) hab
    (tauOne_pos h) tauOne_lt_one hd0 hd1
  obtain ⟨D, hD, hΘγ⟩ := exists_hasDerivAt_angleCornerOne h (a := a) (b := b) hβ hz1 hz2
    hψ hψ' hpos1 hpos2 hord hlam
  have hρ : DifferentiableAt ℝ (hd σ 0) z :=
    (contDiffAt_hd h 0 hz hne).differentiableAt (by simp)
  have hΘd : DifferentiableAt ℝ (angleCornerOne σ a b β β') z :=
    (contDiffAt_angleCornerOne h a b β β' hz1 hz2 hψ hpos1 hpos2).differentiableAt (by simp)
  have hργ : ∀ᶠ t in 𝓝 (0 : ℝ), hd σ 0 (hcirc σ.vertexOne z t) = hd σ 0 z :=
    Eventually.of_forall fun t => hd_hcirc h 0 hz t
  have hm0 : mob σ.vertexOne z ≠ 0 := norm_ne_zero_iff.1 hne
  have hρN : HasDerivAt (fun t : ℝ => hd σ 0 (z + t * hrad σ.vertexOne z)) (hd σ 0 z) 0 :=
    hasDerivAt_norm_mob_hrad hv1 hz hm0
  have key := det_fderiv_polar (c := ((3 / 2 : ℝ) : ℂ))
    (S := hypInnerRadial σ.p₁ a b (tauOne σ)) (ρ := hd σ 0)
    (Θ := angleCornerOne σ a b β β') (N := hrad σ.vertexOne z) hSd hρ hΘd
    (hasDerivAt_hcirc hv1 hz) (hcirc_zero hv1 hz) hργ hΘγ hρN (hasDerivAt_comp_ray' hΘd)
  rw [cross_I_mul] at key
  have hN : 0 < ‖hrad σ.vertexOne z‖ ^ 2 := by
    have := norm_pos_iff.2 (hrad_ne_zero hv1 hz hm0)
    positivity
  have hS0 := hypInnerRadial_pos (p := σ.p₁) (a := a) (b := b) (tauOne_pos h) tauOne_lt_one
    hd0 hd1
  exact det_pos_of_polar' hN key (by positivity)

omit h in
theorem polar_pow' {w : ℂ} (hpos : 0 < ‖w‖ + w.re) (p : ℕ) :
    w ^ p = ((‖w‖ ^ p : ℝ) : ℂ) * exp ((((p : ℝ) * discAngle w : ℝ) : ℂ) * I) := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hpos
  conv_lhs => rw [halfArg_polar_self hw0 hpos]
  rw [mul_pow, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

theorem norm_rotOne_eq_hd (z : ℂ) : ‖σ.rotOne z‖ = hd σ 0 z := norm_rotOne h z

theorem cornerOne_eq_apexOne {a b β β' : ℝ} (hab : a < b) (ha : 0 ≤ a) {z : ℂ}
    (hd : hd σ 0 z ≤ a) (hψ : z = σ.vertexOne ∨ 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re) :
    cornerOne σ a b β β' z = 3 / 2 + σ.rotOne z ^ σ.p₁ / 2 := by
  have hτ : coneStep a b (HypFold.hd σ 0 z) = 0 := coneStep_eq_zero hab hd
  rcases hψ with hz | hz
  · subst hz
    have hp := one_le_p₁ (σ := σ)
    have h0 : HypFold.hd σ 0 σ.vertexOne = 0 := by
      change ‖mob σ.vertexOne σ.vertexOne‖ = 0
      rw [mob_self, norm_zero]
    have hr : σ.rotOne σ.vertexOne = 0 := by rw [rotOne_eq_mul_mob h, mob_self, mul_zero]
    rw [cornerOne, hypInnerRadial, h0, coneStep_eq_zero hab ha, hr]
    simp [zero_pow (by omega : σ.p₁ ≠ 0)]
  · rw [cornerOne, angleCornerOne, hypInnerRadial, hτ, polar_pow' hz, norm_rotOne_eq_hd h, psiOne]
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    push_cast
    ring

omit h in
theorem polar_of_norm_sub' {u : ℂ} {c S : ℝ} (hS : 0 < S) (hn : ‖u - c‖ = S)
    (hpos : 0 < S + (u.re - c)) :
    u = (c : ℂ) + (S : ℂ) * exp ((halfArg S (u.re - c) u.im : ℂ) * I) := by
  have hsq : (u.re - c) ^ 2 + u.im ^ 2 = S ^ 2 := by
    rw [← hn, Complex.sq_norm, normSq_apply]
    simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
    ring
  rw [← halfArg_polar hS hpos hsq]
  apply Complex.ext <;> simp

omit h in
theorem polar_of_norm_sub_neg' {u : ℂ} {c S : ℝ} (hS : 0 < S) (hn : ‖u - c‖ = S)
    (hpos : 0 < S - (u.re - c)) :
    u = (c : ℂ) + (S : ℂ) * exp ((negHalfArg S (u.re - c) u.im : ℂ) * I) := by
  have hsq : (u.re - c) ^ 2 + u.im ^ 2 = S ^ 2 := by
    rw [← hn, Complex.sq_norm, normSq_apply]
    simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
    ring
  rw [← negHalfArg_polar hS hpos hsq]
  apply Complex.ext <;> simp

omit h in
theorem modOne_eq_radial (z : ℂ) :
    modOne σ z = 3 / 2 + compactProfileSlope * canonForm (tauOne σ) (HypFold.hd σ 0 z) := rfl

theorem cornerOne_eq_bridgeOne {a b β β' : ℝ} (hab : a < b) (hβ : β < β') {z : ℂ}
    (hz1 : z ∈ domOneThree σ) (hpos1 : 0 < modOne σ z + ((bridgeOne σ z).re - 3 / 2))
    (hd : b ≤ hd σ 0 z) (hs : β' ≤ lensCoord σ z) :
    cornerOne σ a b β β' z = bridgeOne σ z := by
  have hz := norm_lt_one_of_domOneThree hz1
  have hS : 0 < modOne σ z := by linarith [(modOne_mem h hz).1]
  have hn : ‖bridgeOne σ z - ((3 / 2 : ℝ) : ℂ)‖ = modOne σ z := by
    rw [show ((3 / 2 : ℝ) : ℂ) = 3 / 2 by push_cast; ring]
    exact (norm_bridgeOne h hz1).2
  conv_rhs => rw [polar_of_norm_sub' hS hn hpos1]
  rw [cornerOne, angleCornerOne, hypInnerRadial, coneStep_eq_one hab hd, lensSwitch,
    coneStep_eq_one hβ hs, modOne_eq_radial, angleOneAtOne, modOne_eq_radial]
  simp only [sub_self, zero_mul, one_mul, zero_add, add_zero, zero_div]

theorem cornerOne_eq_bridgeTwo {a b β β' : ℝ} (hab : a < b) (hβ : β < β') {z : ℂ}
    (hz2 : z ∈ domOneTwo σ) (hpos2 : 0 < modOne σ z - ((bridgeTwo σ z).re - 3 / 2))
    (hd : b ≤ hd σ 0 z) (hs : lensCoord σ z ≤ β) :
    cornerOne σ a b β β' z = bridgeTwo σ z := by
  have hz := norm_lt_one_of_domOneTwo hz2
  have hS : 0 < modOne σ z := by linarith [(modOne_mem h hz).1]
  have hn : ‖bridgeTwo σ z - ((3 / 2 : ℝ) : ℂ)‖ = modOne σ z := by
    rw [show ((3 / 2 : ℝ) : ℂ) = 3 / 2 by push_cast; ring]
    exact (norm_bridgeTwo h hz2).1
  conv_rhs => rw [polar_of_norm_sub_neg' hS hn hpos2]
  rw [cornerOne, angleCornerOne, hypInnerRadial, coneStep_eq_one hab hd, lensSwitch,
    coneStep_eq_zero hβ hs, modOne_eq_radial, angleTwoAtOne, modOne_eq_radial]
  simp only [sub_self, zero_mul, one_mul, zero_add, sub_zero, zero_div]

omit h in
theorem one_le_p₂ : 1 ≤ σ.p₂ := le_trans (by norm_num) σ.two_le_p₂

theorem contDiffAt_angleCornerTwo (a b β β' : ℝ) {z : ℂ} (hz2 : z ∈ domOneTwo σ)
    (hz0 : z ∈ domZeroThree σ)
    (hpos2 : 0 < modTwo σ z + ((bridgeTwo σ z).re + 3 / 2))
    (hpos0 : 0 < modTwo σ z - ((bridgeZero σ z).re + 3 / 2)) :
    ContDiffAt ℝ ∞ (angleCornerTwo σ a b β β') z := by
  have hz := norm_lt_one_of_domOneTwo hz2
  have hτ : ContDiffAt ℝ ∞ (fun u => coneStep a b (hd σ 1 u)) z :=
    (contDiff_coneStep a b).contDiffAt.comp z
      (contDiffAt_hd h 1 hz (hd_ne_zero_of_domOneTwo h hz2).1)
  have hs : ContDiffAt ℝ ∞ (lensSwitch σ β β') z :=
    (contDiff_coneStep β β').contDiffAt.comp z (contDiffAt_lensCoord h hz)
  exact ((contDiffAt_const.sub hτ).mul (contDiffAt_const.mul
    (contDiffAt_psiTwo h hz hz2.2.2.1))).add
    (hτ.mul (((contDiffAt_const.sub hs).mul (contDiffAt_angleTwoAtTwo h hz2 hpos2)).add
      (hs.mul (contDiffAt_angleZeroAtTwo h hz0 hpos0))))

theorem contDiffAt_cornerTwo (a b β β' : ℝ) {z : ℂ} (hz2 : z ∈ domOneTwo σ)
    (hz0 : z ∈ domZeroThree σ)
    (hpos2 : 0 < modTwo σ z + ((bridgeTwo σ z).re + 3 / 2))
    (hpos0 : 0 < modTwo σ z - ((bridgeZero σ z).re + 3 / 2)) :
    ContDiffAt ℝ ∞ (cornerTwo σ a b β β') z := by
  have hz := norm_lt_one_of_domOneTwo hz2
  have hdc := contDiffAt_hd h 1 hz (hd_ne_zero_of_domOneTwo h hz2).1
  have hD : 1 - hd σ 1 z * tauTwo σ ≠ 0 := by
    have := hd_lt_one h 1 hz
    have := hd_nonneg (σ := σ) 1 z
    have := tauTwo_lt_one (σ := σ)
    nlinarith [tauTwo_pos h]
  have hS : ContDiffAt ℝ ∞ (fun u => hypInnerRadial σ.p₂ a b (tauTwo σ) (hd σ 1 u)) z :=
    (contDiffAt_hypInnerRadial σ.p₂ a b hD).comp z hdc
  have hΘ := contDiffAt_angleCornerTwo h a b β β' hz2 hz0 hpos2 hpos0
  have hof : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := ofRealCLM.contDiff
  exact contDiffAt_const.add ((hof.contDiffAt.comp z hS).mul
    (((hof.contDiffAt.comp z hΘ).mul contDiffAt_const).cexp))

theorem exists_hasDerivAt_angleCornerTwo {a b β β' : ℝ} (hβ : β < β') {z : ℂ}
    (hz2 : z ∈ domOneTwo σ) (hz0 : z ∈ domZeroThree σ)
    (hψ' : 0 < ‖exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z‖ +
      (exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).re)
    (hpos2 : 0 < modTwo σ z + ((bridgeTwo σ z).re + 3 / 2))
    (hpos0 : 0 < modTwo σ z - ((bridgeZero σ z).re + 3 / 2))
    (hord : angleTwoAtTwo σ z ≤ angleZeroAtTwo σ z)
    (hlam : 0 ≤ (σ.rotTwo z).re ∨ β' < lensCoord σ z ∨ lensCoord σ z < β) :
    ∃ D : ℝ, 0 < D ∧
      HasDerivAt (fun t => angleCornerTwo σ a b β β' (hcirc σ.vertexTwo z t)) D 0 := by
  have hz := norm_lt_one_of_domOneTwo hz2
  have hv2 := norm_vertexTwo_lt_one h
  obtain ⟨d₂, hd₂, h₂⟩ := exists_hasDerivAt_angleTwoAtTwo h hz2 hpos2
  obtain ⟨d₀, hd₀, h₀⟩ := exists_hasDerivAt_angleZeroAtTwo h hz0 hpos0 hψ'
  have hψd := hasDerivAt_psiTwo_hcirc h hz hz2.2.2.1
  have hL := hasDerivAt_lensCoord_hcircTwo h hz
  have hsw := (hasDerivAt_coneStep β β' (lensCoord σ (hcirc σ.vertexTwo z 0))).comp
    (0 : ℝ) hL
  rw [hcirc_zero hv2 hz] at hsw
  have hden : 0 < 1 - normSq (σ.rotTwo z) := by linarith [normSq_rotTwo_lt_one h hz]
  set sw' := deriv (coneStep β β') (lensCoord σ z) *
    (2 * (σ.rotTwo z).re / (1 - normSq (σ.rotTwo z))) with hsw'
  have hsw0 : 0 ≤ sw' := by
    apply lensSwitch_deriv_nonneg' hβ
    rcases hlam with hl | hl | hl
    · exact Or.inl (div_nonneg (by linarith) hden.le)
    · exact Or.inr (Or.inl hl)
    · exact Or.inr (Or.inr hl)
  set τ₀ := coneStep a b (hd σ 1 z) with hτ₀
  have hΘγ : HasDerivAt (fun t => angleCornerTwo σ a b β β' (hcirc σ.vertexTwo z t))
      ((1 - τ₀) * (σ.p₂ * 1) + τ₀ * (((0 - sw') * angleTwoAtTwo σ z +
        (1 - lensSwitch σ β β' z) * d₂) + (sw' * angleZeroAtTwo σ z +
          lensSwitch σ β β' z * d₀))) 0 := by
    have hh := ((hasDerivAt_const (0 : ℝ) (1 - τ₀)).mul (hψd.const_mul (σ.p₂ : ℝ))).add
      ((hasDerivAt_const (0 : ℝ) τ₀).mul ((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hsw).mul
        h₂).add (hsw.mul h₀)))
    have e : (fun t => angleCornerTwo σ a b β β' (hcirc σ.vertexTwo z t)) =
        (fun _ => 1 - τ₀) * (fun t => (σ.p₂ : ℝ) * psiTwo σ (hcirc σ.vertexTwo z t)) +
        (fun _ => τ₀) * (((fun _ => (1 : ℝ)) -
          fun t => lensSwitch σ β β' (hcirc σ.vertexTwo z t)) *
          (fun t => angleTwoAtTwo σ (hcirc σ.vertexTwo z t)) +
          (fun t => lensSwitch σ β β' (hcirc σ.vertexTwo z t)) *
          (fun t => angleZeroAtTwo σ (hcirc σ.vertexTwo z t))) := by
      funext t
      have : hd σ 1 (hcirc σ.vertexTwo z t) = hd σ 1 z := hd_hcirc h 1 hz t
      simp only [angleCornerTwo, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, this, hτ₀]
    rw [e]
    convert hh using 1
    · rfl
    · simp only [Function.comp_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply,
        hcirc_zero hv2 hz, zero_mul, zero_add, lensSwitch]
  have hpR : (0 : ℝ) < σ.p₂ := by exact_mod_cast one_le_p₂ (σ := σ)
  have hτ0 : 0 ≤ τ₀ := coneStep_nonneg _ _ _
  have hτ1 : τ₀ ≤ 1 := coneStep_le_one _ _ _
  have hs0 : 0 ≤ lensSwitch σ β β' z := coneStep_nonneg _ _ _
  have hs1 : lensSwitch σ β β' z ≤ 1 := coneStep_le_one _ _ _
  have hD : 0 < (1 - τ₀) * (σ.p₂ * 1) + τ₀ * (((0 - sw') * angleTwoAtTwo σ z +
        (1 - lensSwitch σ β β' z) * d₂) + (sw' * angleZeroAtTwo σ z +
          lensSwitch σ β β' z * d₀)) := by
    have hb : 0 < (1 - lensSwitch σ β β' z) * d₂ + lensSwitch σ β β' z * d₀ :=
      convex_comb_pos hs0 hs1 hd₂ hd₀
    have hx : 0 ≤ sw' * (angleZeroAtTwo σ z - angleTwoAtTwo σ z) :=
      mul_nonneg hsw0 (by linarith)
    have hin : 0 < ((0 - sw') * angleTwoAtTwo σ z + (1 - lensSwitch σ β β' z) * d₂) +
        (sw' * angleZeroAtTwo σ z + lensSwitch σ β β' z * d₀) := by nlinarith
    have := convex_comb_pos hτ0 hτ1 (by linarith : (0 : ℝ) < σ.p₂ * 1) hin
    linarith
  exact ⟨_, hD, hΘγ⟩

theorem det_fderiv_cornerTwo_pos {a b β β' : ℝ} (hab : a < b) (hβ : β < β') {z : ℂ}
    (hz2 : z ∈ domOneTwo σ) (hz0 : z ∈ domZeroThree σ)
    (hψ' : 0 < ‖exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z‖ +
      (exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).re)
    (hpos2 : 0 < modTwo σ z + ((bridgeTwo σ z).re + 3 / 2))
    (hpos0 : 0 < modTwo σ z - ((bridgeZero σ z).re + 3 / 2))
    (hord : angleTwoAtTwo σ z ≤ angleZeroAtTwo σ z)
    (hlam : 0 ≤ (σ.rotTwo z).re ∨ β' < lensCoord σ z ∨ lensCoord σ z < β) :
    0 < (fderiv ℝ (cornerTwo σ a b β β') z).det := by
  have hz := norm_lt_one_of_domOneTwo hz2
  have hv2 := norm_vertexTwo_lt_one h
  have hne := (hd_ne_zero_of_domOneTwo h hz2).1
  have hd0 : 0 < hd σ 1 z := lt_of_le_of_ne (hd_nonneg 1 z) (Ne.symm hne)
  have hd1 := hd_lt_one h 1 hz
  obtain ⟨S', hS', hSd⟩ := exists_hasDerivAt_hypInnerRadial (one_le_p₂ (σ := σ)) hab
    (tauTwo_pos h) tauTwo_lt_one hd0 hd1
  obtain ⟨D, hD, hΘγ⟩ := exists_hasDerivAt_angleCornerTwo h (a := a) (b := b) hβ hz2 hz0
    hψ' hpos2 hpos0 hord hlam
  have hρ : DifferentiableAt ℝ (hd σ 1) z :=
    (contDiffAt_hd h 1 hz hne).differentiableAt (by simp)
  have hΘd : DifferentiableAt ℝ (angleCornerTwo σ a b β β') z :=
    (contDiffAt_angleCornerTwo h a b β β' hz2 hz0 hpos2 hpos0).differentiableAt (by simp)
  have hργ : ∀ᶠ t in 𝓝 (0 : ℝ), hd σ 1 (hcirc σ.vertexTwo z t) = hd σ 1 z :=
    Eventually.of_forall fun t => hd_hcirc h 1 hz t
  have hm0 : mob σ.vertexTwo z ≠ 0 := norm_ne_zero_iff.1 hne
  have hρN : HasDerivAt (fun t : ℝ => hd σ 1 (z + t * hrad σ.vertexTwo z)) (hd σ 1 z) 0 :=
    hasDerivAt_norm_mob_hrad hv2 hz hm0
  have key := det_fderiv_polar (c := ((-(3 / 2) : ℝ) : ℂ))
    (S := hypInnerRadial σ.p₂ a b (tauTwo σ)) (ρ := hd σ 1)
    (Θ := angleCornerTwo σ a b β β') (N := hrad σ.vertexTwo z) hSd hρ hΘd
    (hasDerivAt_hcirc hv2 hz) (hcirc_zero hv2 hz) hργ hΘγ hρN (hasDerivAt_comp_ray' hΘd)
  rw [cross_I_mul] at key
  have hN : 0 < ‖hrad σ.vertexTwo z‖ ^ 2 := by
    have := norm_pos_iff.2 (hrad_ne_zero hv2 hz hm0)
    positivity
  have hS0 := hypInnerRadial_pos (p := σ.p₂) (a := a) (b := b) (tauTwo_pos h) tauTwo_lt_one
    hd0 hd1
  exact det_pos_of_polar' hN key (by positivity)

theorem norm_rotTwo_eq_hd (z : ℂ) : ‖σ.rotTwo z‖ = hd σ 1 z := norm_rotTwo h z

theorem cornerTwo_eq_apexTwo {a b β β' : ℝ} (hab : a < b) (ha : 0 ≤ a) {z : ℂ}
    (hd : hd σ 1 z ≤ a) (hψ : z = σ.vertexTwo ∨ 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re) :
    cornerTwo σ a b β β' z = -(3 / 2) + σ.rotTwo z ^ σ.p₂ / 2 := by
  have hτ : coneStep a b (HypFold.hd σ 1 z) = 0 := coneStep_eq_zero hab hd
  rcases hψ with hz | hz
  · subst hz
    have hp := one_le_p₂ (σ := σ)
    have h0 : HypFold.hd σ 1 σ.vertexTwo = 0 := by
      change ‖mob σ.vertexTwo σ.vertexTwo‖ = 0
      rw [mob_self, norm_zero]
    have hr : σ.rotTwo σ.vertexTwo = 0 := rotTwo_vertexTwo h
    rw [cornerTwo, hypInnerRadial, h0, coneStep_eq_zero hab ha, hr]
    simp [zero_pow (by omega : σ.p₂ ≠ 0)]
  · rw [cornerTwo, angleCornerTwo, hypInnerRadial, hτ, polar_pow' hz, norm_rotTwo_eq_hd h,
      psiTwo]
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    push_cast
    ring

omit h in
theorem modTwo_eq_radial (z : ℂ) :
    modTwo σ z = 3 / 2 + compactProfileSlope * canonForm (tauTwo σ) (HypFold.hd σ 1 z) := rfl

theorem cornerTwo_eq_bridgeTwo {a b β β' : ℝ} (hab : a < b) (hβ : β < β') {z : ℂ}
    (hz2 : z ∈ domOneTwo σ) (hpos2 : 0 < modTwo σ z + ((bridgeTwo σ z).re + 3 / 2))
    (hd : b ≤ hd σ 1 z) (hs : lensCoord σ z ≤ β) :
    cornerTwo σ a b β β' z = bridgeTwo σ z := by
  have hz := norm_lt_one_of_domOneTwo hz2
  have hS : 0 < modTwo σ z := by linarith [(modTwo_mem h hz).1]
  have hn : ‖bridgeTwo σ z - ((-(3 / 2) : ℝ) : ℂ)‖ = modTwo σ z := by
    rw [show ((-(3 / 2) : ℝ) : ℂ) = -(3 / 2) by push_cast; ring, sub_neg_eq_add]
    exact (norm_bridgeTwo h hz2).2
  have hp : 0 < modTwo σ z + ((bridgeTwo σ z).re - -(3 / 2)) := by
    rw [sub_neg_eq_add]; exact hpos2
  conv_rhs => rw [polar_of_norm_sub' hS hn hp]
  rw [cornerTwo, angleCornerTwo, hypInnerRadial, coneStep_eq_one hab hd, lensSwitch,
    coneStep_eq_zero hβ hs, modTwo_eq_radial, angleTwoAtTwo, modTwo_eq_radial, sub_neg_eq_add]
  simp only [sub_self, zero_mul, one_mul, zero_add, add_zero, sub_zero, zero_div]

theorem cornerTwo_eq_bridgeZero {a b β β' : ℝ} (hab : a < b) (hβ : β < β') {z : ℂ}
    (hz0 : z ∈ domZeroThree σ) (hpos0 : 0 < modTwo σ z - ((bridgeZero σ z).re + 3 / 2))
    (hd : b ≤ hd σ 1 z) (hs : β' ≤ lensCoord σ z) :
    cornerTwo σ a b β β' z = bridgeZero σ z := by
  have hz := norm_lt_one_of_domZeroThree hz0
  have hS : 0 < modTwo σ z := by linarith [(modTwo_mem h hz).1]
  have hn : ‖bridgeZero σ z - ((-(3 / 2) : ℝ) : ℂ)‖ = modTwo σ z := by
    rw [show ((-(3 / 2) : ℝ) : ℂ) = -(3 / 2) by push_cast; ring, sub_neg_eq_add]
    exact (norm_bridgeZero h hz0).2
  have hp : 0 < modTwo σ z - ((bridgeZero σ z).re - -(3 / 2)) := by
    rw [sub_neg_eq_add]; exact hpos0
  conv_rhs => rw [polar_of_norm_sub_neg' hS hn hp]
  rw [cornerTwo, angleCornerTwo, hypInnerRadial, coneStep_eq_one hab hd, lensSwitch,
    coneStep_eq_one hβ hs, modTwo_eq_radial, angleZeroAtTwo, modTwo_eq_radial, sub_neg_eq_add]
  simp only [sub_self, zero_mul, one_mul, zero_add, zero_div]

omit h in
theorem one_le_p₃ : 1 ≤ σ.p₃ := le_trans (by norm_num) σ.two_le_p₃

theorem contDiffAt_nuThree (w δ : ℝ) {z : ℂ} (hz : ‖z‖ < 1) (hψ : 0 < ‖z‖ + z.re)
    (h1 : hd σ 0 z ≠ 0) (h2 : hd σ 1 z ≠ 0) : ContDiffAt ℝ ∞ (nuThree σ w δ) z := by
  have hB : ContDiffAt ℝ ∞ (blendThree σ w δ) z :=
    (contDiffAt_const.mul (((contDiffAt_const.mul (contDiffAt_discAngle_comp'
      contDiffAt_id hψ)).div_const _).sub contDiffAt_const)).add (contDiffAt_const.mul
        ((contDiffAt_canon h 1 hz h2).sub (contDiffAt_canon h 0 hz h1)))
  exact (contDiff_coneStep (-w) w).contDiffAt.comp z hB

theorem contDiffAt_angleCornerThree (a b w δ : ℝ) {z : ℂ} (hz1 : z ∈ domOneThree σ)
    (hz0 : z ∈ domZeroThree σ) (hψ : 0 < ‖z‖ + z.re)
    (hpos1 : 0 < modThree σ z + (bridgeOne σ z).re)
    (hpos0 : 0 < modThree σ z - (bridgeZero σ z).re) :
    ContDiffAt ℝ ∞ (angleCornerThree σ a b w δ) z := by
  have hz := norm_lt_one_of_domOneThree hz1
  have hv1 := hd_ne_zero_of_domOneThree h hz1
  have hv0 := hd_ne_zero_of_domZeroThree h hz0
  have hτ : ContDiffAt ℝ ∞ (fun u : ℂ => coneStep a b ‖u‖) z :=
    (contDiff_coneStep a b).contDiffAt.comp z (contDiffAt_norm ℝ (norm_ne_zero_iff.1 hv1.1))
  have hν := contDiffAt_nuThree h w δ hz hψ hv1.2 hv0.2
  exact ((contDiffAt_const.sub hτ).mul (contDiffAt_const.sub (contDiffAt_const.mul
    (contDiffAt_discAngle_comp' contDiffAt_id hψ)))).add
    (hτ.mul (((contDiffAt_const.sub hν).mul (contDiffAt_angleZeroAtThree h hz0 hpos0)).add
      (hν.mul (contDiffAt_angleOneAtThree h hz1 hpos1))))

theorem contDiffAt_cornerThree (a b w δ : ℝ) {z : ℂ} (hz1 : z ∈ domOneThree σ)
    (hz0 : z ∈ domZeroThree σ) (hψ : 0 < ‖z‖ + z.re)
    (hpos1 : 0 < modThree σ z + (bridgeOne σ z).re)
    (hpos0 : 0 < modThree σ z - (bridgeZero σ z).re) :
    ContDiffAt ℝ ∞ (cornerThree σ a b w δ) z := by
  have hz := norm_lt_one_of_domOneThree hz1
  have hv1 := hd_ne_zero_of_domOneThree h hz1
  have hD : 1 - ‖z‖ * tauThree σ ≠ 0 := by
    have := tauThree_lt_one (σ := σ)
    nlinarith [tauThree_pos h, norm_nonneg z]
  have hS : ContDiffAt ℝ ∞ (fun u : ℂ => hypOuterRadial σ.p₃ a b (tauThree σ) ‖u‖) z :=
    (contDiffAt_hypOuterRadial σ.p₃ a b hD).comp z
      (contDiffAt_norm ℝ (norm_ne_zero_iff.1 hv1.1))
  have hΘ := contDiffAt_angleCornerThree h a b w δ hz1 hz0 hψ hpos1 hpos0
  have hof : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := ofRealCLM.contDiff
  exact contDiffAt_const.add ((hof.contDiffAt.comp z hS).mul
    (((hof.contDiffAt.comp z hΘ).mul contDiffAt_const).cexp))

theorem exists_hasDerivAt_nuThree {w δ : ℝ} (hw : 0 < w) (hδ : 0 < δ) {z : ℂ}
    (hz : ‖z‖ < 1) (hψ : 0 < ‖z‖ + z.re) (h1 : hd σ 0 z ≠ 0) (h2 : hd σ 1 z ≠ 0)
    (hside : (0 ≤ σ.wallSide 0 z ∧ 0 ≤ σ.wallSide 1 z) ∨ w < blendThree σ w δ z ∨
      blendThree σ w δ z < -w) :
    ∃ ν' : ℝ, 0 ≤ ν' ∧ HasDerivAt (fun t => nuThree σ w δ (hcirc 0 z t)) ν' 0 := by
  have h00 : ‖(0 : ℂ)‖ < 1 := by simp
  have hψd := hasDerivAt_psiThree_hcirc hψ
  obtain ⟨c₁, hc₁, hC1⟩ := exists_hasDerivAt_canon_hcirc h 1 (u := 1) norm_one h00 hz h2
    (sideTwoThree_pos h) (α := 0) (by
      rw [one_mul, mob_zero_left, ofReal_zero, zero_mul, Complex.exp_zero, mul_one]; rfl)
  obtain ⟨c₀, hc₀, hC0⟩ := exists_hasDerivAt_canon_hcirc h 0 (u := 1) norm_one h00 hz h1
    (sideOneThree_pos h) (α := σ.θ₃) (by rw [one_mul, mob_zero_left]; rfl)
  have e1 : (exp (-(((0 : ℝ) : ℂ) * I)) * (1 * mob 0 z)).im = σ.wallSide 0 z := by
    rw [one_mul, mob_zero_left, ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul]
    rfl
  have e0 : (exp (-((σ.θ₃ : ℂ) * I)) * (1 * mob 0 z)).im = -σ.wallSide 1 z := by
    rw [one_mul, mob_zero_left, wallSide_one_eq_neg_im, neg_neg]
  rw [e1] at hC1
  rw [e0] at hC0
  have hB : HasDerivAt (fun t => blendThree σ w δ (hcirc 0 z t))
      (w * (2 * 1 / σ.θ₃) + w / δ * (σ.wallSide 0 z * c₁ - -σ.wallSide 1 z * c₀)) 0 := by
    have hh := ((((hψd.const_mul 2).div_const σ.θ₃).sub_const 1).const_mul w).add
      ((hC1.sub hC0).const_mul (w / δ))
    exact hh
  have hN := (hasDerivAt_coneStep (-w) w (blendThree σ w δ (hcirc 0 z 0))).comp (0 : ℝ) hB
  rw [hcirc_zero h00 hz] at hN
  refine ⟨_, ?_, hN⟩
  have hwlt : -w < w := by linarith
  rcases hside with ⟨h0', h1'⟩ | hh | hh
  · apply mul_nonneg (deriv_coneStep_nonneg hwlt _)
    have := θ₃_pos σ
    have e : σ.wallSide 0 z * c₁ - -σ.wallSide 1 z * c₀ =
        σ.wallSide 0 z * c₁ + σ.wallSide 1 z * c₀ := by ring
    rw [e]
    positivity
  · rw [deriv_coneStep_eq_zero_of_lt hwlt hh, zero_mul]
  · rw [deriv_coneStep_eq_zero_of_gt hwlt hh, zero_mul]

theorem exists_hasDerivAt_angleCornerThree {a b w δ : ℝ} (hw : 0 < w) (hδ : 0 < δ) {z : ℂ}
    (hz1 : z ∈ domOneThree σ) (hz0 : z ∈ domZeroThree σ) (hψ : 0 < ‖z‖ + z.re)
    (hpos1 : 0 < modThree σ z + (bridgeOne σ z).re)
    (hpos0 : 0 < modThree σ z - (bridgeZero σ z).re)
    (hord : angleOneAtThree σ z ≤ angleZeroAtThree σ z)
    (hside : (0 ≤ σ.wallSide 0 z ∧ 0 ≤ σ.wallSide 1 z) ∨ w < blendThree σ w δ z ∨
      blendThree σ w δ z < -w) :
    ∃ D : ℝ, D < 0 ∧
      HasDerivAt (fun t => angleCornerThree σ a b w δ (hcirc 0 z t)) D 0 := by
  have hz := norm_lt_one_of_domOneThree hz1
  have h00 : ‖(0 : ℂ)‖ < 1 := by simp
  have hv1 := hd_ne_zero_of_domOneThree h hz1
  have hv0 := hd_ne_zero_of_domZeroThree h hz0
  obtain ⟨d₀, hd₀, h₀⟩ := exists_hasDerivAt_angleZeroAtThree h hz0 hpos0
  obtain ⟨d₁, hd₁, h₁⟩ := exists_hasDerivAt_angleOneAtThree h hz1 hpos1
  obtain ⟨ν', hν', hν⟩ := exists_hasDerivAt_nuThree h hw hδ hz hψ hv1.2 hv0.2 hside
  have hψd := hasDerivAt_psiThree_hcirc hψ
  set τ₀ := coneStep a b ‖z‖ with hτ₀
  have hΘγ : HasDerivAt (fun t => angleCornerThree σ a b w δ (hcirc 0 z t))
      ((1 - τ₀) * (0 - σ.p₃ * 1) + τ₀ * (((0 - ν') * angleZeroAtThree σ z +
        (1 - nuThree σ w δ z) * d₀) + (ν' * angleOneAtThree σ z + nuThree σ w δ z * d₁))) 0 := by
    have hh := ((hasDerivAt_const (0 : ℝ) (1 - τ₀)).mul ((hasDerivAt_const (0 : ℝ)
      Real.pi).sub (hψd.const_mul (σ.p₃ : ℝ)))).add ((hasDerivAt_const (0 : ℝ) τ₀).mul
        ((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hν).mul h₀).add (hν.mul h₁)))
    have e : (fun t => angleCornerThree σ a b w δ (hcirc 0 z t)) =
        (fun _ => 1 - τ₀) * ((fun _ => Real.pi) -
          fun t => (σ.p₃ : ℝ) * discAngle (hcirc 0 z t)) +
        (fun _ => τ₀) * (((fun _ => (1 : ℝ)) - fun t => nuThree σ w δ (hcirc 0 z t)) *
          (fun t => angleZeroAtThree σ (hcirc 0 z t)) +
          (fun t => nuThree σ w δ (hcirc 0 z t)) *
          (fun t => angleOneAtThree σ (hcirc 0 z t))) := by
      funext t
      have : ‖hcirc 0 z t‖ = ‖z‖ := by rw [hcirc_zero_left, norm_mul_exp]
      simp only [angleCornerThree, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, this, hτ₀]
    rw [e]
    convert hh using 1
    simp only [hcirc_zero h00 hz, Pi.sub_apply, zero_mul, zero_add]
  have hpR : (0 : ℝ) < σ.p₃ := by exact_mod_cast one_le_p₃ (σ := σ)
  have hτ0 : 0 ≤ τ₀ := coneStep_nonneg _ _ _
  have hτ1 : τ₀ ≤ 1 := coneStep_le_one _ _ _
  have hn0 : 0 ≤ nuThree σ w δ z := coneStep_nonneg _ _ _
  have hn1 : nuThree σ w δ z ≤ 1 := coneStep_le_one _ _ _
  refine ⟨_, ?_, hΘγ⟩
  have hb : 0 < (1 - nuThree σ w δ z) * (-d₀) + nuThree σ w δ z * (-d₁) :=
    convex_comb_pos hn0 hn1 (by linarith) (by linarith)
  have hx : 0 ≤ ν' * (angleZeroAtThree σ z - angleOneAtThree σ z) :=
    mul_nonneg hν' (by linarith)
  have hin : 0 < -(((0 - ν') * angleZeroAtThree σ z + (1 - nuThree σ w δ z) * d₀) +
      (ν' * angleOneAtThree σ z + nuThree σ w δ z * d₁)) := by nlinarith
  have := convex_comb_pos hτ0 hτ1 (by linarith : (0 : ℝ) < σ.p₃ * 1) hin
  nlinarith

theorem det_fderiv_cornerThree_pos {a b w δ : ℝ} (hab : a < b) (hb : b ≤ 1 / 5) (hw : 0 < w)
    (hδ : 0 < δ) {z : ℂ} (hz1 : z ∈ domOneThree σ) (hz0 : z ∈ domZeroThree σ)
    (hψ : 0 < ‖z‖ + z.re)
    (hpos1 : 0 < modThree σ z + (bridgeOne σ z).re)
    (hpos0 : 0 < modThree σ z - (bridgeZero σ z).re)
    (hord : angleOneAtThree σ z ≤ angleZeroAtThree σ z)
    (hside : (0 ≤ σ.wallSide 0 z ∧ 0 ≤ σ.wallSide 1 z) ∨ w < blendThree σ w δ z ∨
      blendThree σ w δ z < -w) :
    0 < (fderiv ℝ (cornerThree σ a b w δ) z).det := by
  have hz := norm_lt_one_of_domOneThree hz1
  have h00 : ‖(0 : ℂ)‖ < 1 := by simp
  have hv1 := hd_ne_zero_of_domOneThree h hz1
  have hz0' : z ≠ 0 := norm_ne_zero_iff.1 hv1.1
  have hd0 : 0 < ‖z‖ := norm_pos_iff.2 hz0'
  obtain ⟨S', hS', hSd⟩ := exists_hasDerivAt_hypOuterRadial (one_le_p₃ (σ := σ)) hab hb
    (tauThree_pos h) tauThree_lt_one hd0 hz
  obtain ⟨D, hD, hΘγ⟩ := exists_hasDerivAt_angleCornerThree h (a := a) (b := b) hw hδ hz1 hz0
    hψ hpos1 hpos0 hord hside
  have hnc : ContDiffAt ℝ ∞ (fun u : ℂ => ‖u‖) z := contDiffAt_norm ℝ hz0'
  have hρ : DifferentiableAt ℝ (fun u : ℂ => ‖u‖) z := hnc.differentiableAt (by simp)
  have hΘd : DifferentiableAt ℝ (angleCornerThree σ a b w δ) z :=
    (contDiffAt_angleCornerThree h a b w δ hz1 hz0 hψ hpos1 hpos0).differentiableAt (by simp)
  have hργ : ∀ᶠ t in 𝓝 (0 : ℝ), ‖hcirc 0 z t‖ = ‖z‖ :=
    Eventually.of_forall fun t => by rw [hcirc_zero_left, norm_mul_exp]
  have hm0 : mob 0 z ≠ 0 := by rwa [mob_zero_left]
  have hρN : HasDerivAt (fun t : ℝ => ‖z + t * hrad 0 z‖) ‖z‖ 0 := by
    have := hasDerivAt_norm_mob_hrad h00 hz hm0
    simp only [mob_zero_left] at this
    exact this
  have key := det_fderiv_polar (c := ((0 : ℝ) : ℂ))
    (S := hypOuterRadial σ.p₃ a b (tauThree σ)) (ρ := fun u : ℂ => ‖u‖)
    (Θ := angleCornerThree σ a b w δ) (N := hrad 0 z) hSd hρ hΘd
    (hasDerivAt_hcirc h00 hz) (hcirc_zero h00 hz) hργ hΘγ hρN (hasDerivAt_comp_ray' hΘd)
  rw [cross_I_mul] at key
  have hN : 0 < ‖hrad 0 z‖ ^ 2 := by
    have := norm_pos_iff.2 (hrad_ne_zero h00 hz hm0)
    positivity
  have hS0 := hypOuterRadial_pos (p := σ.p₃) (a := a) (b := b) (tauThree_pos h)
    tauThree_lt_one (norm_nonneg z) hz
  have hpos : 0 < hypOuterRadial σ.p₃ a b (tauThree σ) ‖z‖ * S' * D * ‖z‖ := by
    have := mul_pos_of_neg_of_neg hS' hD
    have := mul_pos hS0 this
    nlinarith
  exact det_pos_of_polar' hN key hpos

omit h in
theorem conj_div_norm_eq_exp' {z : ℂ} (hpos : 0 < ‖z‖ + z.re) :
    conj z / ‖z‖ = exp (((-discAngle z : ℝ) : ℂ) * I) := by
  have hz : z ≠ 0 := by
    rintro rfl
    simp at hpos
  have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
  have hc : conj z = (‖z‖ : ℂ) * exp (((-discAngle z : ℝ) : ℂ) * I) := by
    conv_lhs => rw [halfArg_polar_self hz hpos]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hc, mul_div_cancel_left₀ _ hn]

omit h in
theorem cornerThree_eq_outerGerm {a b w δ : ℝ} (hab : a < b) {z : ℂ} (hd : ‖z‖ ≤ a)
    (hψ : 0 < ‖z‖ + z.re) : cornerThree σ a b w δ z = compactOuterGerm σ.p₃ z := by
  rw [cornerThree, angleCornerThree, hypOuterRadial, coneStep_eq_zero hab hd, compactOuterGerm,
    conj_div_norm_eq_exp' hψ, ← Complex.exp_nat_mul]
  simp only [sub_zero, one_mul, zero_mul, add_zero]
  rw [show ((Real.pi - σ.p₃ * discAngle z : ℝ) : ℂ) * I =
      Real.pi * I + (σ.p₃ : ℂ) * (((-discAngle z : ℝ) : ℂ) * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_pi_mul_I]
  push_cast
  ring

omit h in
theorem modThree_eq_radial (z : ℂ) :
    modThree σ z = 3 - compactProfileSlope * canonForm (tauThree σ) ‖z‖ := rfl

theorem cornerThree_eq_bridgeZero {a b w δ : ℝ} (hab : a < b) (hw : 0 < w) {z : ℂ}
    (hz0 : z ∈ domZeroThree σ) (hpos0 : 0 < modThree σ z - (bridgeZero σ z).re)
    (hd : b ≤ ‖z‖) (hν : blendThree σ w δ z ≤ -w) :
    cornerThree σ a b w δ z = bridgeZero σ z := by
  have hz := norm_lt_one_of_domZeroThree hz0
  have hS : 0 < modThree σ z := by linarith [(modThree_mem h hz).1]
  have hn : ‖bridgeZero σ z - ((0 : ℝ) : ℂ)‖ = modThree σ z := by
    rw [ofReal_zero, sub_zero]
    exact (norm_bridgeZero h hz0).1
  have hp : 0 < modThree σ z - ((bridgeZero σ z).re - 0) := by rw [sub_zero]; exact hpos0
  conv_rhs => rw [polar_of_norm_sub_neg' hS hn hp]
  rw [cornerThree, angleCornerThree, hypOuterRadial, coneStep_eq_one hab hd, nuThree,
    coneStep_eq_zero (by linarith) hν, modThree_eq_radial, angleZeroAtThree, modThree_eq_radial,
    sub_zero]
  simp only [sub_self, zero_mul, one_mul, zero_add, add_zero, sub_zero]

theorem cornerThree_eq_bridgeOne {a b w δ : ℝ} (hab : a < b) (hw : 0 < w) {z : ℂ}
    (hz1 : z ∈ domOneThree σ) (hpos1 : 0 < modThree σ z + (bridgeOne σ z).re)
    (hd : b ≤ ‖z‖) (hν : w ≤ blendThree σ w δ z) :
    cornerThree σ a b w δ z = bridgeOne σ z := by
  have hz := norm_lt_one_of_domOneThree hz1
  have hS : 0 < modThree σ z := by linarith [(modThree_mem h hz).1]
  have hn : ‖bridgeOne σ z - ((0 : ℝ) : ℂ)‖ = modThree σ z := by
    rw [ofReal_zero, sub_zero]
    exact (norm_bridgeOne h hz1).1
  have hp : 0 < modThree σ z + ((bridgeOne σ z).re - 0) := by rw [sub_zero]; exact hpos1
  conv_rhs => rw [polar_of_norm_sub' hS hn hp]
  rw [cornerThree, angleCornerThree, hypOuterRadial, coneStep_eq_one hab hd, nuThree,
    coneStep_eq_one (by linarith) hν, modThree_eq_radial, angleOneAtThree, modThree_eq_radial,
    sub_zero]
  simp only [sub_self, zero_mul, one_mul, zero_add]

end Hyp

end HypFold

end GC.Seifert

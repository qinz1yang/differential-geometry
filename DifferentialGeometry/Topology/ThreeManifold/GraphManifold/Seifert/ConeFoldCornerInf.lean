import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldOuterProfile

/-!
# The corner at the cusp `∞` of the `(p, ⊤, ⊤)` fold

Lane A4, tier 2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5).
`angleZeroInf` and `angleOneInf` are the arguments about `0` of the bridges `bridgeZero` (wall 0)
and `bridgeOne` (wall 1), written with `halfArg` and `negHalfArg`: `bridgeZero` has positive and
`bridgeOne` negative real part, so the first lies in `(-π/2, π/2)`, the second in `(π/2, 3π/2)`
(`angleZeroInf_mem`, `angleOneInf_mem`), and both bridges are `(3/2 + G y) e^{i angle}`
(`bridgeZero_polar`, `bridgeOne_polar`). Along every horizontal line both angles are strictly
increasing (`exists_hasDerivAt_angleZeroInf`, `exists_hasDerivAt_angleOneInf`): the derivative is
`2|b| B B'/(b w √P)` off the wall, where `B'/w` is the explicit derivative of the other virtual
height divided by the wall function (`hasDerivAt_cuspZeroHeight_horizontal`,
`hasDerivAt_coneHeight_horizontal`), and `± w'√P/(3 (3/2 + G y))` on the wall, where `w'` is the
explicit derivative of the side function.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace ConeShape

variable (σ : ConeShape)

def angleZeroInf (z : ℂ) : ℝ :=
  halfArg (3 / 2 + coneProfile σ.constK z.im) (σ.bridgeZero z).re (σ.bridgeZero z).im

def angleOneInf (z : ℂ) : ℝ :=
  negHalfArg (3 / 2 + coneProfile σ.constK z.im) (σ.bridgeOne z).re (σ.bridgeOne z).im

theorem sq_add_sq_eq_of_norm {u : ℂ} {S : ℝ} (h : ‖u‖ = S) : u.re ^ 2 + u.im ^ 2 = S ^ 2 := by
  rw [← h, Complex.sq_norm, normSq_apply]
  ring

theorem bridgeZero_sq {z : ℂ} (hz : 0 < z.im) :
    (σ.bridgeZero z).re ^ 2 + (σ.bridgeZero z).im ^ 2 =
      (3 / 2 + coneProfile σ.constK z.im) ^ 2 :=
  sq_add_sq_eq_of_norm (σ.norm_bridgeZero hz)

theorem bridgeOne_sq {z : ℂ} (hz : z ∈ σ.domOne) :
    (σ.bridgeOne z).re ^ 2 + (σ.bridgeOne z).im ^ 2 =
      (3 / 2 + coneProfile σ.constK z.im) ^ 2 :=
  sq_add_sq_eq_of_norm (σ.norm_bridgeOne hz)

theorem outerModulus_pos (z : ℂ) : 0 < 3 / 2 + coneProfile σ.constK z.im := by
  linarith [half_le_coneProfile σ.constK_pos z.im]

theorem bridgeZero_polar {z : ℂ} (hz : 0 < z.im) :
    σ.bridgeZero z = ((3 / 2 + coneProfile σ.constK z.im : ℝ) : ℂ) *
      exp ((σ.angleZeroInf z : ℂ) * I) := by
  have h := halfArg_polar (σ.outerModulus_pos z)
    (by linarith [σ.outerModulus_pos z, σ.bridgeZero_re_pos hz]) (σ.bridgeZero_sq hz)
  rw [angleZeroInf, ← h]

theorem bridgeOne_polar {z : ℂ} (hz : z ∈ σ.domOne) :
    σ.bridgeOne z = ((3 / 2 + coneProfile σ.constK z.im : ℝ) : ℂ) *
      exp ((σ.angleOneInf z : ℂ) * I) := by
  have h := negHalfArg_polar (σ.outerModulus_pos z)
    (by linarith [σ.outerModulus_pos z, σ.bridgeOne_re_neg hz.1]) (σ.bridgeOne_sq hz)
  rw [angleOneInf, ← h]

theorem abs_div_lt_one_of_sq {S R J : ℝ} (hS : 0 < S + R) (hR : 0 < R)
    (h : R ^ 2 + J ^ 2 = S ^ 2) : |J / (S + R)| < 1 := by
  rw [abs_div, abs_of_pos hS, div_lt_one hS, abs_lt]
  constructor <;> nlinarith

theorem angleZeroInf_mem {z : ℂ} (hz : 0 < z.im) :
    σ.angleZeroInf z ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have hR := σ.bridgeZero_re_pos hz
  have hS : 0 < 3 / 2 + coneProfile σ.constK z.im + (σ.bridgeZero z).re := by
    linarith [σ.outerModulus_pos z]
  have h := abs_div_lt_one_of_sq hS hR (σ.bridgeZero_sq hz)
  rw [abs_lt] at h
  have h1 := Real.arctan_strictMono h.2
  have h2 := Real.arctan_strictMono h.1
  rw [Real.arctan_one] at h1
  rw [Real.arctan_neg, Real.arctan_one] at h2
  constructor <;> unfold angleZeroInf halfArg <;> linarith

theorem angleOneInf_mem {z : ℂ} (hz : z ∈ σ.domOne) :
    σ.angleOneInf z ∈ Set.Ioo (Real.pi / 2) (3 * Real.pi / 2) := by
  have hR : 0 < -(σ.bridgeOne z).re := by linarith [σ.bridgeOne_re_neg hz.1]
  have hS : 0 < 3 / 2 + coneProfile σ.constK z.im + -(σ.bridgeOne z).re := by
    linarith [σ.outerModulus_pos z]
  have h0 := σ.bridgeOne_sq hz
  have h0' : (-(σ.bridgeOne z).re) ^ 2 + (σ.bridgeOne z).im ^ 2 =
      (3 / 2 + coneProfile σ.constK z.im) ^ 2 := by rw [neg_sq]; exact h0
  have h := abs_div_lt_one_of_sq hS hR h0'
  rw [abs_lt] at h
  have h1 := Real.arctan_strictMono h.2
  have h2 := Real.arctan_strictMono h.1
  rw [Real.arctan_one] at h1
  rw [Real.arctan_neg, Real.arctan_one] at h2
  have e : 3 / 2 + coneProfile σ.constK z.im + -(σ.bridgeOne z).re =
      3 / 2 + coneProfile σ.constK z.im - (σ.bridgeOne z).re := by ring
  rw [e] at h1 h2
  constructor <;> unfold angleOneInf negHalfArg <;> linarith

theorem contDiffAt_halfArg_comp {S R J : ℂ → ℝ} {z : ℂ} (hS : ContDiffAt ℝ ∞ S z)
    (hR : ContDiffAt ℝ ∞ R z) (hJ : ContDiffAt ℝ ∞ J z) (hSR : 0 < S z + R z) :
    ContDiffAt ℝ ∞ (fun u => halfArg (S u) (R u) (J u)) z := by
  unfold halfArg
  exact contDiffAt_const.mul (Real.contDiff_arctan.contDiffAt.comp z
    (hJ.div (hS.add hR) hSR.ne'))

theorem contDiffAt_negHalfArg_comp {S R J : ℂ → ℝ} {z : ℂ} (hS : ContDiffAt ℝ ∞ S z)
    (hR : ContDiffAt ℝ ∞ R z) (hJ : ContDiffAt ℝ ∞ J z) (hSR : 0 < S z - R z) :
    ContDiffAt ℝ ∞ (fun u => negHalfArg (S u) (R u) (J u)) z := by
  unfold negHalfArg
  exact contDiffAt_const.sub (contDiffAt_const.mul (Real.contDiff_arctan.contDiffAt.comp z
    (hJ.div (hS.sub hR) hSR.ne')))

theorem contDiffAt_outerModulus (z : ℂ) :
    ContDiffAt ℝ ∞ (fun u : ℂ => 3 / 2 + coneProfile σ.constK u.im) z :=
  contDiffAt_const.add ((contDiff_coneProfile σ.constK_pos).contDiffAt.comp z
    imCLM.contDiff.contDiffAt)

theorem contDiffAt_angleZeroInf {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ σ.angleZeroInf z := by
  have hb := σ.contDiffAt_bridgeZero hz
  exact contDiffAt_halfArg_comp (σ.contDiffAt_outerModulus z)
    (reCLM.contDiff.contDiffAt.comp z hb) (imCLM.contDiff.contDiffAt.comp z hb)
    (by linarith [σ.outerModulus_pos z, σ.bridgeZero_re_pos hz])

theorem contDiffAt_angleOneInf {z : ℂ} (hz : z ∈ σ.domOne) :
    ContDiffAt ℝ ∞ σ.angleOneInf z := by
  have hb := σ.contDiffAt_bridgeOne hz
  exact contDiffAt_negHalfArg_comp (σ.contDiffAt_outerModulus z)
    (reCLM.contDiff.contDiffAt.comp z hb) (imCLM.contDiff.contDiffAt.comp z hb)
    (by linarith [σ.outerModulus_pos z, σ.bridgeOne_re_neg hz.1])

theorem eventually_im_pos {z : ℂ} (hz : 0 < z.im) :
    ∀ᶠ t : ℝ in 𝓝 0, 0 < (z + t).im := by
  simp only [add_im, ofReal_im, add_zero]
  exact Eventually.of_forall fun _ => hz

theorem exists_hasDerivAt_angleZeroInf {z : ℂ} (hz : 0 < z.im) :
    ∃ D : ℝ, 0 < D ∧ HasDerivAt (fun t : ℝ => σ.angleZeroInf (z + t)) D 0 := by
  set K := σ.constK
  have hK := σ.constK_pos
  set A₀ := 3 / 2 + coneProfile K z.im with hA₀
  have hA₀pos : 0 < A₀ := σ.outerModulus_pos z
  set η : ℝ → ℝ := fun t => cuspZeroHeight (z + t) with hη
  have hη' : HasDerivAt η (2 * z.re / z.im) 0 := hasDerivAt_cuspZeroHeight_horizontal z
  have hηpos : ∀ t : ℝ, 0 < η t := fun t => cuspZeroHeight_pos (by simpa using hz)
  set κ := 4 * K * η 0 / (η 0 ^ 2 + K) ^ 2 * (2 / z.im) with hκ
  have hG : HasDerivAt (fun t => coneProfile K (η t)) ((z + ((0 : ℝ) : ℂ)).re * κ) 0 := by
    refine ((hasDerivAt_coneProfile hK (η 0)).comp 0 hη').congr_deriv ?_
    simp only [ofReal_zero, add_zero, hκ]
    ring
  have hw : HasDerivAt (fun t : ℝ => (z + t).re) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).const_add z.re
  have hPd : DifferentiableAt ℝ (fun t : ℝ => outerCofactor K (3 / 2) z.im (η t) (1 / z.im))
      0 := by
    have hc : ContDiffAt ℝ ∞ (fun u : ℂ => outerCofactor K (3 / 2) u.im (cuspZeroHeight u)
        (1 / u.im)) z := by
      have h1 := contDiffAt_cuspZeroHeight hz
      have hi : ContDiffAt ℝ ∞ (fun u : ℂ => u.im) z := imCLM.contDiff.contDiffAt
      unfold outerCofactor
      have hd : (cuspZeroHeight z ^ 2 + K) * (z.im ^ 2 + K) ≠ 0 := by positivity
      have hG' := (contDiff_coneProfile hK).contDiffAt (x := z.im)
      have hG'' := (contDiff_coneProfile hK).contDiffAt (x := cuspZeroHeight z)
      exact ((((contDiffAt_const.add (hG'.comp z hi)).add (hG''.comp z h1)).pow 2).sub
        contDiffAt_const).mul (((contDiffAt_const.add (hG'.comp z hi)).sub
          (hG''.comp z h1))) |>.mul
        ((contDiffAt_const.div hi hz.ne').mul ((contDiffAt_const.mul (h1.add hi)).div
          ((h1.pow 2 |>.add contDiffAt_const).mul (hi.pow 2 |>.add contDiffAt_const)) hd))
    have hl : HasDerivAt (fun t : ℝ => z + t) 1 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add z
    have hz0 : z = z + ((0 : ℝ) : ℂ) := by simp
    have := ((hc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl
      hz0).differentiableAt
    simpa [Function.comp_def, hη] using this
  have hP0 : ∀ᶠ t : ℝ in 𝓝 0, 0 < outerCofactor K (3 / 2) z.im (η t) (1 / z.im) :=
    Eventually.of_forall fun t => outerCofactor_pos hK (Or.inl rfl) hz (hηpos t) (by positivity)
  have hH : ∀ᶠ t : ℝ in 𝓝 0, ((A₀ + coneProfile K (η t)) ^ 2 - (3 / 2 - 0) ^ 2) *
      ((3 / 2 - 0) ^ 2 - (A₀ - coneProfile K (η t)) ^ 2) =
      (z + t).re ^ 2 * outerCofactor K (3 / 2) z.im (η t) (1 / z.im) := by
    refine Eventually.of_forall fun t => ?_
    have h := outerBridge_heron hK (Or.inl rfl) (y := z.im) (η := η t) (w := (z + t).re)
      (q := 1 / z.im) (by
        have := cuspZeroHeight_sub_im (z := z + t) (by simpa using hz)
        simpa using this)
    rw [hA₀]
    linarith [h]
  have hpos : 0 < A₀ + ((twoCircle 0 (3 / 2) A₀ (coneProfile K (η 0)) (z + (0 : ℝ)).re
      (outerCofactor K (3 / 2) z.im (η 0) (1 / z.im))).re - 0) := by
    have := σ.bridgeZero_re_pos hz
    simp only [bridgeZero, outerBridge] at this
    simp only [ofReal_zero, add_zero, sub_zero, hη]
    linarith
  have h := hasDerivAt_halfArg_twoCircle' (a := 0) (b := 3 / 2) (by norm_num) hA₀pos hG hw hPd
    hP0 hH hpos
  have he : (fun t : ℝ => σ.angleZeroInf (z + t)) = fun t : ℝ => halfArg A₀
      ((twoCircle 0 (3 / 2) A₀ (coneProfile K (η t)) (z + t).re
        (outerCofactor K (3 / 2) z.im (η t) (1 / z.im))).re - 0)
      (twoCircle 0 (3 / 2) A₀ (coneProfile K (η t)) (z + t).re
        (outerCofactor K (3 / 2) z.im (η t) (1 / z.im))).im := by
    funext t
    simp only [angleZeroInf, bridgeZero, outerBridge, sub_zero, add_im, ofReal_im, add_zero, hη,
      hA₀]
    rfl
  rw [he]
  refine ⟨_, ?_, h⟩
  have hsq := Real.sqrt_pos.2 (hP0.self_of_nhds)
  have hGp := half_le_coneProfile hK (η 0)
  have hκpos : 0 < κ := by
    have := hηpos 0
    rw [hκ]
    positivity
  split_ifs with h0
  · positivity
  · have : 0 < coneProfile K (η 0) := by linarith
    have h32 : (0 : ℝ) < 3 / 2 - 0 := by norm_num
    positivity

theorem vertexOne_ne_of_domOne {z : ℂ} (hz : z ∈ σ.domOne) : z ≠ σ.vertexOne := by
  intro h
  have := σ.discOne_ne_zero hz
  rw [discOne, h, coneDisc_self] at this
  exact this rfl

theorem hasDerivAt_wallOne_horizontal {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun t : ℝ => σ.wallOne (z + t)) (deriv (fun t : ℝ => σ.wallOne (z + t)) 0) 0 ∧
      (σ.wallOne z = 0 → deriv (fun t : ℝ => σ.wallOne (z + t)) 0 < 0) := by
  have hl : HasDerivAt (fun t : ℝ => z + t) 1 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add z
  have hz0 : z = z + ((0 : ℝ) : ℂ) := by simp
  have hd : DifferentiableAt ℝ (fun t : ℝ => σ.wallOne (z + t)) 0 := by
    have := (((σ.contDiffAt_wallOne hz).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasDerivAt_of_eq (0 : ℝ) hl hz0).differentiableAt
    simpa [Function.comp_def] using this
  refine ⟨hd.hasDerivAt, fun hw0 => ?_⟩
  set w' := deriv (fun t : ℝ => σ.wallOne (z + t)) 0
  let D : ℝ → ℝ := fun t => normSq (z + t - conj σ.vertexOne)
  have hD : HasDerivAt D (2 * (z.re - σ.width)) 0 := by
    have e : D = fun t : ℝ => (z.re + t - σ.width) ^ 2 + (z.im + σ.vertexOne.im) ^ 2 := by
      funext t
      simp only [D, normSq_apply, sub_re, add_re, ofReal_re, conj_re, sub_im, add_im, ofReal_im,
        conj_im, add_zero, vertexOne_re]
      ring
    rw [e]
    have := (((hasDerivAt_id' (0 : ℝ)).const_add z.re).sub_const σ.width).pow 2 |>.add_const
      ((z.im + σ.vertexOne.im) ^ 2)
    refine this.congr_deriv ?_
    simp
  have hprod := hd.hasDerivAt.mul hD
  have hlin : HasDerivAt (fun t : ℝ => σ.wallOne (z + t) * D t)
      (-(2 * σ.vertexOne.im)) 0 := by
    have e : (fun t : ℝ => σ.wallOne (z + t) * D t) =
        fun t : ℝ => 2 * σ.vertexOne.im * (σ.width - (z.re + t)) := by
      funext t
      have := σ.im_coneDisc_vertexOne_mul (z + t)
      simp only [wallOne, discOne, D]
      rw [this]
      simp [wallSide]
    rw [e]
    have := (((hasDerivAt_id' (0 : ℝ)).const_add z.re).const_sub σ.width).const_mul
      (2 * σ.vertexOne.im)
    refine this.congr_deriv ?_
    ring
  have huniq := hprod.unique hlin
  have hw0' : σ.wallOne (z + ((0 : ℝ) : ℂ)) = 0 := by simpa using hw0
  rw [hw0', zero_mul, add_zero] at huniq
  have hDpos : 0 < D 0 := by
    simp only [D, ofReal_zero, add_zero]
    exact normSq_sub_conj_pos σ.vertexOne_im_pos hz
  have := σ.vertexOne_im_pos
  nlinarith

theorem exists_hasDerivAt_angleOneInf {z : ℂ} (hz : z ∈ σ.domOne) :
    ∃ D : ℝ, 0 < D ∧ HasDerivAt (fun t : ℝ => σ.angleOneInf (z + t)) D 0 := by
  set K := σ.constK
  have hK := σ.constK_pos
  set A₀ := 3 / 2 + coneProfile K z.im with hA₀
  have hA₀pos : 0 < A₀ := σ.outerModulus_pos z
  have hzv := σ.vertexOne_ne_of_domOne hz
  have hev : ∀ᶠ t : ℝ in 𝓝 0, z + t ∈ σ.domOne := by
    have hc : Continuous fun t : ℝ => z + t := continuous_const.add Complex.continuous_ofReal
    have := hc.continuousAt (x := 0) |>.preimage_mem_nhds (σ.isOpen_domOne.mem_nhds
      (by simpa using hz))
    exact this
  set η : ℝ → ℝ := fun t => σ.etaOne (z + t) with hη
  set ϖ := ‖coneDisc σ.vertexOne z‖ with hϖ
  set κ₁ := -(4 * z.im * σ.vertexOne.im) /
    ((1 - ϖ) ^ 2 * ϖ * normSq (z - conj σ.vertexOne)) with hκ₁
  have hη' : HasDerivAt η (σ.wallOne z * κ₁) 0 := by
    have := hasDerivAt_coneHeight_horizontal σ.vertexOne_im_pos hz.1 hzv
    exact this
  have hϖpos : 0 < ϖ := norm_pos_iff.2 (σ.discOne_ne_zero hz)
  have hϖ1 : ϖ < 1 := σ.norm_discOne_lt_one hz.1
  have hκ₁neg : κ₁ < 0 := by
    have : 0 < normSq (z - conj σ.vertexOne) := normSq_sub_conj_pos σ.vertexOne_im_pos hz.1
    have h1 : 0 < 1 - ϖ := by linarith
    have := σ.vertexOne_im_pos
    have := hz.1
    rw [hκ₁, neg_div]
    apply neg_neg_of_pos
    positivity
  set κ := 4 * K * η 0 / (η 0 ^ 2 + K) ^ 2 * κ₁ with hκ
  have hκneg : κ < 0 := by
    have : 0 < η 0 := σ.etaOne_pos (by simpa using hz.1)
    have : 0 < 4 * K * η 0 / (η 0 ^ 2 + K) ^ 2 := by positivity
    rw [hκ]
    exact mul_neg_of_pos_of_neg this hκ₁neg
  have hG : HasDerivAt (fun t => coneProfile K (η t)) (σ.wallOne (z + ((0 : ℝ) : ℂ)) * κ) 0 := by
    refine ((hasDerivAt_coneProfile hK (η 0)).comp 0 hη').congr_deriv ?_
    simp only [ofReal_zero, add_zero, hκ]
    ring
  obtain ⟨hw, hw'⟩ := σ.hasDerivAt_wallOne_horizontal hz.1
  have hPd : DifferentiableAt ℝ
      (fun t : ℝ => outerCofactor K (-(3 / 2)) z.im (η t) (σ.cofOne (z + t))) 0 := by
    have hc : ContDiffAt ℝ ∞ (fun u : ℂ => outerCofactor K (-(3 / 2)) u.im (σ.etaOne u)
        (σ.cofOne u)) z := by
      have h1 := σ.contDiffAt_etaOne hz
      have h2 := σ.contDiffAt_cofOne hz
      have hi : ContDiffAt ℝ ∞ (fun u : ℂ => u.im) z := imCLM.contDiff.contDiffAt
      have hηz := σ.etaOne_pos hz.1
      unfold outerCofactor
      have hd : (σ.etaOne z ^ 2 + K) * (z.im ^ 2 + K) ≠ 0 := by positivity
      have hG' := (contDiff_coneProfile hK).contDiffAt (x := z.im)
      have hG'' := (contDiff_coneProfile hK).contDiffAt (x := σ.etaOne z)
      exact ((((contDiffAt_const.add (hG'.comp z hi)).add (hG''.comp z h1)).pow 2).sub
        contDiffAt_const).mul (((contDiffAt_const.add (hG'.comp z hi)).sub
          (hG''.comp z h1))) |>.mul
        (h2.mul ((contDiffAt_const.mul (h1.add hi)).div
          ((h1.pow 2 |>.add contDiffAt_const).mul (hi.pow 2 |>.add contDiffAt_const)) hd))
    have hl : HasDerivAt (fun t : ℝ => z + t) 1 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add z
    have hz0 : z = z + ((0 : ℝ) : ℂ) := by simp
    have := ((hc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl
      hz0).differentiableAt
    simpa [Function.comp_def, hη] using this
  have hP0 : ∀ᶠ t : ℝ in 𝓝 0, 0 < outerCofactor K (-(3 / 2)) z.im (η t) (σ.cofOne (z + t)) := by
    filter_upwards [hev] with t ht
    have := outerCofactor_pos hK (Or.inr rfl) (y := (z + t).im) ht.1 (σ.etaOne_pos ht.1)
      (σ.cofOne_pos ht)
    simpa using this
  have hH : ∀ᶠ t : ℝ in 𝓝 0, ((A₀ + coneProfile K (η t)) ^ 2 - (-(3 / 2) - 0) ^ 2) *
      ((-(3 / 2) - 0) ^ 2 - (A₀ - coneProfile K (η t)) ^ 2) =
      σ.wallOne (z + t) ^ 2 * outerCofactor K (-(3 / 2)) z.im (η t) (σ.cofOne (z + t)) := by
    filter_upwards [hev] with t ht
    have h := outerBridge_heron hK (Or.inr rfl) (σ.etaOne_sub_im ht)
    simp only [add_im, ofReal_im, add_zero] at h
    rw [hA₀]
    linarith [h]
  have hpos : 0 < A₀ - ((twoCircle 0 (-(3 / 2)) A₀ (coneProfile K (η 0))
      (σ.wallOne (z + ((0 : ℝ) : ℂ)))
      (outerCofactor K (-(3 / 2)) z.im (η 0) (σ.cofOne (z + ((0 : ℝ) : ℂ))))).re - 0) := by
    have := σ.bridgeOne_re_neg hz.1
    simp only [bridgeOne, outerBridge] at this
    simp only [ofReal_zero, add_zero, sub_zero, hη]
    linarith
  have h := hasDerivAt_negHalfArg_twoCircle' (a := 0) (b := -(3 / 2)) (by norm_num) hA₀pos hG
    hw hPd hP0 hH hpos
  have he : (fun t : ℝ => σ.angleOneInf (z + t)) = fun t : ℝ => negHalfArg A₀
      ((twoCircle 0 (-(3 / 2)) A₀ (coneProfile K (η t)) (σ.wallOne (z + t))
        (outerCofactor K (-(3 / 2)) z.im (η t) (σ.cofOne (z + t)))).re - 0)
      (twoCircle 0 (-(3 / 2)) A₀ (coneProfile K (η t)) (σ.wallOne (z + t))
        (outerCofactor K (-(3 / 2)) z.im (η t) (σ.cofOne (z + t)))).im := by
    funext t
    simp only [angleOneInf, bridgeOne, outerBridge, sub_zero, add_im, ofReal_im, add_zero, hη,
      hA₀]
    rfl
  rw [he]
  refine ⟨_, ?_, h⟩
  have hsq := Real.sqrt_pos.2 (hP0.self_of_nhds)
  have hGp := half_le_coneProfile hK (η 0)
  split_ifs with h0
  · have hw0 : σ.wallOne z = 0 := by simpa using h0
    have := hw' hw0
    have h32 : (0 : ℝ) < |-(3 / 2) - 0| := by norm_num
    have : 0 < -deriv (fun t : ℝ => σ.wallOne (z + t)) 0 := by linarith
    have e : -(deriv (fun t : ℝ => σ.wallOne (z + t)) 0 *
        Real.sqrt (outerCofactor K (-(3 / 2)) z.im (η 0) (σ.cofOne (z + ((0 : ℝ) : ℂ)))) /
        (2 * |-(3 / 2) - 0| * A₀)) =
        (-deriv (fun t : ℝ => σ.wallOne (z + t)) 0) *
        Real.sqrt (outerCofactor K (-(3 / 2)) z.im (η 0) (σ.cofOne (z + ((0 : ℝ) : ℂ)))) /
        (2 * |-(3 / 2) - 0| * A₀) := by ring
    rw [e]
    positivity
  · have : 0 < coneProfile K (η 0) := by linarith
    have e : 2 * |-(3 / 2) - 0| * coneProfile K (η 0) * κ /
        ((-(3 / 2) - 0) * Real.sqrt (outerCofactor K (-(3 / 2)) z.im (η 0)
          (σ.cofOne (z + ((0 : ℝ) : ℂ))))) =
        2 * coneProfile K (η 0) * (-κ) / Real.sqrt (outerCofactor K (-(3 / 2)) z.im (η 0)
          (σ.cofOne (z + ((0 : ℝ) : ℂ)))) := by
      rw [show |-(3 / 2) - (0 : ℝ)| = 3 / 2 by norm_num]
      field_simp
      ring
    rw [e]
    have : 0 < -κ := by linarith
    positivity

end ConeShape

end GC.Seifert

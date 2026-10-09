import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldBridges

/-!
# The bridges of a cone shape

Lane A4, tier 2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §4).
For a `ConeShape` `σ` with `K = σ.constK`, `ω = coneDisc v₁ z`, `r = |ω|`:

* `σ.bridgeOne` (wall 1, `x = W`, between the cone `v₁` and the cusp `∞`) is the outer bridge
  with `|u| = 3/2 + G y`, `|u + 3/2| = G η₁`, `η₁ = coneHeight v₁`, wall function `Im ω` and
  cofactor `σ.cofOne`, from `coneHeight_sub_im`; it is defined and smooth on `σ.domOne`
  (`0 < r + Re ω`: the upper half-plane minus the closed vertical ray below `v₁`), and
  `bridgeOne ∘ refl 1 = conj ∘ bridgeOne` there;
* for the `(p, ⊤, ⊤)` shapes (`θ₂ = 0`, the cusp at `0`), `σ.bridgeZero` (wall 0) is the outer
  bridge with `|u - 3/2| = G η₀`, `η₀ = |z|²/Im z`, wall function `x` and cofactor `1/y`
  (`η₀ - y = x²/y`), smooth on the whole upper half-plane and odd under `z ↦ -z̄`, and
  `σ.bridgeTwo` (wall 2) is the inner bridge with `|u - 3/2| = G η₀`, `|u + 3/2| = G η₁`, wall
  function `-Im(e^{-iθ₁} ω)` and cofactor `2K/((r + Re(e^{-iθ₁}ω))(1 - r)²)`, from
  `coneHeight_mul_cuspZero_sub` and `constK_eq_normSq`, odd under the circle reflection.
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

namespace ConeShape

variable (σ : ConeShape)

def discOne (z : ℂ) : ℂ := coneDisc σ.vertexOne z

def etaOne (z : ℂ) : ℝ := coneHeight σ.vertexOne z

def wallOne (z : ℂ) : ℝ := (σ.discOne z).im

def cofOne (z : ℂ) : ℝ :=
  2 * σ.vertexOne.im * (1 - ‖σ.discOne z‖ ^ 2) /
    ((‖σ.discOne z‖ + (σ.discOne z).re) * (1 - ‖σ.discOne z‖) ^ 2 *
      ((1 - (σ.discOne z).re) ^ 2 + (σ.discOne z).im ^ 2))

def domOne : Set ℂ := {z | 0 < z.im ∧ 0 < ‖σ.discOne z‖ + (σ.discOne z).re}

def bridgeOne (z : ℂ) : ℂ :=
  outerBridge σ.constK (-(3 / 2)) z.im (σ.etaOne z) (σ.wallOne z) (σ.cofOne z)

theorem discOne_ne_zero {z : ℂ} (hz : z ∈ σ.domOne) : σ.discOne z ≠ 0 := by
  intro h
  have := hz.2
  rw [h] at this
  simp at this

theorem norm_discOne_lt_one {z : ℂ} (hz : 0 < z.im) : ‖σ.discOne z‖ < 1 :=
  norm_coneDisc_lt_one σ.vertexOne_im_pos hz

theorem etaOne_pos {z : ℂ} (hz : 0 < z.im) : 0 < σ.etaOne z :=
  coneHeight_pos σ.vertexOne_im_pos hz

theorem etaOne_sub_im {z : ℂ} (hz : z ∈ σ.domOne) :
    σ.etaOne z - z.im = σ.wallOne z ^ 2 * σ.cofOne z := by
  rw [etaOne, coneHeight_sub_im σ.vertexOne_im_pos hz.1 hz.2, wallOne, cofOne, discOne]
  ring

theorem cofOne_pos {z : ℂ} (hz : z ∈ σ.domOne) : 0 < σ.cofOne z := by
  have h1 := σ.norm_discOne_lt_one hz.1
  have h2 := σ.vertexOne_im_pos
  have h3 := hz.2
  have h4 : 0 < 1 - ‖σ.discOne z‖ := by linarith
  have h5 : 0 < 1 - ‖σ.discOne z‖ ^ 2 := by nlinarith [norm_nonneg (σ.discOne z)]
  have h6 : 0 < (1 - (σ.discOne z).re) ^ 2 + (σ.discOne z).im ^ 2 := by
    have : (σ.discOne z).re < 1 := lt_of_le_of_lt (Complex.re_le_norm _) h1
    have : 0 < (1 - (σ.discOne z).re) ^ 2 := by nlinarith
    positivity
  unfold cofOne
  positivity

theorem contDiffAt_discOne {z : ℂ} (hz : 0 < z.im) : ContDiffAt ℝ ∞ σ.discOne z :=
  (contDiffAt_coneDisc σ.vertexOne_im_pos hz).restrict_scalars ℝ

theorem contDiffAt_norm_discOne {z : ℂ} (hz : z ∈ σ.domOne) :
    ContDiffAt ℝ ∞ (fun u => ‖σ.discOne u‖) z :=
  (σ.contDiffAt_discOne hz.1).norm ℝ (σ.discOne_ne_zero hz)

theorem contDiffAt_re_discOne {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (fun u => (σ.discOne u).re) z :=
  reCLM.contDiff.contDiffAt.comp z (σ.contDiffAt_discOne hz)

theorem contDiffAt_im_discOne {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (fun u => (σ.discOne u).im) z :=
  imCLM.contDiff.contDiffAt.comp z (σ.contDiffAt_discOne hz)

theorem contDiffAt_etaOne {z : ℂ} (hz : z ∈ σ.domOne) : ContDiffAt ℝ ∞ σ.etaOne z := by
  have h := σ.contDiffAt_norm_discOne hz
  have h1 : 1 - ‖σ.discOne z‖ ≠ 0 := (sub_pos.2 (σ.norm_discOne_lt_one hz.1)).ne'
  exact (contDiffAt_const.mul (contDiffAt_const.add h)).div (contDiffAt_const.sub h) h1

theorem contDiffAt_wallOne {z : ℂ} (hz : 0 < z.im) : ContDiffAt ℝ ∞ σ.wallOne z :=
  σ.contDiffAt_im_discOne hz

theorem contDiffAt_cofOne {z : ℂ} (hz : z ∈ σ.domOne) : ContDiffAt ℝ ∞ σ.cofOne z := by
  have hn := σ.contDiffAt_norm_discOne hz
  have hre := σ.contDiffAt_re_discOne hz.1
  have him := σ.contDiffAt_im_discOne hz.1
  have hpos := σ.cofOne_pos hz
  have h1 := σ.norm_discOne_lt_one hz.1
  have hd : (‖σ.discOne z‖ + (σ.discOne z).re) * (1 - ‖σ.discOne z‖) ^ 2 *
      ((1 - (σ.discOne z).re) ^ 2 + (σ.discOne z).im ^ 2) ≠ 0 := by
    have h6 : 0 < (1 - (σ.discOne z).re) ^ 2 + (σ.discOne z).im ^ 2 := by
      have : (σ.discOne z).re < 1 := lt_of_le_of_lt (Complex.re_le_norm _) h1
      have : 0 < (1 - (σ.discOne z).re) ^ 2 := by nlinarith
      positivity
    have h4 : 0 < 1 - ‖σ.discOne z‖ := by linarith
    have := hz.2
    positivity
  exact (contDiffAt_const.mul (contDiffAt_const.sub (hn.pow 2))).div
    (((hn.add hre).mul ((contDiffAt_const.sub hn).pow 2)).mul
      (((contDiffAt_const.sub hre).pow 2).add (him.pow 2))) hd

theorem contDiffAt_bridgeOne {z : ℂ} (hz : z ∈ σ.domOne) : ContDiffAt ℝ ∞ σ.bridgeOne z :=
  contDiffAt_outerBridge σ.constK_pos (Or.inr rfl) contDiffAt_im (σ.contDiffAt_etaOne hz)
    (σ.contDiffAt_wallOne hz.1) (σ.contDiffAt_cofOne hz) hz.1 (σ.etaOne_pos hz.1)
    (σ.cofOne_pos hz)
where
  contDiffAt_im : ContDiffAt ℝ ∞ (fun u : ℂ => u.im) z := imCLM.contDiff.contDiffAt

theorem isOpen_domOne : IsOpen σ.domOne := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hc : ContinuousAt (fun u => ‖σ.discOne u‖ + (σ.discOne u).re) z :=
    ((σ.contDiffAt_norm_discOne hz).add (σ.contDiffAt_re_discOne hz.1)).continuousAt
  have h1 : ∀ᶠ u in nhds z, 0 < u.im :=
    Complex.continuous_im.continuousAt.eventually (lt_mem_nhds hz.1)
  have h2 : ∀ᶠ u in nhds z, 0 < ‖σ.discOne u‖ + (σ.discOne u).re :=
    hc.eventually (lt_mem_nhds hz.2)
  filter_upwards [h1, h2] with u hu1 hu2
  exact ⟨hu1, hu2⟩

theorem discOne_refl_one (z : ℂ) : σ.discOne (σ.refl 1 z) = conj (σ.discOne z) :=
  σ.coneDisc_vertexOne_refl_one z

theorem refl_one_im (z : ℂ) : (σ.refl 1 z).im = z.im := by
  simp [refl]

theorem refl_one_mem_domOne {z : ℂ} (hz : z ∈ σ.domOne) : σ.refl 1 z ∈ σ.domOne := by
  refine ⟨by rw [refl_one_im]; exact hz.1, ?_⟩
  rw [discOne_refl_one, Complex.norm_conj, conj_re]
  exact hz.2

theorem bridgeOne_refl_one (z : ℂ) : σ.bridgeOne (σ.refl 1 z) = conj (σ.bridgeOne z) := by
  have e1 : σ.etaOne (σ.refl 1 z) = σ.etaOne z := by
    simp only [etaOne, coneHeight, σ.coneDisc_vertexOne_refl_one, Complex.norm_conj]
  have e2 : σ.wallOne (σ.refl 1 z) = -σ.wallOne z := by
    simp [wallOne, discOne_refl_one]
  have e3 : σ.cofOne (σ.refl 1 z) = σ.cofOne z := by
    simp only [cofOne, discOne_refl_one, Complex.norm_conj, conj_re, conj_im, neg_sq]
  rw [bridgeOne, bridgeOne, refl_one_im, e1, e2, e3, outerBridge_neg]

theorem norm_bridgeOne {z : ℂ} (hz : z ∈ σ.domOne) :
    ‖σ.bridgeOne z‖ = 3 / 2 + coneProfile σ.constK z.im :=
  norm_outerBridge σ.constK_pos (Or.inr rfl) hz.1 (σ.etaOne_pos hz.1) (σ.cofOne_pos hz)
    (σ.etaOne_sub_im hz)

theorem norm_bridgeOne_add {z : ℂ} (hz : z ∈ σ.domOne) :
    ‖σ.bridgeOne z + 3 / 2‖ = coneProfile σ.constK (σ.etaOne z) := by
  have h := norm_outerBridge_sub σ.constK_pos (Or.inr rfl) hz.1 (σ.etaOne_pos hz.1)
    (σ.cofOne_pos hz) (σ.etaOne_sub_im hz)
  simpa [bridgeOne, sub_neg_eq_add] using h

theorem bridgeOne_re_neg {z : ℂ} (hz : 0 < z.im) : (σ.bridgeOne z).re < 0 := by
  have h := outerBridge_re_mul_pos σ.constK_pos (Or.inr rfl) (η := σ.etaOne z)
    (w := σ.wallOne z) (q := σ.cofOne z) hz
  rw [bridgeOne]
  linarith

theorem bridgeOne_im_pos {z : ℂ} (hz : z ∈ σ.domOne) (hw : 0 < σ.wallOne z) :
    0 < (σ.bridgeOne z).im :=
  outerBridge_im_pos σ.constK_pos (Or.inr rfl) hz.1 (σ.etaOne_pos hz.1) (σ.cofOne_pos hz) hw

section Cusp

def bridgeZero (z : ℂ) : ℂ :=
  outerBridge σ.constK (3 / 2) z.im (cuspZeroHeight z) z.re (1 / z.im)

theorem cuspZeroHeight_pos {z : ℂ} (hz : 0 < z.im) : 0 < cuspZeroHeight z := by
  have : 0 < normSq z := normSq_pos.2 (fun h => by rw [h] at hz; simp at hz)
  unfold cuspZeroHeight
  positivity

theorem cuspZeroHeight_sub_im {z : ℂ} (hz : 0 < z.im) :
    cuspZeroHeight z - z.im = z.re ^ 2 * (1 / z.im) := by
  unfold cuspZeroHeight
  rw [normSq_apply]
  field_simp
  ring

theorem contDiffAt_cuspZeroHeight {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ cuspZeroHeight z := by
  have h1 : ContDiffAt ℝ ∞ (fun u : ℂ => normSq u) z := by
    have : (fun u : ℂ => normSq u) = fun u => u.re * u.re + u.im * u.im := by
      funext u
      rw [normSq_apply]
    rw [this]
    exact ((reCLM.contDiff.contDiffAt.mul reCLM.contDiff.contDiffAt).add
      (imCLM.contDiff.contDiffAt.mul imCLM.contDiff.contDiffAt))
  exact h1.div imCLM.contDiff.contDiffAt hz.ne'

theorem contDiffAt_bridgeZero {z : ℂ} (hz : 0 < z.im) : ContDiffAt ℝ ∞ σ.bridgeZero z :=
  contDiffAt_outerBridge σ.constK_pos (Or.inl rfl) imCLM.contDiff.contDiffAt
    (contDiffAt_cuspZeroHeight hz) reCLM.contDiff.contDiffAt
    (contDiffAt_const.div imCLM.contDiff.contDiffAt hz.ne') hz (cuspZeroHeight_pos hz)
    (by simpa using hz)

theorem bridgeZero_refl_zero (z : ℂ) : σ.bridgeZero (σ.refl 0 z) = conj (σ.bridgeZero z) := by
  have e1 : cuspZeroHeight (σ.refl 0 z) = cuspZeroHeight z := by
    simp [cuspZeroHeight, refl, normSq_apply]
  have e2 : (σ.refl 0 z).im = z.im := by simp [refl]
  have e3 : (σ.refl 0 z).re = -z.re := by simp [refl]
  rw [bridgeZero, bridgeZero, e1, e2, e3, outerBridge_neg]

theorem norm_bridgeZero_sub {z : ℂ} (hz : 0 < z.im) :
    ‖σ.bridgeZero z - 3 / 2‖ = coneProfile σ.constK (cuspZeroHeight z) := by
  have h := norm_outerBridge_sub σ.constK_pos (Or.inl rfl) hz (cuspZeroHeight_pos hz)
    (by simpa using hz) (cuspZeroHeight_sub_im hz)
  simpa [bridgeZero] using h

theorem norm_bridgeZero {z : ℂ} (hz : 0 < z.im) :
    ‖σ.bridgeZero z‖ = 3 / 2 + coneProfile σ.constK z.im :=
  norm_outerBridge σ.constK_pos (Or.inl rfl) hz (cuspZeroHeight_pos hz) (by simpa using hz)
    (cuspZeroHeight_sub_im hz)

theorem bridgeZero_re_pos {z : ℂ} (hz : 0 < z.im) : 0 < (σ.bridgeZero z).re := by
  have h := outerBridge_re_mul_pos σ.constK_pos (Or.inl rfl) (η := cuspZeroHeight z)
    (w := z.re) (q := 1 / z.im) hz
  rw [bridgeZero]
  linarith

def wallTwo (z : ℂ) : ℝ := -(exp (-(σ.θ₁ * I)) * σ.discOne z).im

def cofTwo (z : ℂ) : ℝ :=
  2 * σ.constK / ((‖σ.discOne z‖ + (exp (-(σ.θ₁ * I)) * σ.discOne z).re) *
    (1 - ‖σ.discOne z‖) ^ 2)

def domTwo : Set ℂ :=
  {z | 0 < z.im ∧ 0 < ‖σ.discOne z‖ + (exp (-(σ.θ₁ * I)) * σ.discOne z).re}

def bridgeTwo (z : ℂ) : ℂ :=
  innerBridge σ.constK (cuspZeroHeight z) (σ.etaOne z) (σ.wallTwo z) (σ.cofTwo z)

theorem discOne_ne_zero_of_domTwo {z : ℂ} (hz : z ∈ σ.domTwo) : σ.discOne z ≠ 0 := by
  intro h
  have := hz.2
  rw [h] at this
  simp at this

theorem cofTwo_pos {z : ℂ} (hz : z ∈ σ.domTwo) : 0 < σ.cofTwo z := by
  have h1 := σ.norm_discOne_lt_one hz.1
  have h4 : 0 < 1 - ‖σ.discOne z‖ := by linarith
  have := hz.2
  have := σ.constK_pos
  unfold cofTwo
  positivity

theorem etaOne_mul_cuspZeroHeight_sub (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.domTwo) :
    σ.etaOne z * cuspZeroHeight z - σ.constK = σ.wallTwo z ^ 2 * σ.cofTwo z := by
  have h := coneHeight_mul_cuspZero_sub σ.vertexOne_im_pos hz.1
    (by rw [σ.conj_div_vertexOne hθ]; exact hz.2)
  rw [σ.conj_div_vertexOne hθ, ← σ.constK_eq_normSq hθ] at h
  rw [etaOne, h, wallTwo, cofTwo, discOne, neg_sq]
  ring

theorem norm_bridgeTwo_sub (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.domTwo) :
    ‖σ.bridgeTwo z - 3 / 2‖ = coneProfile σ.constK (cuspZeroHeight z) :=
  norm_innerBridge_sub σ.constK_pos (cuspZeroHeight_pos hz.1) (σ.etaOne_pos hz.1)
    (σ.cofTwo_pos hz) (σ.etaOne_mul_cuspZeroHeight_sub hθ hz)

theorem norm_bridgeTwo_add (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.domTwo) :
    ‖σ.bridgeTwo z + 3 / 2‖ = coneProfile σ.constK (σ.etaOne z) :=
  norm_innerBridge_add σ.constK_pos (cuspZeroHeight_pos hz.1) (σ.etaOne_pos hz.1)
    (σ.cofTwo_pos hz) (σ.etaOne_mul_cuspZeroHeight_sub hθ hz)

theorem norm_bridgeTwo_lt_two (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.domTwo) :
    ‖σ.bridgeTwo z‖ < 2 :=
  norm_innerBridge_lt_two σ.constK_pos (cuspZeroHeight_pos hz.1) (σ.etaOne_pos hz.1)
    (σ.cofTwo_pos hz) (σ.etaOne_mul_cuspZeroHeight_sub hθ hz)

theorem contDiffAt_bridgeTwo {z : ℂ} (hz : z ∈ σ.domTwo) : ContDiffAt ℝ ∞ σ.bridgeTwo z := by
  have hd1 := σ.contDiffAt_discOne hz.1
  have hne := σ.discOne_ne_zero_of_domTwo hz
  have hn : ContDiffAt ℝ ∞ (fun u => ‖σ.discOne u‖) z := hd1.norm ℝ hne
  have hrot : ContDiffAt ℝ ∞ (fun u => exp (-(σ.θ₁ * I)) * σ.discOne u) z :=
    contDiffAt_const.mul hd1
  have hre : ContDiffAt ℝ ∞ (fun u => (exp (-(σ.θ₁ * I)) * σ.discOne u).re) z :=
    reCLM.contDiff.contDiffAt.comp z hrot
  have him : ContDiffAt ℝ ∞ (fun u => (exp (-(σ.θ₁ * I)) * σ.discOne u).im) z :=
    imCLM.contDiff.contDiffAt.comp z hrot
  have h1 := σ.norm_discOne_lt_one hz.1
  have hden : (‖σ.discOne z‖ + (exp (-(σ.θ₁ * I)) * σ.discOne z).re) *
      (1 - ‖σ.discOne z‖) ^ 2 ≠ 0 := by
    have h4 : 0 < 1 - ‖σ.discOne z‖ := by linarith
    have := hz.2
    positivity
  have hdomOne_eta : ContDiffAt ℝ ∞ σ.etaOne z := by
    have h1' : 1 - ‖σ.discOne z‖ ≠ 0 := (sub_pos.2 h1).ne'
    exact (contDiffAt_const.mul (contDiffAt_const.add hn)).div (contDiffAt_const.sub hn) h1'
  exact contDiffAt_innerBridge σ.constK_pos (contDiffAt_cuspZeroHeight hz.1) hdomOne_eta
    him.neg (contDiffAt_const.div ((hn.add hre).mul ((contDiffAt_const.sub hn).pow 2)) hden)
    (cuspZeroHeight_pos hz.1) (σ.etaOne_pos hz.1) (σ.cofTwo_pos hz)

theorem refl_two_eq_cusp (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im) :
    σ.refl 2 z = conj z / (4 * conj z - 1) := by
  have h1 : 4 * conj z - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have h2 : conj z - 1 / 4 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  simp only [refl, σ.cusp_centre hθ]
  push_cast
  field_simp
  ring

theorem cuspZeroHeight_refl_two (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im) :
    cuspZeroHeight (σ.refl 2 z) = cuspZeroHeight z := by
  rw [σ.refl_two_eq_cusp hθ hz]
  have h1 : 4 * conj z - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hn : normSq (4 * conj z - 1) ≠ 0 := normSq_eq_zero.not.2 h1
  have him : (conj z / (4 * conj z - 1)).im = z.im / normSq (4 * conj z - 1) := by
    rw [div_im]
    simp [normSq_apply]
    field_simp
    ring
  unfold cuspZeroHeight
  rw [him, map_div₀, Complex.normSq_conj]
  field_simp

theorem bridgeTwo_refl_two (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im) :
    σ.bridgeTwo (σ.refl 2 z) = conj (σ.bridgeTwo z) := by
  have hc : z ≠ σ.centre := sub_ne_zero.1 (σ.centre_ne hz)
  have hd : σ.discOne (σ.refl 2 z) = exp (2 * σ.θ₁ * I) * conj (σ.discOne z) :=
    σ.coneDisc_vertexOne_refl_two hc
  have hrot : exp (-(σ.θ₁ * I)) * σ.discOne (σ.refl 2 z) =
      conj (exp (-(σ.θ₁ * I)) * σ.discOne z) := by
    rw [hd, map_mul, ← Complex.exp_conj, ← mul_assoc, ← Complex.exp_add]
    congr 2
    simp
    ring
  have hnorm : ‖σ.discOne (σ.refl 2 z)‖ = ‖σ.discOne z‖ := by
    rw [hd, norm_mul, Complex.norm_conj, Complex.norm_exp]
    simp
  have e1 : σ.etaOne (σ.refl 2 z) = σ.etaOne z := by
    simp only [etaOne, coneHeight]
    rw [← discOne, ← discOne, hnorm]
  have e2 : σ.wallTwo (σ.refl 2 z) = -σ.wallTwo z := by
    simp only [wallTwo, hrot, conj_im, neg_neg]
  have e3 : σ.cofTwo (σ.refl 2 z) = σ.cofTwo z := by
    simp only [cofTwo, hrot, hnorm, conj_re]
  rw [bridgeTwo, bridgeTwo, σ.cuspZeroHeight_refl_two hθ hz, e1, e2, e3, innerBridge_neg]

end Cusp

end ConeShape

end GC.Seifert

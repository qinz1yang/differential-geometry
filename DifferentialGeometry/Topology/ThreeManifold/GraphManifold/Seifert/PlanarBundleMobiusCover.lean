import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClassicalInputs
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Blocks
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarModels

/-!
# The double cover of a Möbius base by the annulus

Chapter 6, lane MD5, tier T4 of the P1 Morse-decomposition plan
(`docs/geometrization/handoffs/20261003-survey-p1-morse-decomposition.md`, §3, errata after
review 8), first file. A circle fibration over a Möbius base is studied on the annulus that
double covers the base, because the gluing of fibre coordinates needs an orientation of the base.

The annulus `annulus = {1/2 ≤ ‖w‖ ≤ 3}` (`planarModel 2`, the surface `annulusSurface`) maps to
the Möbius model by `model w = modelOf (w / ‖w‖) ((4‖w‖ - 7) / 5)`, where `modelOf z s` is the
formula of `mobiusPoint` with `s = 2t - 1`; `unwrap z t = (1/2 + 5t/2) z` gives
`model (unwrap z t) = mobiusPoint z t` (`model_unwrap`) and turns `mobiusDeck` into the involution
`deck w = -((7/2 - ‖w‖)/‖w‖) w` (`unwrap_symm`). The fibres of `model` on the annulus are exactly
`{w, deck w}` (`eq_or_eq_deck_of_model_eq`: the first two coordinates give `R z²` with
`R = 2 + s re z ≥ 1`, hence `R` and `z²`; the third gives `s im z`). On the half annulus
`re (w z̄₀) > 0` the explicit map `localInv z₀` inverts `model`, recovering `z = z₀ v` from
`v² + 1 = 2 (re v) v` and `s = re z (R - 2) + im z X₂` without square roots (`localInv_model`), and
it is smooth there (`contDiffAt_localInv`).

For a smooth embedding `E` of a compact surface `B` onto `mobiusModel`, `cover = E⁻¹ ∘ model` is
a smooth map `annulusSurface → B` (`contMDiff_cover`), surjective, with fibres `{x, annDeck x}`
(`cover_eq_cover_iff`); on every half annulus `sheet z₀` it is injective with open image and has
the smooth local inverse `localSection z₀` (`contMDiffOn_localSection`).
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

namespace MobiusCover

def modelOf (z : ℂ) (s : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[(2 + s * z.re) * (z ^ 2).re, (2 + s * z.re) * (z ^ 2).im, s * z.im]

def dir (w : ℂ) : ℂ := ‖w‖⁻¹ • w

def ht (w : ℂ) : ℝ := (4 * ‖w‖ - 7) / 5

def model (w : ℂ) : EuclideanSpace ℝ (Fin 3) := modelOf (dir w) (ht w)

def deck (w : ℂ) : ℂ := -(((7 / 2 - ‖w‖) / ‖w‖) • w)

def unwrap (z : Circle) (t : unitInterval) : ℂ := (1 / 2 + 5 / 2 * (t : ℝ)) • (z : ℂ)

def annulus : Set ℂ := {w | 1 / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 3}

theorem modelOf_apply_zero (z : ℂ) (s : ℝ) :
    modelOf z s 0 = (2 + s * z.re) * (z ^ 2).re := rfl

theorem modelOf_apply_one (z : ℂ) (s : ℝ) :
    modelOf z s 1 = (2 + s * z.re) * (z ^ 2).im := rfl

theorem modelOf_apply_two (z : ℂ) (s : ℝ) : modelOf z s 2 = s * z.im := rfl

theorem mobiusPoint_eq_modelOf (z : Circle) (t : unitInterval) :
    mobiusPoint z t = modelOf z (2 * t - 1) := rfl

theorem norm_dir {w : ℂ} (hw : w ≠ 0) : ‖dir w‖ = 1 := by
  rw [dir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]

theorem norm_smul_dir (w : ℂ) : ‖w‖ • dir w = w := by
  rcases eq_or_ne w 0 with h | h
  · simp [h, dir]
  · rw [dir, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]

theorem re_sq_add_im_sq {z : ℂ} (hz : ‖z‖ = 1) : z.re ^ 2 + z.im ^ 2 = 1 := by
  have h := Complex.sq_norm z
  rw [hz, Complex.normSq_apply] at h
  nlinarith

theorem abs_re_le {z : ℂ} (hz : ‖z‖ = 1) : |z.re| ≤ 1 := by
  rw [← hz]
  exact Complex.abs_re_le_norm z

theorem modelOf_neg (z : ℂ) (s : ℝ) : modelOf (-z) (-s) = modelOf z s := by
  ext i
  fin_cases i <;> simp [modelOf]

theorem eq_of_modelOf_eq {z z' : ℂ} {s s' : ℝ} (hz : ‖z‖ = 1) (hz' : ‖z'‖ = 1) (hs : |s| ≤ 1)
    (hs' : |s'| ≤ 1) (h : modelOf z s = modelOf z' s') :
    (z' = z ∧ s' = s) ∨ (z' = -z ∧ s' = -s) := by
  have h0 := congrArg (fun X : EuclideanSpace ℝ (Fin 3) => X 0) h
  have h1 := congrArg (fun X : EuclideanSpace ℝ (Fin 3) => X 1) h
  have h2 := congrArg (fun X : EuclideanSpace ℝ (Fin 3) => X 2) h
  simp only [modelOf_apply_zero, modelOf_apply_one, modelOf_apply_two] at h0 h1 h2
  have hzz := re_sq_add_im_sq hz
  have hzz' := re_sq_add_im_sq hz'
  have hR : 1 ≤ 2 + s * z.re := by
    have h3 : |s * z.re| ≤ 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg s, abs_nonneg z.re, abs_re_le hz]
    linarith [neg_abs_le (s * z.re)]
  have hR' : 1 ≤ 2 + s' * z'.re := by
    have h3 : |s' * z'.re| ≤ 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg s', abs_nonneg z'.re, abs_re_le hz']
    linarith [neg_abs_le (s' * z'.re)]
  have hc : (((2 + s * z.re : ℝ)) : ℂ) * z ^ 2 = (((2 + s' * z'.re : ℝ)) : ℂ) * z' ^ 2 := by
    apply Complex.ext
    · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        using h0
    · simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        using h1
  have hn := congrArg norm hc
  simp only [norm_mul, norm_pow, hz, hz', one_pow, mul_one, Complex.norm_real,
    Real.norm_eq_abs] at hn
  rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at hn
  have hsr : s * z.re = s' * z'.re := by linarith
  rw [hn] at hc
  have hz2 : z ^ 2 = z' ^ 2 :=
    mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (by linarith)) hc
  have hfac : (z' - z) * (z' + z) = 0 := by linear_combination -hz2
  rcases mul_eq_zero.mp hfac with h3 | h3
  · left
    have e : z' = z := sub_eq_zero.mp h3
    subst e
    exact ⟨rfl, by linear_combination (-z'.re) * hsr + (-z'.im) * h2 + (s - s') * hzz⟩
  · right
    have e : z' = -z := eq_neg_of_add_eq_zero_left h3
    subst e
    simp only [Complex.neg_re, Complex.neg_im] at hsr h2 hzz'
    refine ⟨by ring, ?_⟩
    linear_combination (z.re) * hsr + (z.im) * h2 - (s' + s) * hzz'

theorem ne_zero_of_mem_annulus {w : ℂ} (hw : w ∈ annulus) : w ≠ 0 := by
  intro h
  have := hw.1
  rw [h, norm_zero] at this
  norm_num at this

theorem norm_pos_of_mem_annulus {w : ℂ} (hw : w ∈ annulus) : 0 < ‖w‖ := by
  linarith [hw.1]

theorem abs_ht_le {w : ℂ} (hw : w ∈ annulus) : |ht w| ≤ 1 := by
  rw [ht, abs_le]
  constructor <;> linarith [hw.1, hw.2]

theorem norm_eq_of_ht (w : ℂ) : ‖w‖ = (5 * ht w + 7) / 4 := by
  rw [ht]
  ring

theorem deck_eq_smul_dir (w : ℂ) : deck w = -((7 / 2 - ‖w‖) • dir w) := by
  rw [deck, dir, smul_smul, div_eq_mul_inv]

theorem norm_deck {w : ℂ} (hw : w ∈ annulus) : ‖deck w‖ = 7 / 2 - ‖w‖ := by
  rw [deck_eq_smul_dir w, norm_neg, norm_smul,
    norm_dir (ne_zero_of_mem_annulus hw), mul_one, Real.norm_eq_abs, abs_of_pos]
  linarith [hw.2]

theorem deck_mem_annulus {w : ℂ} (hw : w ∈ annulus) : deck w ∈ annulus := by
  rw [annulus, mem_ofPred_eq, norm_deck hw]
  constructor <;> linarith [hw.1, hw.2]

theorem dir_deck {w : ℂ} (hw : w ∈ annulus) : dir (deck w) = -dir w := by
  rw [dir, norm_deck hw, deck_eq_smul_dir w, smul_neg, smul_smul,
    inv_mul_cancel₀ (by linarith [hw.2]), one_smul]

theorem ht_deck {w : ℂ} (hw : w ∈ annulus) : ht (deck w) = -ht w := by
  rw [ht, ht, norm_deck hw]
  ring

theorem model_deck {w : ℂ} (hw : w ∈ annulus) : model (deck w) = model w := by
  rw [model, model, dir_deck hw, ht_deck hw, modelOf_neg]

theorem deck_deck {w : ℂ} (hw : w ∈ annulus) : deck (deck w) = w := by
  have hd := deck_mem_annulus hw
  rw [deck_eq_smul_dir (deck w), norm_deck hw, dir_deck hw]
  rw [show (7 / 2 - (7 / 2 - ‖w‖) : ℝ) = ‖w‖ by ring, smul_neg, neg_neg, norm_smul_dir]

theorem eq_or_eq_deck_of_model_eq {w w' : ℂ} (hw : w ∈ annulus) (hw' : w' ∈ annulus)
    (h : model w = model w') : w' = w ∨ w' = deck w := by
  rcases eq_of_modelOf_eq (norm_dir (ne_zero_of_mem_annulus hw))
    (norm_dir (ne_zero_of_mem_annulus hw')) (abs_ht_le hw) (abs_ht_le hw') h with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [← norm_smul_dir w', ← norm_smul_dir w, h1, norm_eq_of_ht w', norm_eq_of_ht w, h2]
  · right
    rw [← norm_smul_dir w', deck_eq_smul_dir w, h1,
      norm_eq_of_ht w', h2, smul_neg]
    congr 2
    rw [norm_eq_of_ht w]
    ring

theorem norm_unwrap (z : Circle) (t : unitInterval) : ‖unwrap z t‖ = 1 / 2 + 5 / 2 * (t : ℝ) := by
  rw [unwrap, norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs, abs_of_pos]
  linarith [t.2.1]

theorem unwrap_mem_annulus (z : Circle) (t : unitInterval) : unwrap z t ∈ annulus := by
  rw [annulus, mem_ofPred_eq, norm_unwrap]
  constructor <;> linarith [t.2.1, t.2.2]

theorem dir_unwrap (z : Circle) (t : unitInterval) : dir (unwrap z t) = z := by
  rw [dir, norm_unwrap, unwrap, smul_smul, inv_mul_cancel₀ (by linarith [t.2.1]), one_smul]

theorem ht_unwrap (z : Circle) (t : unitInterval) : ht (unwrap z t) = 2 * (t : ℝ) - 1 := by
  rw [ht, norm_unwrap]
  ring

theorem model_unwrap (z : Circle) (t : unitInterval) : model (unwrap z t) = mobiusPoint z t := by
  rw [model, dir_unwrap, ht_unwrap, mobiusPoint_eq_modelOf]

theorem unwrap_symm (z : Circle) (t : unitInterval) :
    unwrap (-z) (unitInterval.symm t) = deck (unwrap z t) := by
  rw [deck_eq_smul_dir (unwrap z t), dir_unwrap,
    norm_unwrap, unwrap, unitInterval.coe_symm_eq, Circle.coe_neg, smul_neg]
  congr 2
  ring

theorem model_mem_mobiusModel {w : ℂ} (hw : w ∈ annulus) : model w ∈ mobiusModel := by
  have hd : dir w ∈ Submonoid.unitSphere ℂ := by
    change dir w ∈ Metric.sphere (0 : ℂ) 1
    exact mem_sphere_zero_iff_norm.mpr (norm_dir (ne_zero_of_mem_annulus hw))
  have ht1 : (ht w + 1) / 2 ∈ unitInterval := by
    have := abs_le.mp (abs_ht_le hw)
    constructor <;> linarith
  refine ⟨(⟨dir w, hd⟩, ⟨(ht w + 1) / 2, ht1⟩), ?_⟩
  change mobiusPoint _ _ = _
  rw [mobiusPoint_eq_modelOf, model]
  congr 1
  change 2 * ((ht w + 1) / 2) - 1 = ht w
  ring

theorem mobiusModel_subset : mobiusModel ⊆ model '' annulus := by
  rintro _ ⟨⟨z, t⟩, rfl⟩
  exact ⟨unwrap z t, unwrap_mem_annulus z t, model_unwrap z t⟩

def planeOf (X : EuclideanSpace ℝ (Fin 3)) : ℂ := (X 0 : ℂ) + (X 1 : ℂ) * Complex.I

def localInv (z₀ : ℂ) (X : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  let u := ‖planeOf X‖⁻¹ • planeOf X
  let a := u * conj z₀ ^ 2 + 1
  let z := z₀ * (‖a‖⁻¹ • a)
  ((5 * (z.re * (‖planeOf X‖ - 2) + z.im * X 2) + 7) / 4) • z

theorem planeOf_modelOf (z : ℂ) (s : ℝ) : planeOf (modelOf z s) = (2 + s * z.re) • z ^ 2 := by
  apply Complex.ext <;> simp [planeOf, modelOf_apply_zero, modelOf_apply_one]

theorem one_le_of_abs {z : ℂ} {s : ℝ} (hz : ‖z‖ = 1) (hs : |s| ≤ 1) : 1 ≤ 2 + s * z.re := by
  have h3 : |s * z.re| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg s, abs_nonneg z.re, abs_re_le hz]
  linarith [neg_abs_le (s * z.re)]

theorem norm_planeOf_model {w : ℂ} (hw : w ∈ annulus) :
    ‖planeOf (model w)‖ = 2 + ht w * (dir w).re := by
  rw [model, planeOf_modelOf, norm_smul, norm_pow, norm_dir (ne_zero_of_mem_annulus hw), one_pow,
    mul_one, Real.norm_eq_abs, abs_of_pos]
  linarith [one_le_of_abs (norm_dir (ne_zero_of_mem_annulus hw)) (abs_ht_le hw)]

theorem sq_add_one_eq {v : ℂ} (hv : ‖v‖ = 1) : v ^ 2 + 1 = (2 * v.re) • v := by
  have h1 : v * conj v = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv]
    norm_num
  have h2 : v + conj v = ((2 * v.re : ℝ) : ℂ) := by
    rw [Complex.add_conj]
  rw [Complex.real_smul, ← h2, ← h1]
  ring

theorem localInv_model {z₀ w : ℂ} (hz₀ : ‖z₀‖ = 1) (hw : w ∈ annulus)
    (hre : 0 < (w * conj z₀).re) : localInv z₀ (model w) = w := by
  have hw0 := ne_zero_of_mem_annulus hw
  set d := dir w with hd
  have hdn : ‖d‖ = 1 := norm_dir hw0
  have hR := norm_planeOf_model hw
  have hR1 := one_le_of_abs hdn (abs_ht_le hw)
  have hu : ‖planeOf (model w)‖⁻¹ • planeOf (model w) = d ^ 2 := by
    rw [hR, model, planeOf_modelOf, smul_smul, inv_mul_cancel₀ (by linarith), one_smul]
  set v := d * conj z₀ with hv
  have hvn : ‖v‖ = 1 := by rw [hv, norm_mul, Complex.norm_conj, hdn, hz₀, one_mul]
  have hvre : 0 < v.re := by
    have e : w * conj z₀ = ‖w‖ • v := by
      rw [hv, ← smul_mul_assoc, hd, norm_smul_dir]
    rw [e, Complex.smul_re] at hre
    exact pos_of_mul_pos_right hre (norm_nonneg w)
  have ha : d ^ 2 * conj z₀ ^ 2 + 1 = (2 * v.re) • v := by
    rw [← sq_add_one_eq hvn, hv, mul_pow]
  have hz : z₀ * (‖(2 * v.re) • v‖⁻¹ • ((2 * v.re) • v)) = d := by
    rw [norm_smul, hvn, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith), smul_smul,
      inv_mul_cancel₀ (by linarith), one_smul, hv, ← mul_assoc, mul_comm z₀ d, mul_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, hz₀]
    norm_num
  simp only [localInv]
  rw [hu, ha, hz, hR]
  have hs : d.re * (2 + ht w * d.re - 2) + d.im * model w 2 = ht w := by
    rw [model, modelOf_apply_two, ← hd]
    have := re_sq_add_im_sq hdn
    linear_combination ht w * this
  rw [hs, ← norm_eq_of_ht, hd, norm_smul_dir]

theorem contDiff_modelOf : ContDiff ℝ ∞ (fun p : ℂ × ℝ => modelOf p.1 p.2) := by
  refine contDiff_piLp' 2 fun i => ?_
  have hre : ContDiff ℝ ∞ (fun p : ℂ × ℝ => p.1.re) := Complex.reCLM.contDiff.comp contDiff_fst
  have him : ContDiff ℝ ∞ (fun p : ℂ × ℝ => p.1.im) := Complex.imCLM.contDiff.comp contDiff_fst
  have hsq : ∀ v : ℂ, (v ^ 2).re = v.re ^ 2 - v.im ^ 2 ∧ (v ^ 2).im = 2 * v.re * v.im := by
    intro v
    constructor <;> simp [sq]; ring
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, modelOf_apply_zero, (hsq _).1]
    exact (contDiff_const.add (contDiff_snd.mul hre)).mul ((hre.pow 2).sub (him.pow 2))
  · simp only [Fin.mk_one, Fin.isValue, modelOf_apply_one, (hsq _).2]
    exact (contDiff_const.add (contDiff_snd.mul hre)).mul ((contDiff_const.mul hre).mul him)
  · simp only [Fin.reduceFinMk, modelOf_apply_two]
    exact contDiff_snd.mul him

theorem contDiffAt_dir {w : ℂ} (hw : w ≠ 0) : ContDiffAt ℝ ∞ dir w :=
  ((contDiffAt_norm ℝ hw).inv (norm_ne_zero_iff.mpr hw)).smul contDiffAt_id

theorem contDiffAt_ht {w : ℂ} (hw : w ≠ 0) : ContDiffAt ℝ ∞ ht w :=
  ((contDiffAt_const.mul (contDiffAt_norm ℝ hw)).sub contDiffAt_const).div_const _

theorem contDiffAt_model {w : ℂ} (hw : w ≠ 0) : ContDiffAt ℝ ∞ model w :=
  contDiff_modelOf.contDiffAt.comp w ((contDiffAt_dir hw).prodMk (contDiffAt_ht hw))

theorem contDiffAt_deck {w : ℂ} (hw : w ≠ 0) : ContDiffAt ℝ ∞ deck w :=
  (((contDiffAt_const.sub (contDiffAt_norm ℝ hw)).div (contDiffAt_norm ℝ hw)
    (norm_ne_zero_iff.mpr hw)).smul contDiffAt_id).neg

theorem contDiff_planeOf : ContDiff ℝ ∞ planeOf :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_piLp_apply 2 (i := (0 : Fin 3)))).add
    ((Complex.ofRealCLM.contDiff.comp (contDiff_piLp_apply 2 (i := (1 : Fin 3)))).mul
      contDiff_const)

theorem contDiffAt_localInv {z₀ w : ℂ} (hz₀ : ‖z₀‖ = 1) (hw : w ∈ annulus)
    (hre : 0 < (w * conj z₀).re) : ContDiffAt ℝ ∞ (localInv z₀) (model w) := by
  have hw0 := ne_zero_of_mem_annulus hw
  have hdn : ‖dir w‖ = 1 := norm_dir hw0
  have hR := norm_planeOf_model hw
  have hR1 := one_le_of_abs hdn (abs_ht_le hw)
  have hP0 : planeOf (model w) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hR
    linarith
  have hN : ContDiffAt ℝ ∞ (fun X => ‖planeOf X‖) (model w) :=
    (contDiffAt_norm ℝ hP0).comp (model w) contDiff_planeOf.contDiffAt
  have hNi : ContDiffAt ℝ ∞ (fun X => ‖planeOf X‖⁻¹) (model w) :=
    hN.inv (norm_ne_zero_iff.mpr hP0)
  have hU : ContDiffAt ℝ ∞ (fun X => ‖planeOf X‖⁻¹ • planeOf X) (model w) :=
    hNi.smul contDiff_planeOf.contDiffAt
  have hA : ContDiffAt ℝ ∞ (fun X => (‖planeOf X‖⁻¹ • planeOf X) * conj z₀ ^ 2 + 1)
      (model w) := (hU.mul contDiffAt_const).add contDiffAt_const
  have hA0 : (‖planeOf (model w)‖⁻¹ • planeOf (model w)) * conj z₀ ^ 2 + 1 ≠ 0 := by
    set v := dir w * conj z₀ with hv
    have hvn : ‖v‖ = 1 := by rw [hv, norm_mul, Complex.norm_conj, hdn, hz₀, one_mul]
    have hvre : 0 < v.re := by
      have e : w * conj z₀ = ‖w‖ • v := by
        rw [hv, ← smul_mul_assoc, norm_smul_dir]
      rw [e, Complex.smul_re] at hre
      exact pos_of_mul_pos_right hre (norm_nonneg w)
    have hu : ‖planeOf (model w)‖⁻¹ • planeOf (model w) = dir w ^ 2 := by
      rw [hR, model, planeOf_modelOf, smul_smul, inv_mul_cancel₀ (by linarith), one_smul]
    rw [hu, ← mul_pow, ← hv, sq_add_one_eq hvn]
    intro h
    rcases smul_eq_zero.mp h with h' | h'
    · linarith
    · rw [h', norm_zero] at hvn
      norm_num at hvn
  have hZ : ContDiffAt ℝ ∞ (fun X => z₀ * (‖(‖planeOf X‖⁻¹ • planeOf X) * conj z₀ ^ 2 + 1‖⁻¹ •
      ((‖planeOf X‖⁻¹ • planeOf X) * conj z₀ ^ 2 + 1))) (model w) :=
    contDiffAt_const.mul ((((contDiffAt_norm ℝ hA0).comp (model w) hA).inv
      (norm_ne_zero_iff.mpr hA0)).smul hA)
  have hX2 : ContDiffAt ℝ ∞ (fun X : EuclideanSpace ℝ (Fin 3) => X 2) (model w) :=
    (contDiff_piLp_apply 2 (i := (2 : Fin 3))).contDiffAt
  set Z := fun X : EuclideanSpace ℝ (Fin 3) => z₀ * (‖(‖planeOf X‖⁻¹ • planeOf X) *
      conj z₀ ^ 2 + 1‖⁻¹ • ((‖planeOf X‖⁻¹ • planeOf X) * conj z₀ ^ 2 + 1)) with hZdef
  have hS : ContDiffAt ℝ ∞ (fun X => (Z X).re * (‖planeOf X‖ - 2) + (Z X).im * X 2)
      (model w) :=
    ((Complex.reCLM.contDiff.contDiffAt.comp (model w) hZ).mul (hN.sub contDiffAt_const)).add
      ((Complex.imCLM.contDiff.contDiffAt.comp (model w) hZ).mul hX2)
  have hfin : ContDiffAt ℝ ∞
      (fun X => ((5 * ((Z X).re * (‖planeOf X‖ - 2) + (Z X).im * X 2) + 7) / 4) • Z X)
      (model w) := (((contDiffAt_const.mul hS).add contDiffAt_const).div_const 4).smul hZ
  exact hfin

theorem planarModel_two_eq : planarModel 2 = annulus := by
  ext w
  simp only [planarModel, annulus, mem_ofPred_eq, Fin.forall_fin_two]
  simp [planarCenter]
  tauto

def annEmb (x : annulusSurface.{u}.Carrier) : ℂ := annulusPlanarBase.{u}.embedding x

theorem annEmb_apply (x : annulusSurface.{u}.Carrier) : annEmb x = x.val.down := rfl

theorem isSmoothEmbedding_annEmb :
    Manifold.IsSmoothEmbedding (SurfaceModel.model annulusSurface.{u}.kind) 𝓘(ℝ, ℂ) ∞
      annEmb.{u} :=
  annulusPlanarBase.{u}.isSmoothEmbedding

theorem annEmb_mem (x : annulusSurface.{u}.Carrier) : annEmb x ∈ annulus := by
  rw [← planarModel_two_eq, ← annulusPlanarBase.{u}.range_embedding]
  exact mem_range_self x

theorem injective_annEmb : Function.Injective annEmb.{u} :=
  isSmoothEmbedding_annEmb.isEmbedding.injective

def annMk (w : ℂ) (hw : w ∈ annulus) : annulusSurface.{u}.Carrier :=
  ⟨ULift.up w, (mem_planarSet_iff (Or.inl rfl) (ULift.up w)).mpr (planarModel_two_eq ▸ hw)⟩

theorem annEmb_annMk (w : ℂ) (hw : w ∈ annulus) : annEmb (annMk.{u} w hw) = w := rfl

theorem annMk_annEmb (x : annulusSurface.{u}.Carrier) : annMk (annEmb x) (annEmb_mem x) = x :=
  injective_annEmb rfl

theorem continuous_annMk {X : Type*} [TopologicalSpace X] {f : X → ℂ} (hf : Continuous f)
    (hfm : ∀ x, f x ∈ annulus) : Continuous fun x => annMk.{u} (f x) (hfm x) :=
  (continuous_uliftUp.comp hf).subtype_mk _

def annDeck (x : annulusSurface.{u}.Carrier) : annulusSurface.{u}.Carrier :=
  annMk (deck (annEmb x)) (deck_mem_annulus (annEmb_mem x))

theorem annEmb_annDeck (x : annulusSurface.{u}.Carrier) : annEmb (annDeck x) = deck (annEmb x) :=
  rfl

theorem annDeck_annDeck (x : annulusSurface.{u}.Carrier) : annDeck (annDeck x) = x :=
  injective_annEmb (deck_deck (annEmb_mem x))

theorem continuous_deck_annEmb :
    Continuous fun x : annulusSurface.{u}.Carrier => deck (annEmb x) :=
  continuous_iff_continuousAt.mpr fun x =>
    (contDiffAt_deck (ne_zero_of_mem_annulus (annEmb_mem x))).continuousAt.comp
      isSmoothEmbedding_annEmb.isEmbedding.continuous.continuousAt

theorem contMDiff_annDeck :
    ContMDiff (SurfaceModel.model annulusSurface.{u}.kind)
      (SurfaceModel.model annulusSurface.{u}.kind) ∞ annDeck.{u} := by
  refine (ContMDiff.iff_comp_isImmersion isSmoothEmbedding_annEmb.isImmersion).mpr
    ⟨continuous_annMk continuous_deck_annEmb _, fun x => ?_⟩
  exact (contDiffAt_deck (ne_zero_of_mem_annulus (annEmb_mem x))).comp_contMDiffAt
    (isSmoothEmbedding_annEmb.isImmersion.contMDiff x)

def sheet (z₀ : ℂ) : Set annulusSurface.{u}.Carrier := {x | 0 < (annEmb x * conj z₀).re}

theorem isOpen_sheet (z₀ : ℂ) : IsOpen (sheet.{u} z₀) :=
  isOpen_lt continuous_const (Complex.continuous_re.comp
    (isSmoothEmbedding_annEmb.isEmbedding.continuous.mul continuous_const))

theorem re_annDeck (z₀ : ℂ) (x : annulusSurface.{u}.Carrier) :
    (annEmb (annDeck x) * conj z₀).re =
      -((7 / 2 - ‖annEmb x‖) / ‖annEmb x‖) * (annEmb x * conj z₀).re := by
  rw [annEmb_annDeck, deck, neg_mul, Complex.neg_re, smul_mul_assoc, Complex.smul_re]
  ring

theorem re_annDeck_neg_iff (z₀ : ℂ) (x : annulusSurface.{u}.Carrier) :
    (annEmb (annDeck x) * conj z₀).re < 0 ↔ 0 < (annEmb x * conj z₀).re := by
  have hx := annEmb_mem x
  have hc : 0 < (7 / 2 - ‖annEmb x‖) / ‖annEmb x‖ :=
    div_pos (by linarith [hx.2]) (norm_pos_of_mem_annulus hx)
  rw [re_annDeck, neg_mul, neg_lt_zero]
  exact ⟨fun h => pos_of_mul_pos_right h hc.le, fun h => mul_pos hc h⟩

theorem re_annDeck_pos_iff (z₀ : ℂ) (x : annulusSurface.{u}.Carrier) :
    0 < (annEmb (annDeck x) * conj z₀).re ↔ (annEmb x * conj z₀).re < 0 := by
  have h := re_annDeck_neg_iff z₀ (annDeck x)
  rw [annDeck_annDeck] at h
  exact h.symm

theorem re_annDeck_eq_zero_iff (z₀ : ℂ) (x : annulusSurface.{u}.Carrier) :
    (annEmb (annDeck x) * conj z₀).re = 0 ↔ (annEmb x * conj z₀).re = 0 := by
  have hx := annEmb_mem x
  have hc : 0 < (7 / 2 - ‖annEmb x‖) / ‖annEmb x‖ :=
    div_pos (by linarith [hx.2]) (norm_pos_of_mem_annulus hx)
  rw [re_annDeck, neg_mul, neg_eq_zero, mul_eq_zero]
  exact ⟨fun h => h.resolve_left hc.ne', Or.inr⟩

section Cover

variable {B : CompactSurface.{u}} {E : B.Carrier → EuclideanSpace ℝ (Fin 3)}

theorem model_mem_range (hrange : range E = mobiusModel) (x : annulusSurface.{u}.Carrier) :
    model (annEmb x) ∈ range E :=
  hrange ▸ model_mem_mobiusModel (annEmb_mem x)

def cover (hrange : range E = mobiusModel) (x : annulusSurface.{u}.Carrier) : B.Carrier :=
  (model_mem_range hrange x).choose

theorem E_cover (hrange : range E = mobiusModel) (x : annulusSurface.{u}.Carrier) :
    E (cover hrange x) = model (annEmb x) :=
  (model_mem_range hrange x).choose_spec

variable (hE : Manifold.IsSmoothEmbedding (SurfaceModel.model B.kind)
  𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ E) (hrange : range E = mobiusModel)

omit hE hrange in
theorem continuous_model_annEmb :
    Continuous fun x : annulusSurface.{u}.Carrier => model (annEmb x) :=
  continuous_iff_continuousAt.mpr fun x =>
    (contDiffAt_model (ne_zero_of_mem_annulus (annEmb_mem x))).continuousAt.comp
      isSmoothEmbedding_annEmb.isEmbedding.continuous.continuousAt

include hE in
theorem continuous_cover : Continuous (cover.{u} hrange) := by
  refine hE.isEmbedding.continuous_iff.mpr ?_
  have h : E ∘ cover.{u} hrange = fun x => model (annEmb x) := funext (E_cover (E := E) hrange)
  rw [h]
  exact continuous_model_annEmb

include hE in
theorem contMDiff_cover :
    ContMDiff (SurfaceModel.model annulusSurface.{u}.kind) (SurfaceModel.model B.kind) ∞
      (cover.{u} hrange) := by
  refine (ContMDiff.iff_comp_isImmersion hE.isImmersion).mpr
    ⟨continuous_cover hE hrange, fun x => ?_⟩
  have h : E ∘ cover.{u} hrange = fun x => model (annEmb x) := funext (E_cover (E := E) hrange)
  rw [h]
  exact (contDiffAt_model (ne_zero_of_mem_annulus (annEmb_mem x))).comp_contMDiffAt
    (isSmoothEmbedding_annEmb.isImmersion.contMDiff x)

include hE in
theorem cover_annDeck (x : annulusSurface.{u}.Carrier) :
    cover hrange (annDeck x) = cover hrange x :=
  hE.isEmbedding.injective (by
    rw [E_cover hrange, E_cover hrange, annEmb_annDeck, model_deck (annEmb_mem x)])

include hE in
theorem cover_eq_cover_iff (x y : annulusSurface.{u}.Carrier) :
    cover hrange x = cover hrange y ↔ y = x ∨ y = annDeck x := by
  constructor
  · intro h
    have h' := congrArg E h
    rw [E_cover hrange, E_cover hrange] at h'
    rcases eq_or_eq_deck_of_model_eq (annEmb_mem x) (annEmb_mem y) h' with h1 | h1
    · exact Or.inl (injective_annEmb h1)
    · exact Or.inr (injective_annEmb h1)
  · rintro (rfl | rfl)
    · rfl
    · exact (cover_annDeck hE hrange x).symm

include hE in
theorem surjective_cover : Function.Surjective (cover.{u} hrange) := by
  intro b
  have hb : E b ∈ mobiusModel := hrange ▸ mem_range_self b
  obtain ⟨w, hw, hwb⟩ := mobiusModel_subset hb
  refine ⟨annMk w hw, hE.isEmbedding.injective ?_⟩
  rw [E_cover hrange, annEmb_annMk, hwb]

include hE in
theorem injOn_cover (z₀ : ℂ) : InjOn (cover.{u} hrange) (sheet z₀) := by
  intro x hx y hy h
  rcases (cover_eq_cover_iff hE hrange x y).mp h with h1 | h1
  · exact h1.symm
  · exfalso
    have h2 := (re_annDeck_neg_iff z₀ x).mpr hx
    rw [← h1] at h2
    exact lt_asymm hy h2

include hE in
theorem cover_image_sheet (z₀ : ℂ) :
    cover.{u} hrange '' sheet z₀ =
      (cover hrange '' {x | (annEmb x * conj z₀).re = 0})ᶜ := by
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    rcases (cover_eq_cover_iff hE hrange y x).mp hxy with h1 | h1
    · rw [h1] at hx
      exact absurd hy (ne_of_gt hx)
    · rw [h1] at hx
      have h2 := (re_annDeck_pos_iff z₀ y).mp hx
      have hy' : (annEmb y * conj z₀).re = 0 := hy
      rw [hy'] at h2
      exact lt_irrefl 0 h2
  · intro hb
    obtain ⟨x, rfl⟩ := surjective_cover hE hrange b
    rcases lt_trichotomy (annEmb x * conj z₀).re 0 with h | h | h
    · exact ⟨annDeck x, (re_annDeck_pos_iff z₀ x).mpr h, cover_annDeck hE hrange x⟩
    · exact absurd ⟨x, h, rfl⟩ hb
    · exact ⟨x, h, rfl⟩

include hE in
theorem isOpen_cover_image_sheet (z₀ : ℂ) : IsOpen (cover.{u} hrange '' sheet z₀) := by
  rw [cover_image_sheet hE hrange]
  refine (IsCompact.isClosed ?_).isOpen_compl
  refine (IsClosed.isCompact ?_).image (continuous_cover hE hrange)
  exact isClosed_eq (Complex.continuous_re.comp
    (isSmoothEmbedding_annEmb.isEmbedding.continuous.mul continuous_const)) continuous_const

open Classical in
def localSection (z₀ : ℂ) (b : B.Carrier) : annulusSurface.{u}.Carrier :=
  if h : localInv z₀ (E b) ∈ annulus then annMk (localInv z₀ (E b)) h
  else annMk 2 (by rw [annulus, mem_ofPred_eq]; norm_num)

theorem localSection_cover {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) {x : annulusSurface.{u}.Carrier}
    (hx : x ∈ sheet z₀) : localSection (E := E) z₀ (cover hrange x) = x := by
  have h : localInv z₀ (E (cover hrange x)) = annEmb x := by
    rw [E_cover hrange]
    exact localInv_model hz₀ (annEmb_mem x) hx
  rw [localSection, dite_eq_left (h ▸ annEmb_mem x)]
  apply injective_annEmb
  rw [annEmb_annMk, h]

theorem cover_localSection {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) {b : B.Carrier}
    (hb : b ∈ cover.{u} hrange '' sheet z₀) :
    cover hrange (localSection (E := E) z₀ b) = b := by
  obtain ⟨x, hx, rfl⟩ := hb
  rw [localSection_cover hrange hz₀ hx]

theorem localSection_mem {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) {b : B.Carrier}
    (hb : b ∈ cover.{u} hrange '' sheet z₀) : localSection (E := E) z₀ b ∈ sheet z₀ := by
  obtain ⟨x, hx, rfl⟩ := hb
  rw [localSection_cover hrange hz₀ hx]
  exact hx

theorem annEmb_localSection {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) {b : B.Carrier}
    (hb : b ∈ cover.{u} hrange '' sheet z₀) :
    annEmb (localSection (E := E) z₀ b) = localInv z₀ (E b) := by
  obtain ⟨x, hx, rfl⟩ := hb
  rw [localSection_cover hrange hz₀ hx, E_cover hrange, localInv_model hz₀ (annEmb_mem x) hx]

include hE in
theorem contMDiffAt_localSection {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) {b : B.Carrier}
    (hb : b ∈ cover.{u} hrange '' sheet z₀) :
    ContMDiffAt (SurfaceModel.model B.kind) (SurfaceModel.model annulusSurface.{u}.kind) ∞
      (localSection (E := E) z₀) b := by
  have hO := isOpen_cover_image_sheet hE hrange z₀
  have hev : (fun b' => annEmb (localSection (E := E) z₀ b')) =ᶠ[𝓝 b]
      fun b' => localInv z₀ (E b') := by
    filter_upwards [hO.mem_nhds hb] with b' hb'
    exact annEmb_localSection hrange hz₀ hb'
  obtain ⟨x, hx, rfl⟩ := hb
  have hsm : ContMDiffAt (SurfaceModel.model B.kind) 𝓘(ℝ, ℂ) ∞
      (fun b' => localInv z₀ (E b')) (cover hrange x) := by
    have h1 := contDiffAt_localInv hz₀ (annEmb_mem x) hx
    rw [← E_cover hrange x] at h1
    exact h1.comp_contMDiffAt (hE.isImmersion.contMDiff _)
  refine (ContMDiffAt.iff_comp_isImmersionAt
    (isSmoothEmbedding_annEmb.isImmersion.isImmersionAt
      (localSection (E := E) z₀ (cover hrange x)))).mpr
    ⟨?_, hsm.congr_of_eventuallyEq hev⟩
  refine (isSmoothEmbedding_annEmb.isEmbedding.isInducing.continuousAt_iff).mpr ?_
  exact (hsm.continuousAt).congr hev.symm

include hE in
theorem contMDiffOn_localSection {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) :
    ContMDiffOn (SurfaceModel.model B.kind) (SurfaceModel.model annulusSurface.{u}.kind) ∞
      (localSection (E := E) z₀) (cover.{u} hrange '' sheet z₀) :=
  fun _ hb => (contMDiffAt_localSection hE hrange hz₀ hb).contMDiffWithinAt

end Cover

end MobiusCover

end GC.Seifert

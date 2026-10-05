import DifferentialGeometry.Topology.Manifold.AddCircle.Circle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MobiusRefibration

/-!
# Coordinates of the twisted `I`-bundle model `mobiusBundleCarrier`

Lane LFR54-QUOT (Q2, the Klein row of LFR52/LFR54). The fixed model `GC.Seifert.mobiusBundleCarrier`
is `{Q ≤ 0} ⊆ L(4, -1)`; its points have model coordinates `(z, u) ∈ S¹ × ℂˣ`
(`GC.Seifert.modelPoint`), the lens generator acting by `(z, u) ↦ (-z, u⁻¹)`.

This file supplies explicit coordinates relating it to the Klein deck involution
`(x, y, t) ↦ (x + ½, -y, -t)` of `T² × ℝ`:
* the angle `circleArg z ∈ AddCircle 1` of a nonzero complex number, smooth off `0`
  (`contMDiffAt_circleArg`), with `circleArg (-z) = circleArg z + ½` and
  `circleArg u⁻¹ = -circleArg u`;
* the radial coordinate `kleinT u` and its inverse `kleinU ω t` (`kleinT_kleinU`,
  `kleinU_kleinT`), odd under `u ↦ u⁻¹` (`kleinT_inv`), with `|kleinT u| ≤ 1` exactly on the
  model annulus `‖joukowski u‖ ≤ 3` (`norm_joukowski_le_three_iff`);
* an explicit smooth map `kleinW : ℝ × ℝ × ℝ → S³ ⊆ ℂ²` whose model point is
  `(e^{2πix}, kleinU (e^{2πiy}) t)` (`modelPoint_kleinW`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Function Module
open scoped Manifold ContDiff Topology ComplexConjugate Real

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel.Klein

/-! ### The angle of a nonzero complex number -/

/-- `ℂ` has real dimension `1 + 1`. -/
local instance finrankComplexFact_LFR54QUOT : Fact (finrank ℝ ℂ = 1 + 1) :=
  ⟨by rw [Complex.finrank_real_complex]⟩

/-- The unit complex number `z / ‖z‖` (and `1` at `0`). -/
def unitCircleOf (z : ℂ) : Circle :=
  if h : z = 0 then 1 else
    ⟨z / (‖z‖ : ℂ), by
      change z / (‖z‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1
      rw [mem_sphere_zero_iff_norm, norm_div,
        Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z), div_self (norm_ne_zero_iff.mpr h)]⟩

theorem coe_unitCircleOf {z : ℂ} (hz : z ≠ 0) : (unitCircleOf z : ℂ) = z / (‖z‖ : ℂ) := by
  simp only [unitCircleOf, hz, ↓reduceDIte]

/-- The angle `circleArg z ∈ ℝ / ℤ` of `z`, i.e. `e^{2πi circleArg z} = z / ‖z‖`. -/
def circleArg (z : ℂ) : AddCircle (1 : ℝ) := AddCircle.diffeomorphCircle.symm (unitCircleOf z)

theorem diffeomorphCircle_apply (a : AddCircle (1 : ℝ)) :
    AddCircle.diffeomorphCircle a = AddCircle.toCircle a :=
  AddCircle.homeomorphCircle_apply one_ne_zero a

theorem toCircle_circleArg (z : ℂ) : AddCircle.toCircle (circleArg z) = unitCircleOf z := by
  rw [← diffeomorphCircle_apply, circleArg, Diffeomorph.apply_symm_apply]

theorem coe_toCircle_circleArg {z : ℂ} (hz : z ≠ 0) :
    (AddCircle.toCircle (circleArg z) : ℂ) = z / (‖z‖ : ℂ) := by
  rw [toCircle_circleArg, coe_unitCircleOf hz]

theorem circleArg_eq_iff {z : ℂ} (hz : z ≠ 0) {a : AddCircle (1 : ℝ)} :
    circleArg z = a ↔ (AddCircle.toCircle a : ℂ) = z / (‖z‖ : ℂ) := by
  constructor
  · rintro rfl
    exact coe_toCircle_circleArg hz
  · intro h
    apply AddCircle.injective_toCircle one_ne_zero
    apply Circle.ext
    rw [coe_toCircle_circleArg hz, h]

theorem coe_toCircle_coe (x : ℝ) :
    (AddCircle.toCircle (x : AddCircle (1 : ℝ)) : ℂ) = Circle.exp (2 * π * x) := by
  rw [AddCircle.toCircle_apply_mk, div_one]

/-- The angle of a unit complex number of the form `toCircle a` is `a`. -/
theorem circleArg_toCircle (a : AddCircle (1 : ℝ)) :
    circleArg (AddCircle.toCircle a : ℂ) = a := by
  have hz : (AddCircle.toCircle a : ℂ) ≠ 0 := Circle.coe_ne_zero _
  rw [circleArg_eq_iff hz, Circle.norm_coe, Complex.ofReal_one, div_one]

theorem circleArg_ofReal_mul {r : ℝ} (hr : 0 < r) (z : ℂ) :
    circleArg ((r : ℂ) * z) = circleArg z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [mul_zero]
  have hrz : (r : ℂ) * z ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hz
  rw [circleArg_eq_iff hrz, coe_toCircle_circleArg hz, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hr.le, Complex.ofReal_mul]
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [mul_div_mul_left _ _ hr']

theorem circleArg_neg {z : ℂ} (hz : z ≠ 0) :
    circleArg (-z) = circleArg z + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
  rw [circleArg_eq_iff (neg_ne_zero.mpr hz), AddCircle.toCircle_add, Circle.coe_mul,
    coe_toCircle_circleArg hz, coe_toCircle_coe, Circle.coe_exp, norm_neg]
  have h : Complex.exp (↑(2 * π * (1 / 2 : ℝ)) * I) = -1 := by
    rw [show (2 * π * (1 / 2 : ℝ) : ℝ) = π by ring]
    exact Complex.exp_pi_mul_I
  rw [h, mul_neg_one, neg_div]

theorem circleArg_inv {u : ℂ} (hu : u ≠ 0) : circleArg u⁻¹ = -circleArg u := by
  rw [circleArg_eq_iff (inv_ne_zero hu), AddCircle.toCircle_neg, Circle.coe_inv,
    coe_toCircle_circleArg hu, norm_inv, Complex.ofReal_inv, inv_div, div_inv_eq_mul]
  have hn : (‖u‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu)
  field_simp

/-- The angle is smooth off the origin. -/
theorem contMDiffAt_circleArg {z : ℂ} (hz : z ≠ 0) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ circleArg z := by
  let U : TopologicalSpace.Opens ℂ := ⟨{w | w ≠ 0}, isOpen_ne⟩
  have hdiv : ∀ w : ℂ, w ≠ 0 →
      ContDiffAt ℝ ∞ (fun v : ℂ => v / ((‖v‖ : ℝ) : ℂ)) w := by
    intro w hw
    have hn : ContDiffAt ℝ ∞ (fun v : ℂ => ((‖v‖ : ℝ) : ℂ)) w :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp w (contDiffAt_norm ℝ hw)
    have he : (fun v : ℂ => v / ((‖v‖ : ℝ) : ℂ)) =
        fun v : ℂ => v * (((‖v‖ : ℝ) : ℂ))⁻¹ := funext fun v => div_eq_mul_inv _ _
    rw [he]
    exact contDiffAt_id.mul (hn.inv (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)))
  have hmem : ∀ w : U, (w : ℂ) / ((‖(w : ℂ)‖ : ℝ) : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
    intro w
    have hw : (w : ℂ) ≠ 0 := w.2
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr hw)]
  have hval : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (fun w : U => (w : ℂ) / ((‖(w : ℂ)‖ : ℝ) : ℂ)) := fun w =>
    contMDiffAt_subtype_iff.mpr (hdiv w w.2).contMDiffAt
  have hg : ContMDiff 𝓘(ℝ, ℂ) (𝓡 1) ∞
      (Set.codRestrict (fun w : U => (w : ℂ) / ((‖(w : ℂ)‖ : ℝ) : ℂ)) _ hmem :
        U → Metric.sphere (0 : ℂ) 1) :=
    hval.codRestrict_sphere hmem
  have hc : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (fun w : U => circleArg w) := by
    have h2 := AddCircle.diffeomorphCircle.symm.contMDiff.comp hg
    refine h2.congr fun w => ?_
    change AddCircle.diffeomorphCircle.symm (unitCircleOf w) = _
    congr 1
    apply Circle.ext
    rw [coe_unitCircleOf w.2]
    rfl
  exact contMDiffAt_subtype_iff.mp (hc ⟨z, hz⟩)

/-! ### The radial coordinate of the model annulus -/

/-- `8 - Re u² / |u|²`, in `[7, 9]`. -/
def kleinC (u : ℂ) : ℝ := 8 - (u ^ 2).re / normSq u

/-- `t √(c² - 1)`, the value of `sinh (2 log |u|)` on the radial coordinate `t`. -/
def kleinQ (η : ℂ) (t : ℝ) : ℝ := t * √(kleinC η ^ 2 - 1)

/-- `|u|²` as a function of the angle and the radial coordinate. -/
def kleinRho (η : ℂ) (t : ℝ) : ℝ := kleinQ η t + √(1 + kleinQ η t ^ 2)

/-- The annulus point with angle `η` and radial coordinate `t`. -/
def kleinU (η : ℂ) (t : ℝ) : ℂ := ((√(kleinRho η t) : ℝ) : ℂ) * η

/-- The radial coordinate `(|u|² - |u|⁻²) / (2 √(c² - 1))` of `u`. -/
def kleinT (u : ℂ) : ℝ := (normSq u - (normSq u)⁻¹) / (2 * √(kleinC u ^ 2 - 1))

theorem re_sq_eq (u : ℂ) : (u ^ 2).re = u.re ^ 2 - u.im ^ 2 := by
  simp only [sq, Complex.mul_re]

theorem abs_re_sq_div_normSq_le (u : ℂ) : |(u ^ 2).re / normSq u| ≤ 1 := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hs : 0 < normSq u := normSq_pos.mpr hu
  rw [abs_div, abs_of_pos hs, div_le_one hs, re_sq_eq, normSq_apply, abs_le]
  constructor <;> nlinarith [sq_nonneg u.re, sq_nonneg u.im]

theorem seven_le_kleinC (u : ℂ) : 7 ≤ kleinC u := by
  have h := abs_le.mp (abs_re_sq_div_normSq_le u)
  rw [kleinC]
  linarith [h.2]

theorem kleinC_sq_sub_one_pos (u : ℂ) : 0 < kleinC u ^ 2 - 1 := by
  nlinarith [seven_le_kleinC u]

theorem sqrt_kleinC_pos (u : ℂ) : 0 < √(kleinC u ^ 2 - 1) :=
  Real.sqrt_pos.mpr (kleinC_sq_sub_one_pos u)

theorem kleinC_ofReal_mul {r : ℝ} (hr : r ≠ 0) (u : ℂ) : kleinC ((r : ℂ) * u) = kleinC u := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [mul_zero]
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hs : normSq u ≠ 0 := (normSq_pos.mpr hu).ne'
  rw [kleinC, kleinC, normSq_mul, normSq_ofReal, mul_pow, ← Complex.ofReal_pow,
    Complex.re_ofReal_mul]
  congr 1
  rw [show r * r = r ^ 2 by ring]
  field_simp

theorem kleinC_conj (u : ℂ) : kleinC (conj u) = kleinC u := by
  rw [kleinC, kleinC, normSq_conj, ← map_pow, Complex.conj_re]

theorem kleinC_inv (u : ℂ) : kleinC u⁻¹ = kleinC u := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [inv_zero]
  have hs : normSq u ≠ 0 := (normSq_pos.mpr hu).ne'
  rw [kleinC, kleinC, normSq_inv, inv_pow, Complex.inv_re, map_pow]
  congr 1
  field_simp

theorem one_add_sq_eq_of_rho (q : ℝ) : (q + √(1 + q ^ 2)) * (√(1 + q ^ 2) - q) = 1 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + q ^ 2 by positivity)
  nlinarith [h]

theorem rho_pos (q : ℝ) : 0 < q + √(1 + q ^ 2) := by
  have h1 : |q| < √(1 + q ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg q) (by linarith)
  linarith [neg_abs_le q]

theorem kleinRho_pos (η : ℂ) (t : ℝ) : 0 < kleinRho η t := rho_pos _

theorem kleinRho_inv (η : ℂ) (t : ℝ) :
    (kleinRho η t)⁻¹ = √(1 + kleinQ η t ^ 2) - kleinQ η t := by
  exact inv_eq_of_mul_eq_one_right (one_add_sq_eq_of_rho _)

theorem kleinRho_sub_inv (η : ℂ) (t : ℝ) :
    kleinRho η t - (kleinRho η t)⁻¹ = 2 * kleinQ η t := by
  rw [kleinRho_inv, kleinRho]
  ring

theorem normSq_kleinU {η : ℂ} (hη : ‖η‖ = 1) (t : ℝ) : normSq (kleinU η t) = kleinRho η t := by
  rw [kleinU, normSq_mul, normSq_ofReal, ← sq, Real.sq_sqrt (kleinRho_pos η t).le,
    normSq_eq_norm_sq, hη, one_pow, mul_one]

theorem kleinU_ne_zero {η : ℂ} (hη : η ≠ 0) (t : ℝ) : kleinU η t ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (kleinRho_pos η t)).ne') hη

theorem kleinC_kleinU (η : ℂ) (t : ℝ) : kleinC (kleinU η t) = kleinC η :=
  kleinC_ofReal_mul (Real.sqrt_pos.mpr (kleinRho_pos η t)).ne' η

/-- The radial coordinate of `kleinU η t` is `t`. -/
theorem kleinT_kleinU {η : ℂ} (hη : ‖η‖ = 1) (t : ℝ) : kleinT (kleinU η t) = t := by
  rw [kleinT, normSq_kleinU hη, kleinRho_sub_inv, kleinC_kleinU, kleinQ]
  have hk := (sqrt_kleinC_pos η).ne'
  field_simp

/-- Every nonzero `u` is `kleinU` of its angle and its radial coordinate. -/
theorem kleinU_kleinT {u : ℂ} (hu : u ≠ 0) : kleinU (u / (‖u‖ : ℂ)) (kleinT u) = u := by
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hs : normSq u = ‖u‖ ^ 2 := normSq_eq_norm_sq u
  have hs0 : 0 < normSq u := normSq_pos.mpr hu
  have hc : kleinC (u / (‖u‖ : ℂ)) = kleinC u := by
    rw [div_eq_inv_mul, ← Complex.ofReal_inv]
    exact kleinC_ofReal_mul (inv_ne_zero hn.ne') u
  have hk := sqrt_kleinC_pos u
  have hq : kleinQ (u / (‖u‖ : ℂ)) (kleinT u) = (normSq u - (normSq u)⁻¹) / 2 := by
    rw [kleinQ, hc, kleinT]
    field_simp
  have hsq : √(1 + ((normSq u - (normSq u)⁻¹) / 2) ^ 2) = (normSq u + (normSq u)⁻¹) / 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
    field_simp
    ring
  have hrho : kleinRho (u / (‖u‖ : ℂ)) (kleinT u) = normSq u := by
    rw [kleinRho, hq, hsq]
    ring
  rw [kleinU, hrho, hs, Real.sqrt_sq hn.le]
  have hn' : (‖u‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  field_simp

theorem kleinT_inv (u : ℂ) : kleinT u⁻¹ = -kleinT u := by
  rw [kleinT, kleinT, kleinC_inv, normSq_inv, inv_inv, ← neg_div]
  congr 1
  ring

/-- The model annulus `‖J u‖ ≤ 3` is exactly `|kleinT u| ≤ 1`. -/
theorem norm_joukowski_le_three_iff {u : ℂ} (hu : u ≠ 0) :
    ‖GC.Seifert.joukowski u‖ ≤ 3 ↔ |kleinT u| ≤ 1 := by
  set s := normSq u with hsdef
  have hs : 0 < s := normSq_pos.mpr hu
  set c := kleinC u with hcdef
  have hc7 : 7 ≤ c := seven_le_kleinC u
  have hk := sqrt_kleinC_pos u
  have hk2 : √(c ^ 2 - 1) ^ 2 = c ^ 2 - 1 := Real.sq_sqrt (kleinC_sq_sub_one_pos u).le
  have hnorm : normSq (u + u⁻¹) = s + s⁻¹ + 2 * (8 - c) := by
    rw [hcdef, kleinC, normSq_apply, Complex.add_re, Complex.add_im, Complex.inv_re,
      Complex.inv_im, re_sq_eq, ← hsdef]
    have hs' : s = u.re * u.re + u.im * u.im := by rw [hsdef, normSq_apply]
    field_simp
    rw [hs']
    ring
  have key1 : ‖GC.Seifert.joukowski u‖ ≤ 3 ↔ s + s⁻¹ ≤ 2 * c := by
    rw [GC.Seifert.joukowski, norm_mul, show ‖(3 / 4 : ℂ)‖ = 3 / 4 by norm_num]
    have h4 : ‖u + u⁻¹‖ ≤ 4 ↔ normSq (u + u⁻¹) ≤ 16 := by
      rw [normSq_eq_norm_sq]
      constructor
      · intro h
        nlinarith [norm_nonneg (u + u⁻¹)]
      · intro h
        nlinarith [norm_nonneg (u + u⁻¹)]
    constructor
    · intro h
      have : ‖u + u⁻¹‖ ≤ 4 := by linarith
      have := h4.mp this
      rw [hnorm] at this
      linarith
    · intro h
      have : normSq (u + u⁻¹) ≤ 16 := by rw [hnorm]; linarith
      have := h4.mpr this
      linarith
  have key2 : |kleinT u| ≤ 1 ↔ s + s⁻¹ ≤ 2 * c := by
    have hss : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
    have hpos : 0 < s + s⁻¹ := by positivity
    have hk' : 0 < √(c ^ 2 - 1) := hk
    have hD : 0 < 2 * √(c ^ 2 - 1) := mul_pos two_pos hk'
    rw [kleinT, ← hsdef, ← hcdef, abs_div, abs_of_pos hD, div_le_one hD, abs_le]
    constructor
    · rintro ⟨h1, h2⟩
      have hsq : (s - s⁻¹) ^ 2 ≤ (2 * √(c ^ 2 - 1)) ^ 2 := by nlinarith
      have h3 : (s + s⁻¹) ^ 2 ≤ (2 * c) ^ 2 := by nlinarith
      nlinarith
    · intro h
      have h3 : (s - s⁻¹) ^ 2 ≤ (2 * √(c ^ 2 - 1)) ^ 2 := by nlinarith
      constructor <;> nlinarith [sq_nonneg (s - s⁻¹ - 2 * √(c ^ 2 - 1)),
        sq_nonneg (s - s⁻¹ + 2 * √(c ^ 2 - 1))]
  exact key1.trans key2.symm

theorem kleinU_conj_neg {η : ℂ} (hη : ‖η‖ = 1) (t : ℝ) :
    kleinU (conj η) (-t) = (kleinU η t)⁻¹ := by
  have hq : kleinQ (conj η) (-t) = -kleinQ η t := by
    rw [kleinQ, kleinQ, kleinC_conj]
    ring
  have hrho : kleinRho (conj η) (-t) = (kleinRho η t)⁻¹ := by
    rw [kleinRho, hq, kleinRho_inv, neg_sq]
    ring
  have hη0 : η ≠ 0 := by
    intro h
    rw [h, norm_zero] at hη
    exact zero_ne_one hη
  have hconj : conj η = η⁻¹ := by
    rw [Complex.inv_def, normSq_eq_norm_sq, hη]
    simp
  rw [kleinU, kleinU, hrho, Real.sqrt_inv, hconj, mul_inv, Complex.ofReal_inv]

theorem kleinC_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) : kleinC u = 8 - (u ^ 2).re := by
  rw [kleinC, normSq_eq_norm_sq, hu, one_pow, div_one]

/-! ### The explicit map to `S³ ⊆ ℂ²` -/

/-- `e^{2πiy}`. -/
abbrev kleinAngle (y : ℝ) : ℂ := Circle.exp (2 * π * y)

theorem norm_kleinAngle (y : ℝ) : ‖kleinAngle y‖ = 1 := Circle.norm_coe _

theorem kleinAngle_ne_zero (y : ℝ) : kleinAngle y ≠ 0 := Circle.coe_ne_zero _

/-- The normalising factor `e^{πi(x + ½ - y)} / √(2 (1 + ρ))`. -/
def kleinLam (x y t : ℝ) : ℂ :=
  (((√(2 * (1 + kleinRho (kleinAngle y) t)))⁻¹ : ℝ) : ℂ) * Circle.exp (π * (x + 1 / 2 - y))

/-- The point `λ (U - 1, U + 1)` of `S³` with model point `(e^{2πix}, kleinU (e^{2πiy}) t)`. -/
def kleinW (x y t : ℝ) : ℂ × ℂ :=
  (kleinLam x y t * (kleinU (kleinAngle y) t - 1), kleinLam x y t * (kleinU (kleinAngle y) t + 1))

theorem kleinLam_ne_zero (x y t : ℝ) : kleinLam x y t ≠ 0 := by
  refine mul_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero ?_)) (Circle.coe_ne_zero _)
  exact (Real.sqrt_pos.mpr (by linarith [kleinRho_pos (kleinAngle y) t])).ne'

theorem norm_sq_kleinLam (x y t : ℝ) :
    ‖kleinLam x y t‖ ^ 2 = (2 * (1 + kleinRho (kleinAngle y) t))⁻¹ := by
  have hpos : 0 ≤ 2 * (1 + kleinRho (kleinAngle y) t) := by
    linarith [kleinRho_pos (kleinAngle y) t]
  rw [kleinLam, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    inv_pow, Real.sq_sqrt hpos]

theorem norm_sq_kleinW (x y t : ℝ) :
    ‖(kleinW x y t).1‖ ^ 2 + ‖(kleinW x y t).2‖ ^ 2 = 1 := by
  set U := kleinU (kleinAngle y) t
  have hU : normSq U = kleinRho (kleinAngle y) t := normSq_kleinU (norm_kleinAngle y) t
  have hpar : normSq (U - 1) + normSq (U + 1) = 2 * normSq U + 2 := by
    simp only [normSq_apply, Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im,
      Complex.one_re, Complex.one_im]
    ring
  have hpos : 0 < 1 + kleinRho (kleinAngle y) t := by linarith [kleinRho_pos (kleinAngle y) t]
  simp only [kleinW, norm_mul, mul_pow, norm_sq_kleinLam]
  rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, ← mul_add, hpar, hU]
  field_simp
  ring

theorem kleinLam_sq (x y t : ℝ) :
    kleinLam x y t ^ 2 = -(((√(2 * (1 + kleinRho (kleinAngle y) t)))⁻¹ ^ 2 : ℝ) : ℂ) *
      kleinAngle x * (kleinAngle y)⁻¹ := by
  have hE : (Circle.exp (π * (x + 1 / 2 - y)) : ℂ) ^ 2 = -kleinAngle x * (kleinAngle y)⁻¹ := by
    simp only [kleinAngle, Circle.coe_exp]
    rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
    have h : ((2 : ℕ) : ℂ) * (↑(π * (x + 1 / 2 - y)) * I) =
        ↑(2 * π * x) * I + -(↑(2 * π * y) * I) + π * I := by
      push_cast
      ring
    rw [h, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  rw [kleinLam, mul_pow, hE, Complex.ofReal_pow]
  ring

theorem kleinW_sq_sub_sq (x y t : ℝ) :
    (kleinW x y t).1 ^ 2 - (kleinW x y t).2 ^ 2 =
      ((4 * √(kleinRho (kleinAngle y) t) * (√(2 * (1 + kleinRho (kleinAngle y) t)))⁻¹ ^ 2 : ℝ) :
        ℂ) * kleinAngle x := by
  have hd : (kleinW x y t).1 ^ 2 - (kleinW x y t).2 ^ 2 =
      -4 * kleinU (kleinAngle y) t * kleinLam x y t ^ 2 := by
    simp only [kleinW]
    ring
  rw [hd, kleinLam_sq, kleinU]
  have hA := kleinAngle_ne_zero y
  push_cast
  field_simp

theorem kleinW_sq_sub_sq_ne_zero (x y t : ℝ) :
    (kleinW x y t).1 ^ 2 - (kleinW x y t).2 ^ 2 ≠ 0 := by
  rw [kleinW_sq_sub_sq]
  refine mul_ne_zero (Complex.ofReal_ne_zero.mpr ?_) (kleinAngle_ne_zero x)
  have h1 := Real.sqrt_pos.mpr (kleinRho_pos (kleinAngle y) t)
  have h2 : 0 < (√(2 * (1 + kleinRho (kleinAngle y) t)))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (by linarith [kleinRho_pos (kleinAngle y) t]))
  positivity

theorem modelFibrePoint_kleinW (x y t : ℝ) :
    GC.Seifert.modelFibrePoint (kleinW x y t) = kleinAngle x := by
  have h1 := Real.sqrt_pos.mpr (kleinRho_pos (kleinAngle y) t)
  have h2 : 0 < (√(2 * (1 + kleinRho (kleinAngle y) t)))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (by linarith [kleinRho_pos (kleinAngle y) t]))
  set r : ℝ := 4 * √(kleinRho (kleinAngle y) t) * (√(2 * (1 + kleinRho (kleinAngle y) t)))⁻¹ ^ 2
  have hr : 0 < r := by positivity
  rw [GC.Seifert.modelFibrePoint, kleinW_sq_sub_sq, norm_mul, norm_kleinAngle, mul_one,
    Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  exact mul_div_cancel_left₀ _ hr'

theorem modelAnnulusPoint_kleinW (x y t : ℝ) :
    GC.Seifert.modelAnnulusPoint (kleinW x y t) = kleinU (kleinAngle y) t := by
  have hl := kleinLam_ne_zero x y t
  rw [GC.Seifert.modelAnnulusPoint, kleinW]
  dsimp only
  have h2 : kleinLam x y t * (kleinU (kleinAngle y) t - 1) -
      kleinLam x y t * (kleinU (kleinAngle y) t + 1) = -2 * kleinLam x y t := by ring
  rw [h2, div_eq_iff (mul_ne_zero (by norm_num) hl)]
  ring

theorem modelPoint_kleinW (x y t : ℝ) :
    GC.Seifert.modelPoint (kleinW x y t) = (kleinAngle x, kleinU (kleinAngle y) t) :=
  Prod.ext (modelFibrePoint_kleinW x y t) (modelAnnulusPoint_kleinW x y t)

/-- `kleinW` is smooth. -/
theorem contDiff_kleinW :
    ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => kleinW q.1.1 q.1.2 q.2) := by
  have hexp : ∀ {f : (ℝ × ℝ) × ℝ → ℝ}, ContDiff ℝ ∞ f →
      ContDiff ℝ ∞ (fun q => (Circle.exp (f q) : ℂ)) := by
    intro f hf
    simp only [Circle.coe_exp]
    exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp hf).mul contDiff_const)
  have hx : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => q.1.1) := contDiff_fst.comp contDiff_fst
  have hy : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => q.1.2) := contDiff_snd.comp contDiff_fst
  have ht : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => q.2) := contDiff_snd
  have hA : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => kleinAngle q.1.2) :=
    hexp (contDiff_const.mul hy)
  have hC : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => kleinC (kleinAngle q.1.2)) := by
    have he : (fun q : (ℝ × ℝ) × ℝ => kleinC (kleinAngle q.1.2)) =
        fun q => 8 - ((kleinAngle q.1.2) ^ 2).re := by
      funext q
      exact kleinC_of_norm_eq_one (norm_kleinAngle _)
    rw [he]
    exact contDiff_const.sub (Complex.reCLM.contDiff.comp (hA.pow 2))
  have hQ : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => kleinQ (kleinAngle q.1.2) q.2) :=
    ht.mul ((hC.pow 2).sub contDiff_const |>.sqrt fun q =>
      (kleinC_sq_sub_one_pos (kleinAngle q.1.2)).ne')
  have hRho : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => kleinRho (kleinAngle q.1.2) q.2) :=
    hQ.add ((contDiff_const.add (hQ.pow 2)).sqrt fun q => by positivity)
  have hU : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => kleinU (kleinAngle q.1.2) q.2) := by
    refine (Complex.ofRealCLM.contDiff.comp ?_).mul hA
    exact hRho.sqrt fun q => (kleinRho_pos _ _).ne'
  have hLam : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => kleinLam q.1.1 q.1.2 q.2) := by
    refine (Complex.ofRealCLM.contDiff.comp ?_).mul
      (hexp (contDiff_const.mul ((hx.add contDiff_const).sub hy)))
    refine ContDiff.inv ((contDiff_const.mul (contDiff_const.add hRho)).sqrt fun q => ?_) fun q => ?_
    · linarith [kleinRho_pos (kleinAngle q.1.2) q.2]
    · exact (Real.sqrt_pos.mpr (by linarith [kleinRho_pos (kleinAngle q.1.2) q.2])).ne'
  exact (hLam.mul (hU.sub contDiff_const)).prodMk (hLam.mul (hU.add contDiff_const))

end DifferentialGeometry.Geometry.Collapse.ZeroModel.Klein

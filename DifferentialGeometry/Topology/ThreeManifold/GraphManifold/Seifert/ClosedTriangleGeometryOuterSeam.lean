import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryPunctured
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryData

/-!
# The outer seam model, its full inverse and the outer apex identity

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§1, with review 23 §2.1–2.3). For a filling at the outer hole of a three-holed block, with slope
`(p, q)`, `p = P > 0`, and Bézout column `(a, b)`, `p b - a q = 1`, X13's seam model is
`outerFwd (v, w) = ((7/2 - |v|^P/2) unit(v)^(-p) w^a, unit(v)^(-q) w^b)`
(`seamModel_eq_outerSeamDir`). Its full inverse is
`outerBwd (u, ζ) = ((7 - 2|u|)^(1/P) η^(-b) ζ^a, η^(-q) ζ^p)`, `η = unit u`, from the inverse
matrix `[[-b, a], [-q, p]]`: the two are mutually inverse smooth maps between
`{0 < |v|, |v|^P < 7} × S¹` and `{0 < |u| < 7/2} × S¹` (`outerPartial`). At the outer cone,
with `α = e^{iπ/P}`, `outerFwd (α ω e(aσ), e(Pσ)) = (outerGerm_P ω, e^{-iπq/P} unit(ω)^(-q) e(σ))`
(`outerFwd_apex`), `e(σ) = exp(2πiσ)`: the base is CF's `compactOuterGerm`, the fibre carries the
constant phase `e^{-iπq/P}`. For charts `C`, `C.outerSeamInv m` composed with the tube is the
product chart on the part `outerCollarRadius < |u| < 3` of the outer collar
(`tubeMap_outerSeamInv`), where `outerCollarRadius = max (7/2 - (1 + ε)^P/2) (5/2)`.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

section OuterSeam

variable (P : ℕ) (p q a b : ℤ)

def outerFwd (y : ℂ × Circle) : ℂ × Circle :=
  ((((7 / 2 - ‖y.1‖ ^ P / 2 : ℝ)) : ℂ) * ((unitOf y.1 ^ (-p) * y.2 ^ a : Circle) : ℂ),
    unitOf y.1 ^ (-q) * y.2 ^ b)

def outerBwd (y : ℂ × Circle) : ℂ × Circle :=
  ((((7 - 2 * ‖y.1‖) ^ ((P : ℝ)⁻¹) : ℝ) : ℂ) * ((unitOf y.1 ^ (-b) * y.2 ^ a : Circle) : ℂ),
    unitOf y.1 ^ (-q) * y.2 ^ p)

variable {P p q a b}

theorem norm_outerBwd_fst {y : ℂ × Circle} (hy : ‖y.1‖ < 7 / 2) :
    ‖(outerBwd P p q a b y).1‖ = (7 - 2 * ‖y.1‖) ^ ((P : ℝ)⁻¹) := by
  rw [outerBwd, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg]
  exact Real.rpow_nonneg (by linarith) _

theorem outerBwd_fst_ne_zero {y : ℂ × Circle} (hy : ‖y.1‖ < 7 / 2) :
    (outerBwd P p q a b y).1 ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_outerBwd_fst hy]
  exact (Real.rpow_pos_of_pos (by linarith) _).ne'

theorem unitOf_outerBwd_fst {y : ℂ × Circle} (hy : ‖y.1‖ < 7 / 2) :
    unitOf (outerBwd P p q a b y).1 = unitOf y.1 ^ (-b) * y.2 ^ a :=
  unitOf_ofReal_mul (Real.rpow_pos_of_pos (by linarith) _) _

theorem norm_outerFwd_fst {y : ℂ × Circle} (hy : ‖y.1‖ ^ P < 7) :
    ‖(outerFwd P p q a b y).1‖ = 7 / 2 - ‖y.1‖ ^ P / 2 := by
  rw [outerFwd, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg]
  linarith

theorem unitOf_outerFwd_fst {y : ℂ × Circle} (hy : ‖y.1‖ ^ P < 7) :
    unitOf (outerFwd P p q a b y).1 = unitOf y.1 ^ (-p) * y.2 ^ a :=
  unitOf_ofReal_mul (by linarith) _

variable (hP : P ≠ 0) (hdet : p * b - a * q = 1)
include hdet

include hP in
theorem outerFwd_outerBwd {y : ℂ × Circle} (hy : ‖y.1‖ < 7 / 2) :
    outerFwd P p q a b (outerBwd P p q a b y) = y := by
  have hu := unitOf_outerBwd_fst (P := P) (p := p) (q := q) (a := a) (b := b) hy
  have hpos : 0 < 7 - 2 * ‖y.1‖ := by linarith
  have hpow : ‖(outerBwd P p q a b y).1‖ ^ P = 7 - 2 * ‖y.1‖ := by
    rw [norm_outerBwd_fst hy, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le,
      inv_mul_cancel₀ (by exact_mod_cast hP), Real.rpow_one]
  apply Prod.ext
  · change ((((7 / 2 - ‖(outerBwd P p q a b y).1‖ ^ P / 2 : ℝ)) : ℂ) *
      ((unitOf (outerBwd P p q a b y).1 ^ (-p) * (outerBwd P p q a b y).2 ^ a : Circle) : ℂ)) =
        y.1
    rw [hpow, hu]
    have hcirc : (unitOf y.1 ^ (-b) * y.2 ^ a) ^ (-p) * (unitOf y.1 ^ (-q) * y.2 ^ p) ^ a =
        unitOf y.1 := by
      rw [circle_mul_zpow_mul, circle_mul_zpow_mul, circle_zpow_mul_zpow_mul,
        circle_zpow_congr _ _ (show -b * -p + -q * a = 1 by linear_combination hdet)
          (show a * -p + p * a = 0 by ring), zpow_one, zpow_zero, mul_one]
    change ((((7 / 2 - (7 - 2 * ‖y.1‖) / 2 : ℝ)) : ℂ) *
      (((unitOf y.1 ^ (-b) * y.2 ^ a) ^ (-p) * (unitOf y.1 ^ (-q) * y.2 ^ p) ^ a : Circle) : ℂ)) =
        y.1
    rw [hcirc]
    have h := norm_smul_unitOf y.1
    rw [Complex.real_smul] at h
    rw [show ((7 / 2 - (7 - 2 * ‖y.1‖) / 2 : ℝ) : ℂ) = ((‖y.1‖ : ℝ) : ℂ) by push_cast; ring, h]
  · change unitOf (outerBwd P p q a b y).1 ^ (-q) * (unitOf y.1 ^ (-q) * y.2 ^ p) ^ b = y.2
    rw [hu, circle_mul_zpow_mul, circle_mul_zpow_mul, circle_zpow_mul_zpow_mul,
      circle_zpow_congr _ _ (show -b * -q + -q * b = 0 by ring)
        (show a * -q + p * b = 1 by linear_combination hdet), zpow_zero, zpow_one, one_mul]

include hP in
theorem outerBwd_outerFwd {y : ℂ × Circle} (hy : ‖y.1‖ ^ P < 7) :
    outerBwd P p q a b (outerFwd P p q a b y) = y := by
  have hu := unitOf_outerFwd_fst (P := P) (p := p) (q := q) (a := a) (b := b) hy
  have hn := norm_outerFwd_fst (P := P) (p := p) (q := q) (a := a) (b := b) hy
  apply Prod.ext
  · change ((((7 - 2 * ‖(outerFwd P p q a b y).1‖) ^ ((P : ℝ)⁻¹) : ℝ)) : ℂ) *
      ((unitOf (outerFwd P p q a b y).1 ^ (-b) * (outerFwd P p q a b y).2 ^ a : Circle) : ℂ) =
        y.1
    rw [hn, hu]
    have hr : (7 - 2 * (7 / 2 - ‖y.1‖ ^ P / 2)) ^ ((P : ℝ)⁻¹) = ‖y.1‖ := by
      rw [show 7 - 2 * (7 / 2 - ‖y.1‖ ^ P / 2) = ‖y.1‖ ^ P by ring, ← Real.rpow_natCast,
        ← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ (by exact_mod_cast hP), Real.rpow_one]
    have hcirc : (unitOf y.1 ^ (-p) * y.2 ^ a) ^ (-b) * (unitOf y.1 ^ (-q) * y.2 ^ b) ^ a =
        unitOf y.1 := by
      rw [circle_mul_zpow_mul, circle_mul_zpow_mul, circle_zpow_mul_zpow_mul,
        circle_zpow_congr _ _ (show -p * -b + -q * a = 1 by linear_combination hdet)
          (show a * -b + b * a = 0 by ring), zpow_one, zpow_zero, mul_one]
    change (((7 - 2 * (7 / 2 - ‖y.1‖ ^ P / 2)) ^ ((P : ℝ)⁻¹) : ℝ) : ℂ) *
      (((unitOf y.1 ^ (-p) * y.2 ^ a) ^ (-b) * (unitOf y.1 ^ (-q) * y.2 ^ b) ^ a : Circle) : ℂ) =
        y.1
    rw [hr, hcirc]
    have h := norm_smul_unitOf y.1
    rwa [Complex.real_smul] at h
  · change unitOf (outerFwd P p q a b y).1 ^ (-q) * (unitOf y.1 ^ (-q) * y.2 ^ b) ^ p = y.2
    rw [hu, circle_mul_zpow_mul, circle_mul_zpow_mul, circle_zpow_mul_zpow_mul,
      circle_zpow_congr _ _ (show -p * -q + -q * p = 0 by ring)
        (show a * -q + b * p = 1 by linear_combination hdet), zpow_zero, zpow_one, one_mul]

omit hdet

theorem contMDiffOn_outerFwd :
    ContMDiffOn PlaneCircleModel PlaneCircleModel ∞ (outerFwd P p q a b) {y | y.1 ≠ 0} := by
  intro y hy
  have hy' : y.1 ≠ 0 := hy
  have hU : ContMDiffAt PlaneCircleModel (𝓡 1) ∞ (fun y : ℂ × Circle => unitOf y.1) y :=
    (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hy')).comp y contMDiff_fst.contMDiffAt
  have hN : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℝ) ∞
      (fun y : ℂ × Circle => 7 / 2 - ‖y.1‖ ^ P / 2) y := by
    have h1 : ContDiffAt ℝ ∞ (fun z : ℂ => 7 / 2 - ‖z‖ ^ P / 2) y.1 :=
      contDiffAt_const.sub (((contDiffAt_norm ℝ hy').pow P).div_const 2)
    exact h1.contMDiffAt.comp y contMDiff_fst.contMDiffAt
  have hcoe : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
      (fun y : ℂ × Circle => ((unitOf y.1 ^ (-p) * y.2 ^ a : Circle) : ℂ)) y :=
    contMDiff_circle_coe.contMDiffAt.comp y
      ((((contMDiff_circle_zpow (-p)).contMDiffAt).comp y hU).mul
        (((contMDiff_circle_zpow a).contMDiffAt).comp y contMDiff_snd.contMDiffAt))
  have hreal : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
      (fun y : ℂ × Circle => ((7 / 2 - ‖y.1‖ ^ P / 2 : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contMDiff.contMDiffAt.comp y hN
  have h1 : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
      (fun y : ℂ × Circle => (outerFwd P p q a b y).1) y :=
    chartContMDiffComplexMul.contMDiffAt.comp y (hreal.prodMk_space hcoe)
  have h2 : ContMDiffAt PlaneCircleModel (𝓡 1) ∞
      (fun y : ℂ × Circle => (outerFwd P p q a b y).2) y :=
    (((contMDiff_circle_zpow (-q)).contMDiffAt).comp y hU).mul
      (((contMDiff_circle_zpow b).contMDiffAt).comp y contMDiff_snd.contMDiffAt)
  exact (h1.prodMk h2).contMDiffWithinAt

theorem contMDiffOn_outerBwd :
    ContMDiffOn PlaneCircleModel PlaneCircleModel ∞ (outerBwd P p q a b)
      {y | y.1 ≠ 0 ∧ ‖y.1‖ < 7 / 2} := by
  intro y hy
  obtain ⟨hy', hy7⟩ := hy
  have hU : ContMDiffAt PlaneCircleModel (𝓡 1) ∞ (fun y : ℂ × Circle => unitOf y.1) y :=
    (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hy')).comp y contMDiff_fst.contMDiffAt
  have hpos : 0 < 7 - 2 * ‖y.1‖ := by linarith
  have hN : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℝ) ∞
      (fun y : ℂ × Circle => (7 - 2 * ‖y.1‖) ^ ((P : ℝ)⁻¹)) y := by
    have h0 : ContDiffAt ℝ ∞ (fun z : ℂ => 7 - 2 * ‖z‖) y.1 :=
      contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_norm ℝ hy'))
    have h1 : ContDiffAt ℝ ∞ ((fun x : ℝ => x ^ ((P : ℝ)⁻¹)) ∘ (fun z : ℂ => 7 - 2 * ‖z‖)) y.1 :=
      (Real.contDiffAt_rpow_const_of_ne hpos.ne').comp y.1 h0
    exact h1.contMDiffAt.comp y contMDiff_fst.contMDiffAt
  have hcoe : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
      (fun y : ℂ × Circle => ((unitOf y.1 ^ (-b) * y.2 ^ a : Circle) : ℂ)) y :=
    contMDiff_circle_coe.contMDiffAt.comp y
      ((((contMDiff_circle_zpow (-b)).contMDiffAt).comp y hU).mul
        (((contMDiff_circle_zpow a).contMDiffAt).comp y contMDiff_snd.contMDiffAt))
  have hreal : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
      (fun y : ℂ × Circle => (((7 - 2 * ‖y.1‖) ^ ((P : ℝ)⁻¹) : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contMDiff.contMDiffAt.comp y hN
  have h1 : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
      (fun y : ℂ × Circle => (outerBwd P p q a b y).1) y :=
    chartContMDiffComplexMul.contMDiffAt.comp y (hreal.prodMk_space hcoe)
  have h2 : ContMDiffAt PlaneCircleModel (𝓡 1) ∞
      (fun y : ℂ × Circle => (outerBwd P p q a b y).2) y :=
    (((contMDiff_circle_zpow (-q)).contMDiffAt).comp y hU).mul
      (((contMDiff_circle_zpow p).contMDiffAt).comp y contMDiff_snd.contMDiffAt)
  exact (h1.prodMk h2).contMDiffWithinAt

theorem outerBwd_mem_target {y : ℂ × Circle} (hy : y.1 ≠ 0 ∧ ‖y.1‖ < 7 / 2) (hP : P ≠ 0) :
    (outerBwd P p q a b y).1 ≠ 0 ∧ ‖(outerBwd P p q a b y).1‖ ^ P < 7 := by
  refine ⟨outerBwd_fst_ne_zero hy.2, ?_⟩
  have hpos : 0 < 7 - 2 * ‖y.1‖ := by linarith [hy.2]
  rw [norm_outerBwd_fst hy.2, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le,
    inv_mul_cancel₀ (by exact_mod_cast hP), Real.rpow_one]
  have := norm_pos_iff.mpr hy.1
  linarith

theorem outerFwd_mem_source {y : ℂ × Circle} (hy : y.1 ≠ 0 ∧ ‖y.1‖ ^ P < 7) :
    (outerFwd P p q a b y).1 ≠ 0 ∧ ‖(outerFwd P p q a b y).1‖ < 7 / 2 := by
  rw [← norm_ne_zero_iff, norm_outerFwd_fst hy.2]
  have : 0 < ‖y.1‖ ^ P := pow_pos (norm_pos_iff.mpr hy.1) _
  constructor <;> linarith

include hP hdet in
def outerPartial :
    PartialDiffeomorph PlaneCircleModel PlaneCircleModel (ℂ × Circle) (ℂ × Circle) ∞ where
  toFun := outerBwd P p q a b
  invFun := outerFwd P p q a b
  source := {y | y.1 ≠ 0 ∧ ‖y.1‖ < 7 / 2}
  target := {y | y.1 ≠ 0 ∧ ‖y.1‖ ^ P < 7}
  map_source' _ hy := outerBwd_mem_target hy hP
  map_target' _ hy := outerFwd_mem_source hy
  left_inv' _ hy := outerFwd_outerBwd hP hdet hy.2
  right_inv' _ hy := outerBwd_outerFwd hP hdet hy.2
  open_source := (isOpen_ne.preimage continuous_fst).inter
    (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const)
  open_target := (isOpen_ne.preimage continuous_fst).inter
    (isOpen_lt ((continuous_norm.comp continuous_fst).pow P) continuous_const)
  contMDiffOn_toFun := contMDiffOn_outerBwd
  contMDiffOn_invFun := contMDiffOn_outerFwd.mono fun _ hy => hy.1

include hP hdet in
theorem isLocalDiffeomorphAt_outerBwd {y : ℂ × Circle} (hy0 : y.1 ≠ 0) (hy : ‖y.1‖ < 7 / 2) :
    IsLocalDiffeomorphAt PlaneCircleModel PlaneCircleModel ∞ (outerBwd P p q a b) y :=
  (outerPartial hP hdet).isLocalDiffeomorphAt PlaneCircleModel PlaneCircleModel ∞ ⟨hy0, hy⟩

theorem conj_div_norm_eq_unitOf_inv {η : ℂ} (hη : η ≠ 0) :
    conj η / (‖η‖ : ℂ) = (((unitOf η)⁻¹ : Circle) : ℂ) := by
  rw [Circle.coe_inv_eq_conj]
  have h : ((‖η‖ : ℝ) : ℂ) * (unitOf η : ℂ) = η := by
    have := norm_smul_unitOf η
    rwa [Complex.real_smul] at this
  have hn : ((‖η‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hη).ne'
  calc conj η / ((‖η‖ : ℝ) : ℂ) =
        conj (((‖η‖ : ℝ) : ℂ) * (unitOf η : ℂ)) / ((‖η‖ : ℝ) : ℂ) := by rw [h]
    _ = conj (unitOf η : ℂ) := by
      rw [map_mul, Complex.conj_ofReal]
      field_simp

theorem circle_exp_pow (n : ℤ) (t : ℝ) : Circle.exp t ^ n = Circle.exp (n * t) := by
  rw [← Circle.exp_intCast_mul]

include hdet in
theorem outerFwd_apex (hP : P ≠ 0) (hpP : p = P) (η : ℂ) (hη : η ≠ 0) (s : ℝ) :
    outerFwd P p q a b ((Circle.exp (Real.pi / P) : ℂ) * η *
        (Circle.exp (2 * Real.pi * (a * s)) : ℂ), Circle.exp (2 * Real.pi * (P * s))) =
      (compactOuterGerm P η,
        Circle.exp (-(Real.pi * q / P)) * unitOf η ^ (-q) * Circle.exp (2 * Real.pi * s)) := by
  have hu : unitOf ((Circle.exp (Real.pi / P) : ℂ) * η *
      (Circle.exp (2 * Real.pi * (a * s)) : ℂ)) =
      Circle.exp (Real.pi / P) * unitOf η * Circle.exp (2 * Real.pi * (a * s)) := by
    rw [unitOf_mul (mul_ne_zero (Circle.coe_ne_zero _) hη) (Circle.coe_ne_zero _),
      unitOf_mul (Circle.coe_ne_zero _) hη, unitOf_circle, unitOf_circle]
  have hnorm : ‖(Circle.exp (Real.pi / P) : ℂ) * η *
      (Circle.exp (2 * Real.pi * (a * s)) : ℂ)‖ = ‖η‖ := by
    rw [norm_mul, norm_mul, Circle.norm_coe, Circle.norm_coe, one_mul, mul_one]
  have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast hP
  apply Prod.ext
  · change ((((7 / 2 - ‖(Circle.exp (Real.pi / P) : ℂ) * η *
        (Circle.exp (2 * Real.pi * (a * s)) : ℂ)‖ ^ P / 2 : ℝ)) : ℂ) *
      ((unitOf ((Circle.exp (Real.pi / P) : ℂ) * η *
        (Circle.exp (2 * Real.pi * (a * s)) : ℂ)) ^ (-p) *
          Circle.exp (2 * Real.pi * (P * s)) ^ a : Circle) : ℂ)) = compactOuterGerm P η
    have key : unitOf ((Circle.exp (Real.pi / P) : ℂ) * η *
        (Circle.exp (2 * Real.pi * (a * s)) : ℂ)) ^ (-p) *
          Circle.exp (2 * Real.pi * (P * s)) ^ a =
        Circle.exp (-Real.pi) * (unitOf η)⁻¹ ^ P := by
      rw [hu, mul_zpow, mul_zpow, circle_exp_pow, circle_exp_pow, circle_exp_pow, hpP,
        mul_assoc (_ * _), ← Circle.exp_add]
      have hz : ((-(P : ℤ) : ℤ) : ℝ) * (2 * Real.pi * (a * s)) +
          ((a : ℤ) : ℝ) * (2 * Real.pi * (P * s)) = 0 := by
        push_cast
        ring
      have hpi : ((-(P : ℤ) : ℤ) : ℝ) * (Real.pi / P) = -Real.pi := by
        push_cast
        field_simp
      rw [hz, Circle.exp_zero, mul_one, hpi, inv_pow, ← zpow_natCast, ← zpow_neg]
    rw [hnorm, key]
    unfold compactOuterGerm
    rw [conj_div_norm_eq_unitOf_inv hη, ← Circle.coe_pow, Circle.coe_mul, Circle.coe_exp]
    have he : Complex.exp ((-Real.pi : ℝ) * Complex.I) = -1 := by
      rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    rw [he]
    ring
  · change unitOf ((Circle.exp (Real.pi / P) : ℂ) * η *
        (Circle.exp (2 * Real.pi * (a * s)) : ℂ)) ^ (-q) *
      Circle.exp (2 * Real.pi * (P * s)) ^ b = _
    rw [hu, mul_zpow, mul_zpow, circle_exp_pow, circle_exp_pow, circle_exp_pow]
    have hdet' : (P : ℝ) * b - a * q = 1 := by
      rw [hpP] at hdet
      exact_mod_cast hdet
    have hz : ((-q : ℤ) : ℝ) * (2 * Real.pi * (a * s)) + (b : ℝ) * (2 * Real.pi * (P * s)) =
        2 * Real.pi * s := by
      push_cast
      linear_combination (2 * Real.pi * s) * hdet'
    have hq : ((-q : ℤ) : ℝ) * (Real.pi / P) = -(Real.pi * q / P) := by
      push_cast
      ring
    rw [hq, mul_assoc, mul_assoc, ← Circle.exp_add, hz]
    ac_rfl

end OuterSeam

end GC.Seifert

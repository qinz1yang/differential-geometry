import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryMap

/-!
# The inner seam model and its inverse

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §1 and
§3.1, with review 21 §4.1). For a filling at an inner hole of centre `c`, with slope `(p, q)`,
`p = P > 0`, and Bézout column `(a, b)`, `p b - a q = 1`, X13's seam model is
`seamFwd (v, w) = (c + |v|^P/2 · unit(v)^p w^(-a), unit(v)^(-q) w^b)` (`seamModel_eq_seamFwd`).
Its inverse on the whole non-central region is
`seamBwd (ζ, t) = ((2|ζ - c|)^(1/P) U^b t^a, U^q t^p)` with `U = unit(ζ - c)` (review 21's
formula `v = r U^b t^a`, `w = U^q t^p`, from the inverse matrix `[[b, a], [q, p]]`). The two are
mutually inverse smooth maps between `{v ≠ 0} × S¹` and `{ζ ≠ c} × S¹` (`seamPartial`, a
`PartialDiffeomorph`). At a cone apex, `seamFwd (η e(aσ), e(Pσ)) = (c + η^P/2, e(σ) unit(η)^(-q))`
(`seamFwd_apex`), with `e(σ) = exp(2πiσ)`.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology ComplexConjugate

namespace GC.Seifert

section CircleAlgebra

theorem circle_mul_zpow_mul (x y : Circle) (a b n : ℤ) :
    (x ^ a * y ^ b) ^ n = x ^ (a * n) * y ^ (b * n) := by
  rw [mul_zpow, ← zpow_mul, ← zpow_mul]

theorem circle_zpow_mul_zpow_mul (x y : Circle) (a b c e : ℤ) :
    x ^ a * y ^ b * (x ^ c * y ^ e) = x ^ (a + c) * y ^ (b + e) := by
  rw [zpow_add, zpow_add]
  ac_rfl

theorem circle_zpow_congr (x y : Circle) {a b c e : ℤ} (h1 : a = c) (h2 : b = e) :
    x ^ a * y ^ b = x ^ c * y ^ e := by
  rw [h1, h2]

end CircleAlgebra

section Seam

variable (c : ℂ) (P : ℕ) (p q a b : ℤ)

def seamFwd (y : ℂ × Circle) : ℂ × Circle :=
  (c + ((‖y.1‖ ^ P / 2 : ℝ) : ℂ) * ((unitOf y.1 ^ p * y.2 ^ (-a) : Circle) : ℂ),
    unitOf y.1 ^ (-q) * y.2 ^ b)

def seamBwd (y : ℂ × Circle) : ℂ × Circle :=
  ((((2 * ‖y.1 - c‖) ^ ((P : ℝ)⁻¹) : ℝ) : ℂ) * ((unitOf (y.1 - c) ^ b * y.2 ^ a : Circle) : ℂ),
    unitOf (y.1 - c) ^ q * y.2 ^ p)

variable {c P p q a b}

theorem norm_seamBwd_fst (y : ℂ × Circle) :
    ‖(seamBwd c P p q a b y).1‖ = (2 * ‖y.1 - c‖) ^ ((P : ℝ)⁻¹) := by
  rw [seamBwd, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg]
  exact Real.rpow_nonneg (by positivity) _

theorem seamBwd_fst_ne_zero {y : ℂ × Circle} (hy : y.1 ≠ c) : (seamBwd c P p q a b y).1 ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_seamBwd_fst]
  have : 0 < 2 * ‖y.1 - c‖ := by
    have := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
    positivity
  exact (Real.rpow_pos_of_pos this _).ne'

theorem unitOf_seamBwd_fst {y : ℂ × Circle} (hy : y.1 ≠ c) :
    unitOf (seamBwd c P p q a b y).1 = unitOf (y.1 - c) ^ b * y.2 ^ a := by
  have : 0 < 2 * ‖y.1 - c‖ := by
    have := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
    positivity
  exact unitOf_ofReal_mul (Real.rpow_pos_of_pos this _) _

theorem norm_seamFwd_sub (y : ℂ × Circle) : ‖(seamFwd c P p q a b y).1 - c‖ = ‖y.1‖ ^ P / 2 := by
  rw [seamFwd, add_sub_cancel_left, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

theorem seamFwd_fst_ne {y : ℂ × Circle} (hy : y.1 ≠ 0) : (seamFwd c P p q a b y).1 ≠ c := by
  intro h
  have h' := norm_seamFwd_sub (c := c) (P := P) (p := p) (q := q) (a := a) (b := b) y
  rw [h, sub_self, norm_zero] at h'
  have : 0 < ‖y.1‖ ^ P / 2 := by
    have := norm_pos_iff.mpr hy
    positivity
  linarith

theorem unitOf_seamFwd_sub {y : ℂ × Circle} (hy : y.1 ≠ 0) :
    unitOf ((seamFwd c P p q a b y).1 - c) = unitOf y.1 ^ p * y.2 ^ (-a) := by
  rw [seamFwd, add_sub_cancel_left]
  have : 0 < ‖y.1‖ ^ P / 2 := by
    have := norm_pos_iff.mpr hy
    positivity
  exact unitOf_ofReal_mul this _

variable (hP : P ≠ 0) (hdet : p * b - a * q = 1)
include hdet

include hP in
theorem seamFwd_seamBwd {y : ℂ × Circle} (hy : y.1 ≠ c) :
    seamFwd c P p q a b (seamBwd c P p q a b y) = y := by
  have hne := seamBwd_fst_ne_zero (P := P) (p := p) (q := q) (a := a) (b := b) hy
  have hu := unitOf_seamBwd_fst (P := P) (p := p) (q := q) (a := a) (b := b) hy
  have hpos : 0 < 2 * ‖y.1 - c‖ := by
    have := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
    positivity
  apply Prod.ext
  · change c + ((‖(seamBwd c P p q a b y).1‖ ^ P / 2 : ℝ) : ℂ) *
      ((unitOf (seamBwd c P p q a b y).1 ^ p * (seamBwd c P p q a b y).2 ^ (-a) : Circle) : ℂ) =
        y.1
    rw [norm_seamBwd_fst, hu]
    have hpow : ((2 * ‖y.1 - c‖) ^ ((P : ℝ)⁻¹)) ^ P = 2 * ‖y.1 - c‖ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, inv_mul_cancel₀ (by exact_mod_cast hP),
        Real.rpow_one]
    have hcirc : (unitOf (y.1 - c) ^ b * y.2 ^ a) ^ p *
        (unitOf (y.1 - c) ^ q * y.2 ^ p) ^ (-a) = unitOf (y.1 - c) := by
      rw [circle_mul_zpow_mul, circle_mul_zpow_mul, circle_zpow_mul_zpow_mul]
      rw [circle_zpow_congr _ _ (show b * p + q * -a = 1 by linear_combination hdet)
        (show a * p + p * -a = 0 by ring), zpow_one, zpow_zero, mul_one]
    change c + ((((2 * ‖y.1 - c‖) ^ ((P : ℝ)⁻¹)) ^ P / 2 : ℝ) : ℂ) *
      (((unitOf (y.1 - c) ^ b * y.2 ^ a) ^ p *
        (unitOf (y.1 - c) ^ q * y.2 ^ p) ^ (-a) : Circle) : ℂ) = y.1
    rw [hpow, hcirc]
    have h := norm_smul_unitOf (y.1 - c)
    rw [Complex.real_smul] at h
    rw [show ((2 * ‖y.1 - c‖ / 2 : ℝ) : ℂ) = ((‖y.1 - c‖ : ℝ) : ℂ) by push_cast; ring, h]
    ring
  · change unitOf (seamBwd c P p q a b y).1 ^ (-q) * (unitOf (y.1 - c) ^ q * y.2 ^ p) ^ b = y.2
    rw [hu, circle_mul_zpow_mul, circle_mul_zpow_mul, circle_zpow_mul_zpow_mul,
      circle_zpow_congr _ _ (show b * -q + q * b = 0 by ring)
        (show a * -q + p * b = 1 by linear_combination hdet), zpow_zero, zpow_one, one_mul]

include hP in
theorem seamBwd_seamFwd {y : ℂ × Circle} (hy : y.1 ≠ 0) :
    seamBwd c P p q a b (seamFwd c P p q a b y) = y := by
  have hu := unitOf_seamFwd_sub (c := c) (P := P) (q := q) (b := b) (p := p) (a := a) hy
  have hn := norm_seamFwd_sub (c := c) (P := P) (q := q) (b := b) (p := p) (a := a) y
  have hpos : 0 < ‖y.1‖ := norm_pos_iff.mpr hy
  apply Prod.ext
  · change ((((2 * ‖(seamFwd c P p q a b y).1 - c‖) ^ ((P : ℝ)⁻¹) : ℝ)) : ℂ) *
      ((unitOf ((seamFwd c P p q a b y).1 - c) ^ b *
        (seamFwd c P p q a b y).2 ^ a : Circle) : ℂ) = y.1
    rw [hn, hu]
    have hr : (2 * (‖y.1‖ ^ P / 2)) ^ ((P : ℝ)⁻¹) = ‖y.1‖ := by
      rw [show 2 * (‖y.1‖ ^ P / 2) = ‖y.1‖ ^ P by ring, ← Real.rpow_natCast,
        ← Real.rpow_mul hpos.le, mul_inv_cancel₀ (by exact_mod_cast hP), Real.rpow_one]
    have hcirc : (unitOf y.1 ^ p * y.2 ^ (-a)) ^ b * (unitOf y.1 ^ (-q) * y.2 ^ b) ^ a =
        unitOf y.1 := by
      rw [circle_mul_zpow_mul, circle_mul_zpow_mul, circle_zpow_mul_zpow_mul,
        circle_zpow_congr _ _ (show p * b + -q * a = 1 by linear_combination hdet)
          (show -a * b + b * a = 0 by ring), zpow_one, zpow_zero, mul_one]
    change (((2 * (‖y.1‖ ^ P / 2)) ^ ((P : ℝ)⁻¹) : ℝ) : ℂ) *
      (((unitOf y.1 ^ p * y.2 ^ (-a)) ^ b * (unitOf y.1 ^ (-q) * y.2 ^ b) ^ a : Circle) : ℂ) = y.1
    rw [hr, hcirc]
    have h := norm_smul_unitOf y.1
    rwa [Complex.real_smul] at h
  · change unitOf ((seamFwd c P p q a b y).1 - c) ^ q * (unitOf y.1 ^ (-q) * y.2 ^ b) ^ p = y.2
    rw [hu, circle_mul_zpow_mul, circle_mul_zpow_mul, circle_zpow_mul_zpow_mul,
      circle_zpow_congr _ _ (show p * q + -q * p = 0 by ring)
        (show -a * q + b * p = 1 by linear_combination hdet), zpow_zero, zpow_one, one_mul]

omit hdet

theorem contMDiffOn_seamFwd :
    ContMDiffOn PlaneCircleModel PlaneCircleModel ∞ (seamFwd c P p q a b) {y | y.1 ≠ 0} := by
  intro y hy
  have hy' : y.1 ≠ 0 := hy
  have hU : ContMDiffAt PlaneCircleModel (𝓡 1) ∞ (fun y : ℂ × Circle => unitOf y.1) y :=
    (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hy')).comp y contMDiff_fst.contMDiffAt
  have hN : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℝ) ∞ (fun y : ℂ × Circle => ‖y.1‖ ^ P / 2) y := by
    have h1 : ContDiffAt ℝ ∞ (fun z : ℂ => ‖z‖ ^ P / 2) y.1 :=
      ((contDiffAt_norm ℝ hy').pow P).div_const 2
    exact h1.contMDiffAt.comp y contMDiff_fst.contMDiffAt
  have hcoe : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
      (fun y : ℂ × Circle => ((unitOf y.1 ^ p * y.2 ^ (-a) : Circle) : ℂ)) y :=
    contMDiff_circle_coe.contMDiffAt.comp y
      ((((contMDiff_circle_zpow p).contMDiffAt).comp y hU).mul
        (((contMDiff_circle_zpow (-a)).contMDiffAt).comp y contMDiff_snd.contMDiffAt))
  have hreal : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
      (fun y : ℂ × Circle => ((‖y.1‖ ^ P / 2 : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contMDiff.contMDiffAt.comp y hN
  have h1 : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞ (fun y : ℂ × Circle => (seamFwd c P p q a b y).1)
      y :=
    contMDiffAt_const.add (chartContMDiffComplexMul.contMDiffAt.comp y (hreal.prodMk_space hcoe))
  have h2 : ContMDiffAt PlaneCircleModel (𝓡 1) ∞ (fun y : ℂ × Circle => (seamFwd c P p q a b y).2)
      y :=
    (((contMDiff_circle_zpow (-q)).contMDiffAt).comp y hU).mul
      (((contMDiff_circle_zpow b).contMDiffAt).comp y contMDiff_snd.contMDiffAt)
  exact (h1.prodMk h2).contMDiffWithinAt

theorem contMDiffOn_seamBwd :
    ContMDiffOn PlaneCircleModel PlaneCircleModel ∞ (seamBwd c P p q a b) {y | y.1 ≠ c} := by
  intro y hy
  have hy' : y.1 - c ≠ 0 := sub_ne_zero.mpr hy
  have hsub : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞ (fun y : ℂ × Circle => y.1 - c) y :=
    (contDiff_id.sub contDiff_const).contMDiff.contMDiffAt.comp y contMDiff_fst.contMDiffAt
  have hU : ContMDiffAt PlaneCircleModel (𝓡 1) ∞ (fun y : ℂ × Circle => unitOf (y.1 - c)) y :=
    (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hy')).comp y hsub
  have hpos : 0 < 2 * ‖y.1 - c‖ := by
    have := norm_pos_iff.mpr hy'
    positivity
  have hN : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℝ) ∞
      (fun y : ℂ × Circle => (2 * ‖y.1 - c‖) ^ ((P : ℝ)⁻¹)) y := by
    have h0 : ContDiffAt ℝ ∞ (fun z : ℂ => 2 * ‖z - c‖) y.1 :=
      contDiffAt_const.mul ((contDiffAt_norm ℝ hy').comp y.1
        (contDiffAt_id.sub contDiffAt_const))
    have h1 : ContDiffAt ℝ ∞ ((fun x : ℝ => x ^ ((P : ℝ)⁻¹)) ∘ (fun z : ℂ => 2 * ‖z - c‖)) y.1 :=
      (Real.contDiffAt_rpow_const_of_ne hpos.ne').comp y.1 h0
    exact h1.contMDiffAt.comp y contMDiff_fst.contMDiffAt
  have hcoe : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
      (fun y : ℂ × Circle => ((unitOf (y.1 - c) ^ b * y.2 ^ a : Circle) : ℂ)) y :=
    contMDiff_circle_coe.contMDiffAt.comp y
      ((((contMDiff_circle_zpow b).contMDiffAt).comp y hU).mul
        (((contMDiff_circle_zpow a).contMDiffAt).comp y contMDiff_snd.contMDiffAt))
  have hreal : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
      (fun y : ℂ × Circle => (((2 * ‖y.1 - c‖) ^ ((P : ℝ)⁻¹) : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contMDiff.contMDiffAt.comp y hN
  have h1 : ContMDiffAt PlaneCircleModel 𝓘(ℝ, ℂ) ∞
      (fun y : ℂ × Circle => (seamBwd c P p q a b y).1) y :=
    chartContMDiffComplexMul.contMDiffAt.comp y (hreal.prodMk_space hcoe)
  have h2 : ContMDiffAt PlaneCircleModel (𝓡 1) ∞
      (fun y : ℂ × Circle => (seamBwd c P p q a b y).2) y :=
    (((contMDiff_circle_zpow q).contMDiffAt).comp y hU).mul
      (((contMDiff_circle_zpow p).contMDiffAt).comp y contMDiff_snd.contMDiffAt)
  exact (h1.prodMk h2).contMDiffWithinAt

include hP hdet in
def seamPartial :
    PartialDiffeomorph PlaneCircleModel PlaneCircleModel (ℂ × Circle) (ℂ × Circle) ∞ where
  toFun := seamBwd c P p q a b
  invFun := seamFwd c P p q a b
  source := {y | y.1 ≠ c}
  target := {y | y.1 ≠ 0}
  map_source' _ hy := seamBwd_fst_ne_zero hy
  map_target' _ hy := seamFwd_fst_ne hy
  left_inv' _ hy := seamFwd_seamBwd hP hdet hy
  right_inv' _ hy := seamBwd_seamFwd hP hdet hy
  open_source := isOpen_ne.preimage continuous_fst
  open_target := isOpen_ne.preimage continuous_fst
  contMDiffOn_toFun := contMDiffOn_seamBwd
  contMDiffOn_invFun := contMDiffOn_seamFwd

include hP hdet in
theorem isLocalDiffeomorphAt_seamBwd {y : ℂ × Circle} (hy : y.1 ≠ c) :
    IsLocalDiffeomorphAt PlaneCircleModel PlaneCircleModel ∞ (seamBwd c P p q a b) y :=
  (seamPartial hP hdet).isLocalDiffeomorphAt PlaneCircleModel PlaneCircleModel ∞ hy

include hdet in
theorem seamFwd_apex (hpP : p = P) (η : ℂ) (hη : η ≠ 0) (s : ℝ) :
    seamFwd c P p q a b (η * (Circle.exp (2 * Real.pi * (a * s)) : ℂ),
        Circle.exp (2 * Real.pi * (P * s))) =
      (c + η ^ P / 2, Circle.exp (2 * Real.pi * s) * unitOf η ^ (-q)) := by
  have hu : unitOf (η * (Circle.exp (2 * Real.pi * (a * s)) : ℂ)) =
      unitOf η * Circle.exp (2 * Real.pi * (a * s)) := by
    rw [unitOf_mul hη (Circle.coe_ne_zero _), unitOf_circle]
  have he : ∀ n : ℤ, ∀ t : ℝ, Circle.exp (2 * Real.pi * t) ^ n =
      Circle.exp (2 * Real.pi * (n * t)) := by
    intro n t
    rw [← Circle.exp_intCast_mul]
    congr 1
    ring
  apply Prod.ext
  · change c + ((‖η * (Circle.exp (2 * Real.pi * (a * s)) : ℂ)‖ ^ P / 2 : ℝ) : ℂ) *
      ((unitOf (η * (Circle.exp (2 * Real.pi * (a * s)) : ℂ)) ^ p *
        Circle.exp (2 * Real.pi * (P * s)) ^ (-a) : Circle) : ℂ) = c + η ^ P / 2
    rw [hu, norm_mul, Circle.norm_coe, mul_one, mul_zpow, he, he, mul_assoc, ← Circle.exp_add,
      hpP]
    have hz : 2 * Real.pi * (((P : ℤ) : ℝ) * (a * s)) + 2 * Real.pi * (((-a : ℤ) : ℝ) * (P * s)) =
        0 := by
      push_cast
      ring
    rw [hz, Circle.exp_zero, mul_one, zpow_natCast, Circle.coe_pow]
    have h := norm_smul_unitOf η
    rw [Complex.real_smul] at h
    conv_rhs => rw [← h]
    push_cast
    ring
  · change unitOf (η * (Circle.exp (2 * Real.pi * (a * s)) : ℂ)) ^ (-q) *
      Circle.exp (2 * Real.pi * (P * s)) ^ b = _
    rw [hu, mul_zpow, he, he]
    have hz : 2 * Real.pi * (((-q : ℤ) : ℝ) * (a * s)) + 2 * Real.pi * ((b : ℝ) * (P * s)) =
        2 * Real.pi * s := by
      have hdet' : (P : ℝ) * b - a * q = 1 := by
        rw [hpP] at hdet
        exact_mod_cast hdet
      push_cast
      linear_combination (2 * Real.pi * s) * hdet'
    change unitOf η ^ (-q) * Circle.exp (2 * Real.pi * (((-q : ℤ) : ℝ) * (a * s))) *
      Circle.exp (2 * Real.pi * ((b : ℝ) * (P * s))) =
        Circle.exp (2 * Real.pi * s) * unitOf η ^ (-q)
    rw [mul_assoc, ← Circle.exp_add, hz, mul_comm]

end Seam

end GC.Seifert

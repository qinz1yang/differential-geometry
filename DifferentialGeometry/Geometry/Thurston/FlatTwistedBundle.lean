import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MobiusBlockAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryFlat
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting

/-!
# The flat twisted `I`-bundle over the Klein bottle

Chapter 7, item P3, twisted half: the orientable twisted `I`-bundle `W` over the Klein bottle,
realized as `mobiusBundleCarrier = {Q ≤ 0} ⊆ L(4, -1)` (`Seifert/MobiusRefibration.lean`), is
identified with the flat model, and its boundary torus has `π₁`-image of index two.

Coordinates. `KleinBottleGroup` acts on `E³` by `(x₀, x₁, x₂) ↦ (x₀ + g/2, ±x₁ + m, ±x₂)`
(`KleinBottleGroup.smul_coords`); `TwistedKleinBundle = E³ / KleinBottleGroup` carries the
complete flat structure `twistedKleinBundleGeometry` of `Thurston/Descent.lean`. The point
`kleinLens a b v` of `L(4, -1)` is the class of the normalized pair `e^{πia} (sinh ζ, cosh ζ)`,
`2ζ = arsinh (v √(4 - cos² 2πb)) + 2πib`, with model point `(-e^{2πia}, e^{2ζ})`
(`modelPoint_kleinPoint`). On the slab `|x₂| ≤ 1` the map `kleinLensMap` is invariant
(`kleinLensMap_smul`), its fibres are the orbits (`kleinLensMap_eq_iff`), it is onto `{Q ≤ 0}`
(`exists_kleinLens_eq`), and `Q = 0` exactly on `|x₂| = 1`
(`bundleQuartic_kleinPoint_eq_zero_iff`).

Interior. `kleinOpen x = kleinLens x₀ x₁ (x₂ / √(1 + x₂²))` is smooth with the smooth local left
inverse `kleinChartAt` (branches of `arg` through `liftAngle`), so its differential is bijective
and it is a local diffeomorphism (`isLocalDiffeomorph_kleinOpen`). It descends to an injective
local diffeomorphism `kleinQuotient` of `TwistedKleinBundle` onto `{Q < 0}`, the interior of the
carrier: `mobiusKleinInteriorDiffeo`, and the complete Euclidean interior geometry
`mobiusBundle_interiorGeometry` (`mobiusBundle_interiorGeometry_model`).

Boundary. The closed slab is a simply connected quotient covering of `W` for `KleinBottleGroup`
(`isQuotientCoveringMap_kleinSlabMap`), and the plane `x₂ = 1` covers the boundary torus for the
index-two subgroup `torusTranslations` (`isQuotientCoveringMap_boundaryLift`). Naturality of
`IsQuotientCoveringMap.fundamentalGroupToMulOpposite` (`fundamentalGroupToMulOpposite_map`)
identifies the boundary map on `π₁` with `torusTranslations ≤ KleinBottleGroup`: it is injective
with image of index two (`boundary_fundamentalGroup`) for the boundary torus of any presentation
of the carrier (`mobius_boundary_fundamentalGroup`), in particular for `mobiusTwistedIBundle`
(`mobiusTwistedIBundle_boundary_fundamentalGroup`, `twistExternal_incompressible`,
`twistExternal_index_two`).
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open scoped Manifold ContDiff Topology RealInnerProductSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

namespace GC.Geometry

theorem kleinFlip_apply (x : E3) : kleinFlip x = (2 * x 0) • kleinAxis - x := by
  rw [kleinFlip, Submodule.reflection_apply, Submodule.starProjection_singleton, norm_kleinAxis]
  simp only [kleinAxis, EuclideanSpace.inner_single_left, map_one, one_mul, one_pow, div_one]
  congr 1
  rw [two_smul, ← add_smul, ← two_mul]

theorem kleinFlip_coords (x : E3) :
    kleinFlip x 0 = x 0 ∧ kleinFlip x 1 = -x 1 ∧ kleinFlip x 2 = -x 2 := by
  rw [kleinFlip_apply]
  simp [kleinAxis]
  ring

theorem kleinFlip_zpow_coords (n : ℤ) (x : E3) :
    (kleinFlip ^ n) x 0 = x 0 ∧ (kleinFlip ^ n) x 1 = ((n.negOnePow : ℤ) : ℝ) * x 1 ∧
      (kleinFlip ^ n) x 2 = ((n.negOnePow : ℤ) : ℝ) * x 2 := by
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ i hi =>
    obtain ⟨h0, h1, h2⟩ := hi (kleinFlip x)
    obtain ⟨f0, f1, f2⟩ := kleinFlip_coords x
    rw [zpow_add_one, LinearIsometryEquiv.coe_mul, Function.comp_apply, h0, h1, h2, f0, f1, f2,
      Int.negOnePow_succ]
    push_cast
    exact ⟨rfl, by ring, by ring⟩
  | pred i hi =>
    obtain ⟨h0, h1, h2⟩ := hi (kleinFlip x)
    obtain ⟨f0, f1, f2⟩ := kleinFlip_coords x
    rw [zpow_sub_one, LinearIsometryEquiv.coe_mul, Function.comp_apply, kleinFlip_inv, h0, h1, h2,
      f0, f1, f2, Int.negOnePow_sub, Int.negOnePow_one]
    push_cast
    exact ⟨rfl, by ring, by ring⟩

theorem KleinBottleGroup.smul_coords (γ : KleinBottleGroup) (x : E3) :
    (γ • x) 0 = x 0 + (γ.glide : ℝ) / 2 ∧
      (γ • x) 1 = ((γ.glide.negOnePow : ℤ) : ℝ) * x 1 + γ.shift ∧
      (γ • x) 2 = ((γ.glide.negOnePow : ℤ) : ℝ) * x 2 := by
  obtain ⟨h0, h1, h2⟩ := kleinFlip_zpow_coords γ.glide x
  rw [KleinBottleGroup.smul_def, KleinBottleGroup.linearPart, KleinBottleGroup.translationPart]
  simp only [PiLp.add_apply, PiLp.smul_apply, kleinAxis, kleinFibre, PiLp.single_apply,
    smul_eq_mul, h0, h1, h2]
  norm_num

private theorem euclidean3_ext' {x y : E3} (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2) :
    x = y := by
  ext i
  fin_cases i
  exacts [h0, h1, h2]

theorem KleinBottleGroup.smul_even (k m : ℤ) (x : E3) :
    ((⟨2 * k, m⟩ : KleinBottleGroup) • x) 0 = x 0 + k ∧
      ((⟨2 * k, m⟩ : KleinBottleGroup) • x) 1 = x 1 + m ∧
      ((⟨2 * k, m⟩ : KleinBottleGroup) • x) 2 = x 2 := by
  obtain ⟨h0, h1, h2⟩ := KleinBottleGroup.smul_coords ⟨2 * k, m⟩ x
  have hp : (2 * k).negOnePow = 1 := Int.negOnePow_even _ (even_two_mul k)
  simp only [hp] at h1 h2
  rw [h0, h1, h2]
  push_cast
  exact ⟨by ring, by ring, by ring⟩

theorem KleinBottleGroup.smul_odd (k m : ℤ) (x : E3) :
    ((⟨2 * k + 1, m⟩ : KleinBottleGroup) • x) 0 = x 0 + k + 1 / 2 ∧
      ((⟨2 * k + 1, m⟩ : KleinBottleGroup) • x) 1 = -x 1 + m ∧
      ((⟨2 * k + 1, m⟩ : KleinBottleGroup) • x) 2 = -x 2 := by
  obtain ⟨h0, h1, h2⟩ := KleinBottleGroup.smul_coords ⟨2 * k + 1, m⟩ x
  have hp : (2 * k + 1).negOnePow = -1 := Int.negOnePow_odd _ (odd_two_mul_add_one k)
  simp only [hp] at h1 h2
  rw [h0, h1, h2]
  push_cast
  exact ⟨by ring, by ring, by ring⟩

def kleinWidth (b : ℝ) : ℝ := √(4 - Real.cos (2 * Real.pi * b) ^ 2)

theorem three_le_kleinWidth_arg (b : ℝ) : 3 ≤ 4 - Real.cos (2 * Real.pi * b) ^ 2 := by
  nlinarith [Real.cos_sq_le_one (2 * Real.pi * b)]

theorem kleinWidth_pos (b : ℝ) : 0 < kleinWidth b :=
  Real.sqrt_pos.mpr (by linarith [three_le_kleinWidth_arg b])

theorem kleinWidth_sq (b : ℝ) : kleinWidth b ^ 2 = 4 - Real.cos (2 * Real.pi * b) ^ 2 :=
  Real.sq_sqrt (by linarith [three_le_kleinWidth_arg b])

theorem kleinWidth_neg (b : ℝ) : kleinWidth (-b) = kleinWidth b := by
  rw [kleinWidth, kleinWidth, mul_neg, Real.cos_neg]

theorem kleinWidth_add_int (b : ℝ) (m : ℤ) : kleinWidth (b + m) = kleinWidth b := by
  rw [kleinWidth, kleinWidth, show 2 * Real.pi * (b + m) = 2 * Real.pi * b + m * (2 * Real.pi) by
    ring, Real.cos_add_int_mul_two_pi]

def kleinHeight (b v : ℝ) : ℝ := Real.arsinh (v * kleinWidth b)

theorem kleinHeight_neg (b v : ℝ) : kleinHeight (-b) (-v) = -kleinHeight b v := by
  rw [kleinHeight, kleinHeight, kleinWidth_neg, neg_mul, Real.arsinh_neg]

theorem kleinHeight_add_int (b v : ℝ) (m : ℤ) : kleinHeight (b + m) v = kleinHeight b v := by
  rw [kleinHeight, kleinHeight, kleinWidth_add_int]

theorem sinh_kleinHeight (b v : ℝ) : Real.sinh (kleinHeight b v) = v * kleinWidth b :=
  Real.sinh_arsinh _

theorem kleinHeight_injective (b : ℝ) : Injective (kleinHeight b) := by
  intro v v' h
  have h' := congrArg Real.sinh h
  rw [sinh_kleinHeight, sinh_kleinHeight] at h'
  exact mul_right_cancel₀ (kleinWidth_pos b).ne' h'

def kleinArg (b v : ℝ) : ℂ :=
  ((kleinHeight b v / 2 : ℝ) : ℂ) + ((Real.pi * b : ℝ) : ℂ) * Complex.I

def kleinPhase (a : ℝ) : ℂ := Complex.exp (((Real.pi * a : ℝ) : ℂ) * Complex.I)

def kleinPair (a b v : ℝ) : ℂ × ℂ :=
  (kleinPhase a * Complex.sinh (kleinArg b v), kleinPhase a * Complex.cosh (kleinArg b v))

def kleinModel (a b v : ℝ) : ℂ × ℂ :=
  (-kleinPhase a ^ 2, Complex.exp (2 * kleinArg b v))

theorem kleinPhase_sq (a : ℝ) :
    kleinPhase a ^ 2 = Complex.exp (((2 * Real.pi * a : ℝ) : ℂ) * Complex.I) := by
  rw [kleinPhase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem norm_kleinPhase_sq (a : ℝ) : ‖kleinPhase a ^ 2‖ = 1 := by
  rw [kleinPhase_sq, Complex.norm_exp_ofReal_mul_I]

theorem kleinPhase_ne_zero (a : ℝ) : kleinPhase a ≠ 0 := Complex.exp_ne_zero _

theorem kleinPair_sq_sub (a b v : ℝ) :
    (kleinPair a b v).1 ^ 2 - (kleinPair a b v).2 ^ 2 = -kleinPhase a ^ 2 := by
  simp only [kleinPair]
  linear_combination (-kleinPhase a ^ 2) * Complex.cosh_sq (kleinArg b v)

theorem kleinPair_sq_sub_ne_zero (a b v : ℝ) :
    (kleinPair a b v).1 ^ 2 - (kleinPair a b v).2 ^ 2 ≠ 0 := by
  rw [kleinPair_sq_sub]
  exact neg_ne_zero.mpr (pow_ne_zero 2 (kleinPhase_ne_zero a))

theorem kleinPair_ne_zero (a b v : ℝ) : kleinPair a b v ≠ 0 := by
  intro h
  apply kleinPair_sq_sub_ne_zero a b v
  rw [h]
  simp

theorem modelFibrePoint_kleinPair (a b v : ℝ) :
    modelFibrePoint (kleinPair a b v) = -kleinPhase a ^ 2 := by
  rw [modelFibrePoint, kleinPair_sq_sub, norm_neg, norm_kleinPhase_sq, Complex.ofReal_one, div_one]

theorem modelAnnulusPoint_kleinPair (a b v : ℝ) :
    modelAnnulusPoint (kleinPair a b v) = Complex.exp (2 * kleinArg b v) := by
  have h1 : (kleinPair a b v).1 + (kleinPair a b v).2 =
      kleinPhase a * Complex.exp (kleinArg b v) := by
    simp only [kleinPair]
    rw [← mul_add, Complex.sinh_add_cosh]
  have h2 : (kleinPair a b v).1 - (kleinPair a b v).2 =
      -(kleinPhase a * Complex.exp (-kleinArg b v)) := by
    simp only [kleinPair]
    rw [← mul_sub, Complex.sinh_sub_cosh, mul_neg]
  have hne : kleinPhase a * Complex.exp (-kleinArg b v) ≠ 0 :=
    mul_ne_zero (kleinPhase_ne_zero a) (Complex.exp_ne_zero _)
  rw [modelAnnulusPoint, h1, h2, neg_div_neg_eq, div_eq_iff hne, mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

theorem modelPoint_kleinPair (a b v : ℝ) : modelPoint (kleinPair a b v) = kleinModel a b v :=
  Prod.ext (modelFibrePoint_kleinPair a b v) (modelAnnulusPoint_kleinPair a b v)

theorem modelPoint_real_smul {t : ℝ} (ht : 0 < t) (p : ℂ × ℂ) :
    modelPoint (t • p) = modelPoint p := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hd : (t • p).1 ^ 2 - (t • p).2 ^ 2 = (t : ℂ) ^ 2 * (p.1 ^ 2 - p.2 ^ 2) := by
    simp only [Prod.smul_fst, Prod.smul_snd, Complex.real_smul]
    ring
  refine Prod.ext ?_ ?_
  · simp only [modelPoint, modelFibrePoint]
    rw [hd, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le]
    push_cast
    rw [mul_div_mul_left _ _ (pow_ne_zero 2 ht')]
  · simp only [modelPoint, modelAnnulusPoint, Prod.smul_fst, Prod.smul_snd, Complex.real_smul]
    rw [← mul_add, ← mul_sub, ← mul_neg, mul_div_mul_left _ _ ht']

theorem bundleQuartic_real_smul_nonpos_iff {t : ℝ} (ht : t ≠ 0) (p : ℂ × ℂ) :
    bundleQuartic (t • p) ≤ 0 ↔ bundleQuartic p ≤ 0 := by
  rw [bundleQuartic_smul]
  have h4 : 0 < t ^ 4 := by positivity
  constructor
  · intro h
    by_contra hc
    exact absurd h (not_le.mpr (mul_pos h4 (not_le.mp hc)))
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos h4.le h

theorem bundleQuartic_real_smul_eq_zero_iff {t : ℝ} (ht : t ≠ 0) (p : ℂ × ℂ) :
    bundleQuartic (t • p) = 0 ↔ bundleQuartic p = 0 := by
  rw [bundleQuartic_smul, mul_eq_zero, or_iff_right (pow_ne_zero 4 ht)]

theorem norm_cosh_sq (s θ : ℝ) :
    ‖Complex.cosh ((s : ℂ) + (θ : ℂ) * Complex.I)‖ ^ 2 =
      Real.sinh s ^ 2 + Real.cos θ ^ 2 := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← mul_assoc,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.sq_norm, Complex.normSq_add_mul_I]
  nlinarith [Real.cosh_sq s, Real.sin_sq_add_cos_sq θ]

theorem joukowski_exp (z : ℂ) : joukowski (Complex.exp z) = 3 / 2 * Complex.cosh z := by
  rw [joukowski, ← Complex.exp_neg, Complex.cosh]
  ring

theorem two_mul_kleinArg (b v : ℝ) :
    2 * kleinArg b v = ((kleinHeight b v : ℝ) : ℂ) + ((2 * Real.pi * b : ℝ) : ℂ) * Complex.I := by
  rw [kleinArg]
  push_cast
  ring

theorem norm_joukowski_kleinArg_sq (b v : ℝ) :
    ‖joukowski (Complex.exp (2 * kleinArg b v))‖ ^ 2 =
      9 / 4 * (v ^ 2 * (4 - Real.cos (2 * Real.pi * b) ^ 2) + Real.cos (2 * Real.pi * b) ^ 2) := by
  rw [joukowski_exp, two_mul_kleinArg, norm_mul, mul_pow, norm_cosh_sq, sinh_kleinHeight, mul_pow,
    kleinWidth_sq]
  norm_num

theorem norm_joukowski_kleinArg_le_iff (b v : ℝ) :
    ‖joukowski (Complex.exp (2 * kleinArg b v))‖ ≤ 3 ↔ v ^ 2 ≤ 1 := by
  have h := norm_joukowski_kleinArg_sq b v
  have hc := three_le_kleinWidth_arg b
  have hn := norm_nonneg (joukowski (Complex.exp (2 * kleinArg b v)))
  constructor
  · intro hle
    by_contra hv
    rw [not_le] at hv
    nlinarith
  · intro hv
    nlinarith

theorem norm_joukowski_kleinArg_eq_iff (b v : ℝ) :
    ‖joukowski (Complex.exp (2 * kleinArg b v))‖ = 3 ↔ v ^ 2 = 1 := by
  have h := norm_joukowski_kleinArg_sq b v
  have hc := three_le_kleinWidth_arg b
  have hn := norm_nonneg (joukowski (Complex.exp (2 * kleinArg b v)))
  constructor
  · intro he
    rw [he] at h
    nlinarith
  · intro hv
    rw [hv] at h
    nlinarith

theorem bundleQuartic_kleinPair_nonpos_iff (a b v : ℝ) :
    bundleQuartic (kleinPair a b v) ≤ 0 ↔ v ^ 2 ≤ 1 := by
  rw [bundleQuartic_nonpos_iff (kleinPair_sq_sub_ne_zero a b v),
    ← joukowski_modelAnnulusPoint (kleinPair_sq_sub_ne_zero a b v), modelAnnulusPoint_kleinPair,
    norm_joukowski_kleinArg_le_iff]

theorem bundleQuartic_kleinPair_eq_zero_iff (a b v : ℝ) :
    bundleQuartic (kleinPair a b v) = 0 ↔ v ^ 2 = 1 := by
  rw [bundleQuartic_eq_zero_iff (kleinPair_sq_sub_ne_zero a b v),
    ← joukowski_modelAnnulusPoint (kleinPair_sq_sub_ne_zero a b v), modelAnnulusPoint_kleinPair,
    norm_joukowski_kleinArg_eq_iff]

theorem kleinPhase_add_int_sq (a : ℝ) (k : ℤ) : kleinPhase (a + k) ^ 2 = kleinPhase a ^ 2 := by
  rw [kleinPhase_sq, kleinPhase_sq, show (((2 * Real.pi * (a + k) : ℝ) : ℂ) * Complex.I) =
    ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I + k * (2 * Real.pi * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem kleinPhase_add_half_sq (a : ℝ) (k : ℤ) :
    kleinPhase (a + k + 1 / 2) ^ 2 = -kleinPhase a ^ 2 := by
  rw [kleinPhase_sq, kleinPhase_sq, show (((2 * Real.pi * (a + k + 1 / 2) : ℝ) : ℂ) * Complex.I) =
    ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I + k * (2 * Real.pi * Complex.I) +
      Real.pi * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
  ring

theorem two_mul_kleinArg_add_int (b v : ℝ) (m : ℤ) :
    2 * kleinArg (b + m) v = 2 * kleinArg b v + m * (2 * Real.pi * Complex.I) := by
  rw [two_mul_kleinArg, two_mul_kleinArg, kleinHeight_add_int]
  push_cast
  ring

theorem two_mul_kleinArg_neg_add_int (b v : ℝ) (m : ℤ) :
    2 * kleinArg (-b + m) (-v) = -(2 * kleinArg b v) + m * (2 * Real.pi * Complex.I) := by
  rw [two_mul_kleinArg, two_mul_kleinArg, kleinHeight_add_int, kleinHeight_neg]
  push_cast
  ring

theorem kleinModel_add_int (a b v : ℝ) (k m : ℤ) :
    kleinModel (a + k) (b + m) v = kleinModel a b v := by
  rw [kleinModel, kleinModel, kleinPhase_add_int_sq, two_mul_kleinArg_add_int, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem kleinModel_deck (a b v : ℝ) (k m : ℤ) :
    kleinModel (a + k + 1 / 2) (-b + m) (-v) = modelDeck (kleinModel a b v) := by
  rw [kleinModel, kleinModel, modelDeck, kleinPhase_add_half_sq, two_mul_kleinArg_neg_add_int,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_neg]

theorem exists_int_of_exp_eq {x y : ℝ}
    (h : Complex.exp ((x : ℂ) * Complex.I) = Complex.exp ((y : ℂ) * Complex.I)) :
    ∃ n : ℤ, x = y + n * (2 * Real.pi) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have him := congrArg Complex.im hn
  simp at him
  linarith

theorem kleinPhase_sq_eq_iff (a a' : ℝ) :
    kleinPhase a' ^ 2 = kleinPhase a ^ 2 → ∃ k : ℤ, a' = a + k := by
  intro h
  rw [kleinPhase_sq, kleinPhase_sq] at h
  obtain ⟨n, hn⟩ := exists_int_of_exp_eq h
  refine ⟨n, mul_left_cancel₀ (two_ne_zero' ℝ) (mul_left_cancel₀ Real.pi_ne_zero ?_)⟩
  linarith

theorem kleinPhase_sq_eq_neg_iff (a a' : ℝ) :
    kleinPhase a' ^ 2 = -kleinPhase a ^ 2 → ∃ k : ℤ, a' = a + k + 1 / 2 := by
  intro h
  rw [kleinPhase_sq, kleinPhase_sq, ← neg_one_mul, ← Complex.exp_pi_mul_I, ← Complex.exp_add,
    show Real.pi * Complex.I + ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * a + Real.pi : ℝ) : ℂ) * Complex.I by push_cast; ring] at h
  obtain ⟨n, hn⟩ := exists_int_of_exp_eq h
  refine ⟨n, mul_left_cancel₀ (two_ne_zero' ℝ) (mul_left_cancel₀ Real.pi_ne_zero ?_)⟩
  linarith

theorem kleinArg_eq_of_exp_eq (b v b' v' : ℝ) (σ : ℝ)
    (h : Complex.exp (2 * kleinArg b' v') = Complex.exp
      (((σ * kleinHeight b v : ℝ) : ℂ) + ((2 * Real.pi * (σ * b) : ℝ) : ℂ) * Complex.I)) :
    ∃ m : ℤ, kleinHeight b' v' = σ * kleinHeight b v ∧ b' = σ * b + m := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  rw [two_mul_kleinArg] at hm
  have hre : kleinHeight b' v' = σ * kleinHeight b v := by
    simpa using congrArg Complex.re hm
  have him : 2 * Real.pi * b' = 2 * Real.pi * (σ * b) + m * (2 * Real.pi) := by
    simpa using congrArg Complex.im hm
  refine ⟨m, hre, mul_left_cancel₀ (two_ne_zero' ℝ) (mul_left_cancel₀ Real.pi_ne_zero ?_)⟩
  linarith

theorem kleinModel_eq_imp (a b v a' b' v' : ℝ) (h : kleinModel a' b' v' = kleinModel a b v) :
    ∃ k m : ℤ, a' = a + k ∧ b' = b + m ∧ v' = v := by
  obtain ⟨k, hk⟩ := kleinPhase_sq_eq_iff a a' (neg_inj.mp (congrArg Prod.fst h))
  have h2 : Complex.exp (2 * kleinArg b' v') = Complex.exp
      (((1 * kleinHeight b v : ℝ) : ℂ) + ((2 * Real.pi * (1 * b) : ℝ) : ℂ) * Complex.I) := by
    rw [one_mul, one_mul, ← two_mul_kleinArg]
    exact congrArg Prod.snd h
  obtain ⟨m, hs, hb⟩ := kleinArg_eq_of_exp_eq b v b' v' 1 h2
  rw [one_mul] at hs hb
  refine ⟨k, m, hk, hb, kleinHeight_injective b ?_⟩
  rw [← hs, hb, kleinHeight_add_int]

theorem kleinModel_eq_deck_imp (a b v a' b' v' : ℝ)
    (h : kleinModel a' b' v' = modelDeck (kleinModel a b v)) :
    ∃ k m : ℤ, a' = a + k + 1 / 2 ∧ b' = -b + m ∧ v' = -v := by
  have h1 : kleinPhase a' ^ 2 = -kleinPhase a ^ 2 := by
    have := congrArg Prod.fst h
    simp only [kleinModel, modelDeck, neg_neg] at this
    rw [← this, neg_neg]
  obtain ⟨k, hk⟩ := kleinPhase_sq_eq_neg_iff a a' h1
  have h2 : Complex.exp (2 * kleinArg b' v') = Complex.exp
      (((-1 * kleinHeight b v : ℝ) : ℂ) + ((2 * Real.pi * (-1 * b) : ℝ) : ℂ) * Complex.I) := by
    have := congrArg Prod.snd h
    simp only [kleinModel, modelDeck] at this
    rw [this, ← Complex.exp_neg, two_mul_kleinArg]
    push_cast
    ring_nf
  obtain ⟨m, hs, hb⟩ := kleinArg_eq_of_exp_eq b v b' v' (-1) h2
  rw [neg_one_mul] at hs hb
  refine ⟨k, m, hk, hb, ?_⟩
  have hv : kleinHeight b (-v') = kleinHeight b v := by
    have h3 := kleinHeight_neg b (-v')
    rw [neg_neg] at h3
    have h4 := kleinHeight_add_int (-b) v' m
    rw [← hb] at h4
    linarith
  have h5 := kleinHeight_injective b hv
  linarith

local notation "E4" => EuclideanSpace ℝ (Fin 4)

def kleinVector (a b v : ℝ) : E4 := lensPair.symm (kleinPair a b v)

theorem kleinVector_ne_zero (a b v : ℝ) : kleinVector a b v ≠ 0 := by
  rw [kleinVector, Ne, lensPair.symm.map_eq_zero_iff]
  exact kleinPair_ne_zero a b v

theorem kleinVector_normalize_mem (a b v : ℝ) :
    ‖kleinVector a b v‖⁻¹ • kleinVector a b v ∈ Metric.sphere (0 : E4) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (kleinVector_ne_zero a b v))]

def kleinPoint (a b v : ℝ) : Metric.sphere (0 : E4) 1 :=
  ⟨‖kleinVector a b v‖⁻¹ • kleinVector a b v, kleinVector_normalize_mem a b v⟩

theorem lensPair_kleinPoint (a b v : ℝ) :
    lensPair (kleinPoint a b v : E4) = ‖kleinVector a b v‖⁻¹ • kleinPair a b v := by
  change lensPair (‖kleinVector a b v‖⁻¹ • lensPair.symm (kleinPair a b v)) = _
  rw [map_smul, ContinuousLinearEquiv.apply_symm_apply]

theorem kleinVector_norm_inv_pos (a b v : ℝ) : 0 < ‖kleinVector a b v‖⁻¹ :=
  inv_pos.mpr (norm_pos_iff.mpr (kleinVector_ne_zero a b v))

theorem modelPoint_kleinPoint (a b v : ℝ) :
    modelPoint (lensPair (kleinPoint a b v : E4)) = kleinModel a b v := by
  rw [lensPair_kleinPoint, modelPoint_real_smul (kleinVector_norm_inv_pos a b v),
    modelPoint_kleinPair]

theorem bundleQuartic_kleinPoint_nonpos_iff (a b v : ℝ) :
    bundleQuartic (lensPair (kleinPoint a b v : E4)) ≤ 0 ↔ v ^ 2 ≤ 1 := by
  rw [lensPair_kleinPoint, bundleQuartic_real_smul_nonpos_iff
    (kleinVector_norm_inv_pos a b v).ne', bundleQuartic_kleinPair_nonpos_iff]

theorem bundleQuartic_kleinPoint_eq_zero_iff (a b v : ℝ) :
    bundleQuartic (lensPair (kleinPoint a b v : E4)) = 0 ↔ v ^ 2 = 1 := by
  rw [lensPair_kleinPoint, bundleQuartic_real_smul_eq_zero_iff
    (kleinVector_norm_inv_pos a b v).ne', bundleQuartic_kleinPair_eq_zero_iff]

def kleinLens (a b v : ℝ) : mobiusLens.{u}.Carrier :=
  lensUp (mobiusLensGroup.projection (kleinPoint a b v))

theorem mobiusBundleFunction_kleinLens (a b v : ℝ) :
    mobiusBundleFunction (kleinLens.{u} a b v) = bundleQuartic (lensPair (kleinPoint a b v : E4)) :=
  rfl

theorem lensUp_injective : Injective lensUp.{u} := fun q q' h => by
  rw [← lensDown_lensUp.{u} q, h, lensDown_lensUp]

theorem kleinLens_eq_iff {a b v a' b' v' : ℝ} (hv : v ^ 2 ≤ 1) (hv' : v' ^ 2 ≤ 1) :
    kleinLens.{u} a b v = kleinLens a' b' v' ↔
      kleinModel a' b' v' = kleinModel a b v ∨
        kleinModel a' b' v' = modelDeck (kleinModel a b v) := by
  rw [kleinLens, kleinLens, lensUp_injective.eq_iff, projection_eq_iff_modelPoint _ _
    ((bundleQuartic_kleinPoint_nonpos_iff a b v).mpr hv)
    ((bundleQuartic_kleinPoint_nonpos_iff a' b' v').mpr hv'), modelPoint_kleinPoint,
    modelPoint_kleinPoint]

def kleinLensMap (x : E3) : mobiusLens.{u}.Carrier := kleinLens (x 0) (x 1) (x 2)

theorem kleinLensMap_smul {x : E3} (hx : x 2 ^ 2 ≤ 1) (γ : KleinBottleGroup) :
    kleinLensMap.{u} (γ • x) = kleinLensMap x := by
  have hsq : (γ • x) 2 ^ 2 = x 2 ^ 2 := by
    rw [(KleinBottleGroup.smul_coords γ x).2.2, mul_pow]
    rcases Int.units_eq_one_or γ.glide.negOnePow with h | h <;> simp [h]
  refine ((kleinLens_eq_iff hx (hsq.symm ▸ hx)).mpr ?_).symm
  rcases Int.even_or_odd' γ.glide with ⟨k, hk | hk⟩
  · left
    obtain ⟨h0, h1, h2⟩ := KleinBottleGroup.smul_even k γ.shift x
    have hγ : γ = ⟨2 * k, γ.shift⟩ := KleinBottleGroup.ext hk rfl
    rw [hγ, h0, h1, h2]
    exact kleinModel_add_int _ _ _ _ _
  · right
    obtain ⟨h0, h1, h2⟩ := KleinBottleGroup.smul_odd k γ.shift x
    have hγ : γ = ⟨2 * k + 1, γ.shift⟩ := KleinBottleGroup.ext hk rfl
    rw [hγ, h0, h1, h2]
    exact kleinModel_deck _ _ _ _ _

theorem kleinLensMap_eq_iff {x y : E3} (hx : x 2 ^ 2 ≤ 1) (hy : y 2 ^ 2 ≤ 1) :
    kleinLensMap.{u} x = kleinLensMap y ↔ ∃ γ : KleinBottleGroup, γ • y = x := by
  constructor
  · intro h
    rcases (kleinLens_eq_iff hx hy).mp h with h' | h'
    · obtain ⟨k, m, h0, h1, h2⟩ := kleinModel_eq_imp _ _ _ _ _ _ h'
      refine ⟨⟨2 * (-k), -m⟩, ?_⟩
      obtain ⟨g0, g1, g2⟩ := KleinBottleGroup.smul_even (-k) (-m) y
      refine euclidean3_ext' ?_ ?_ ?_
      · rw [g0, h0]; push_cast; ring
      · rw [g1, h1]; push_cast; ring
      · rw [g2, h2]
    · obtain ⟨k, m, h0, h1, h2⟩ := kleinModel_eq_deck_imp _ _ _ _ _ _ h'
      refine ⟨⟨2 * (-k - 1) + 1, m⟩, ?_⟩
      obtain ⟨g0, g1, g2⟩ := KleinBottleGroup.smul_odd (-k - 1) m y
      refine euclidean3_ext' ?_ ?_ ?_
      · rw [g0, h0]; push_cast; ring
      · rw [g1, h1]; ring
      · rw [g2, h2]; ring
  · rintro ⟨γ, rfl⟩
    exact kleinLensMap_smul hy γ

theorem norm_modelFibrePoint {p : ℂ × ℂ} (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0) :
    ‖modelFibrePoint p‖ = 1 := by
  rw [modelFibrePoint, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hab)]

theorem modelAnnulusPoint_ne_zero {p : ℂ × ℂ} (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0) :
    modelAnnulusPoint p ≠ 0 := by
  obtain ⟨h1, h2⟩ := sub_ne_zero_of_sq_sub_sq_ne_zero hab
  rw [modelAnnulusPoint]
  exact div_ne_zero (neg_ne_zero.mpr h2) h1

theorem exists_kleinLens_eq (y : mobiusLens.{u}.Carrier) (hy : mobiusBundleFunction y ≤ 0) :
    ∃ x : E3, x 2 ^ 2 ≤ 1 ∧ kleinLensMap x = y := by
  obtain ⟨p, hp⟩ := mobiusLensGroup.projection_surjective (lensDown y)
  have hq : bundleQuartic (lensPair (p : E4)) ≤ 0 := by
    change lensDescend bundleQuartic bundleQuartic_invariant (lensDown y) ≤ 0 at hy
    rwa [← hp] at hy
  have hab := sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero p) hq
  set z := modelFibrePoint (lensPair (p : E4)) with hzdef
  set w := modelAnnulusPoint (lensPair (p : E4)) with hwdef
  have hz : ‖-z‖ = 1 := by rw [norm_neg]; exact norm_modelFibrePoint hab
  have hw : w ≠ 0 := modelAnnulusPoint_ne_zero hab
  have hJ : ‖joukowski w‖ ≤ 3 := by
    rw [hwdef, joukowski_modelAnnulusPoint hab, ← bundleQuartic_nonpos_iff hab]
    exact hq
  set a := Complex.arg (-z) / (2 * Real.pi)
  set b := Complex.arg w / (2 * Real.pi)
  set s := Real.log ‖w‖
  set v := Real.sinh s / kleinWidth b
  have hs : kleinHeight b v = s := by
    rw [kleinHeight, div_mul_cancel₀ _ (kleinWidth_pos b).ne', Real.arsinh_sinh]
  have ha : -kleinPhase a ^ 2 = z := by
    rw [kleinPhase_sq, show 2 * Real.pi * a = Complex.arg (-z) by
      simp only [a]; field_simp]
    have h := Complex.norm_mul_exp_arg_mul_I (-z)
    rw [hz, Complex.ofReal_one, one_mul] at h
    rw [h, neg_neg]
  have hb : Complex.exp (2 * kleinArg b v) = w := by
    rw [two_mul_kleinArg, hs, show 2 * Real.pi * b = Complex.arg w by simp only [b]; field_simp]
    have h := Complex.exp_log hw
    rw [Complex.log] at h
    exact h
  have hmodel : kleinModel a b v = modelPoint (lensPair (p : E4)) := Prod.ext ha hb
  have hv : v ^ 2 ≤ 1 := by
    rw [← norm_joukowski_kleinArg_le_iff, hb]
    exact hJ
  refine ⟨!₂[a, b, v], by simpa using hv, ?_⟩
  have hx : kleinLensMap.{u} !₂[a, b, v] = kleinLens.{u} a b v := rfl
  rw [hx, kleinLens, ← lensUp_lensDown y, ← hp]
  congr 1
  refine (projection_eq_iff_modelPoint _ _ ((bundleQuartic_kleinPoint_nonpos_iff a b v).mpr hv)
    hq).mpr (Or.inl ?_)
  rw [modelPoint_kleinPoint, hmodel]


attribute [local instance] fact_finrank_euclideanSpace_four

theorem contDiff_kleinWidth : ContDiff ℝ ∞ kleinWidth :=
  (contDiff_const.sub ((Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).pow 2)).sqrt
    fun b h => by
      simp only [Function.comp_apply, id] at h
      linarith [three_le_kleinWidth_arg b]

private theorem contDiff_coord (j : Fin 3) : ContDiff ℝ ∞ (fun q : E3 => q j) :=
  (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff

theorem contDiff_kleinPairCoord :
    ContDiff ℝ ∞ (fun x : E3 => kleinPair (x 0) (x 1) (x 2)) := by
  have hw : ContDiff ℝ ∞ (fun x : E3 => kleinWidth (x 1)) :=
    contDiff_kleinWidth.comp (contDiff_coord 1)
  have hh : ContDiff ℝ ∞ (fun x : E3 => kleinHeight (x 1) (x 2)) :=
    Real.contDiff_arsinh.comp ((contDiff_coord 2).mul hw)
  have harg : ContDiff ℝ ∞ (fun x : E3 => kleinArg (x 1) (x 2)) :=
    (Complex.ofRealCLM.contDiff.comp (hh.div_const 2)).add
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_coord 1))).mul
        contDiff_const)
  have hph : ContDiff ℝ ∞ (fun x : E3 => kleinPhase (x 0)) :=
    Complex.contDiff_exp.comp
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_coord 0))).mul
        contDiff_const)
  exact (hph.mul ((Complex.contDiff_sinh.restrict_scalars ℝ).comp harg)).prodMk
    (hph.mul ((Complex.contDiff_cosh.restrict_scalars ℝ).comp harg))

theorem contDiff_kleinVectorCoord :
    ContDiff ℝ ∞ (fun x : E3 => kleinVector (x 0) (x 1) (x 2)) :=
  lensPair.symm.contDiff.comp contDiff_kleinPairCoord

theorem contMDiff_kleinPointCoord :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : E3 => kleinPoint (x 0) (x 1) (x 2)) := by
  have hv := contDiff_kleinVectorCoord
  have hn : ContDiff ℝ ∞ (fun x : E3 => ‖kleinVector (x 0) (x 1) (x 2)‖⁻¹) :=
    (hv.norm ℝ fun x => kleinVector_ne_zero _ _ _).inv
      fun x => norm_ne_zero_iff.mpr (kleinVector_ne_zero _ _ _)
  exact (hn.smul hv).contMDiff.codRestrict_sphere fun x => kleinVector_normalize_mem _ _ _

theorem contMDiff_kleinLensMap : ContMDiff (𝓡 3) (𝓡 3) ∞ kleinLensMap.{u} :=
  contMDiff_lensUp.comp
    (mobiusLensGroup.projection_isLocalDiffeomorph.contMDiff.comp contMDiff_kleinPointCoord)

theorem continuous_kleinLensMap : Continuous kleinLensMap.{u} :=
  contMDiff_kleinLensMap.continuous


theorem KleinBottleGroup.smul_two_sq (γ : KleinBottleGroup) (x : E3) :
    (γ • x) 2 ^ 2 = x 2 ^ 2 := by
  rw [(KleinBottleGroup.smul_coords γ x).2.2, mul_pow]
  rcases Int.units_eq_one_or γ.glide.negOnePow with h | h <;> simp [h]

def kleinSlab : SubMulAction KleinBottleGroup E3 where
  carrier := {x | x 2 ^ 2 ≤ 1}
  smul_mem' γ x hx := by
    change (γ • x) 2 ^ 2 ≤ 1
    rw [KleinBottleGroup.smul_two_sq]
    exact hx

theorem mem_kleinSlab {x : E3} : x ∈ kleinSlab ↔ x 2 ^ 2 ≤ 1 := Iff.rfl

instance : ContinuousConstSMul KleinBottleGroup kleinSlab :=
  ⟨fun γ => ((continuous_const_smul γ).comp continuous_subtype_val).subtype_mk _⟩

theorem convex_kleinSlab : Convex ℝ (kleinSlab : Set E3) := by
  intro x hx y hy a b ha hb hab
  change x 2 ^ 2 ≤ 1 at hx
  change y 2 ^ 2 ≤ 1 at hy
  change (a • x + b • y) 2 ^ 2 ≤ 1
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_nonneg ha hb, sq_nonneg (x 2 - y 2), mul_nonneg (mul_nonneg ha hb)
    (sq_nonneg (x 2 - y 2))]

instance : SimplyConnectedSpace kleinSlab :=
  haveI := convex_kleinSlab.contractibleSpace ⟨0, by simp [mem_kleinSlab]⟩
  inferInstance

def kleinSlabMap (x : kleinSlab) : mobiusBundleSet.{u} :=
  ⟨kleinLensMap x.1, (bundleQuartic_kleinPoint_nonpos_iff _ _ _).mpr x.2⟩

theorem continuous_kleinSlabMap : Continuous kleinSlabMap.{u} :=
  (continuous_kleinLensMap.comp continuous_subtype_val).subtype_mk _

theorem exists_smul_unitSquare (x : E3) : ∃ k m : ℤ,
    0 ≤ ((⟨2 * k, m⟩ : KleinBottleGroup) • x) 0 ∧ ((⟨2 * k, m⟩ : KleinBottleGroup) • x) 0 ≤ 1 ∧
    0 ≤ ((⟨2 * k, m⟩ : KleinBottleGroup) • x) 1 ∧ ((⟨2 * k, m⟩ : KleinBottleGroup) • x) 1 ≤ 1 ∧
    ((⟨2 * k, m⟩ : KleinBottleGroup) • x) 2 = x 2 := by
  obtain ⟨h0, h1, h2⟩ := KleinBottleGroup.smul_even (-⌊x 0⌋) (-⌊x 1⌋) x
  refine ⟨-⌊x 0⌋, -⌊x 1⌋, ?_, ?_, ?_, ?_, h2⟩
  · rw [h0]; push_cast; linarith [Int.floor_le (x 0)]
  · rw [h0]; push_cast; linarith [Int.lt_floor_add_one (x 0)]
  · rw [h1]; push_cast; linarith [Int.floor_le (x 1)]
  · rw [h1]; push_cast; linarith [Int.lt_floor_add_one (x 1)]

def kleinBox : Set E3 := {x | x 2 ^ 2 ≤ 1 ∧ 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1}

theorem isCompact_kleinBox : IsCompact kleinBox := by
  have hc (j : Fin 3) : Continuous (fun q : E3 => q j) := (contDiff_coord j).continuous
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le ((hc 2).pow 2) continuous_const).inter
      ((isClosed_le continuous_const (hc 0)).inter ((isClosed_le (hc 0) continuous_const).inter
      ((isClosed_le continuous_const (hc 1)).inter (isClosed_le (hc 1) continuous_const))))
  · refine (Metric.isBounded_closedBall (x := (0 : E3)) (r := 2)).subset fun x hx => ?_
    obtain ⟨h2, h0, h0', h1, h1'⟩ := hx
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsq := EuclideanSpace.norm_sq_eq x
    rw [Fin.sum_univ_three, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
      sq_abs] at hsq
    nlinarith [norm_nonneg x]

theorem exists_kleinBox_eq (y : mobiusBundleSet.{u}) :
    ∃ x ∈ kleinBox, kleinLensMap.{u} x = y.1 := by
  obtain ⟨x, hx, hxy⟩ := exists_kleinLens_eq y.1 y.2
  obtain ⟨k, m, h0, h0', h1, h1', h2⟩ := exists_smul_unitSquare x
  refine ⟨_, ⟨by rw [h2]; exact hx, h0, h0', h1, h1'⟩, ?_⟩
  rw [kleinLensMap_smul hx, hxy]

theorem isQuotientMap_kleinSlabMap : Topology.IsQuotientMap kleinSlabMap.{u} := by
  have : CompactSpace kleinBox := isCompact_iff_compactSpace.mp isCompact_kleinBox
  let g : kleinBox → kleinSlab := fun z => ⟨z.1, z.2.1⟩
  have hg : Continuous g := continuous_subtype_val.subtype_mk _
  have hcont : Continuous (kleinSlabMap.{u} ∘ g) := continuous_kleinSlabMap.comp hg
  refine Topology.IsQuotientMap.of_comp hg continuous_kleinSlabMap ?_
  refine hcont.isClosedMap.isQuotientMap hcont fun y => ?_
  obtain ⟨x, hx, hxy⟩ := exists_kleinBox_eq y
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem kleinSlabMap_eq_iff {x y : kleinSlab} :
    kleinSlabMap.{u} x = kleinSlabMap y ↔ x ∈ MulAction.orbit KleinBottleGroup y := by
  rw [Subtype.ext_iff]
  change kleinLensMap x.1 = kleinLensMap y.1 ↔ _
  rw [kleinLensMap_eq_iff x.2 y.2]
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨γ, Subtype.ext hγ⟩
  · rintro ⟨γ, hγ⟩
    exact ⟨γ, congrArg Subtype.val hγ⟩

theorem KleinBottleGroup.eq_one_of_dist_lt {γ : KleinBottleGroup} {x : E3}
    (h : dist (γ • x) x < 1 / 2) : γ = 1 := by
  obtain ⟨h0, h1, -⟩ := KleinBottleGroup.smul_coords γ x
  have d0 := PiLp.dist_apply_le (γ • x) x 0
  have d1 := PiLp.dist_apply_le (γ • x) x 1
  rw [Real.dist_eq, h0, show x 0 + (γ.glide : ℝ) / 2 - x 0 = γ.glide / 2 by ring] at d0
  have hg : γ.glide = 0 := by
    have h' : |(γ.glide : ℝ)| < 1 := by
      rw [abs_div, abs_two] at d0
      linarith
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast h')
  rw [Real.dist_eq, h1, hg] at d1
  have hs : γ.shift = 0 := by
    have h' : |(γ.shift : ℝ)| < 1 := by
      simp only [Int.negOnePow_zero, Units.val_one, Int.cast_one, one_mul,
        add_sub_cancel_left] at d1
      linarith
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast h')
  exact KleinBottleGroup.ext hg hs

theorem isQuotientCoveringMap_kleinSlabMap :
    IsQuotientCoveringMap kleinSlabMap.{u} KleinBottleGroup where
  __ := isQuotientMap_kleinSlabMap
  apply_eq_iff_mem_orbit := kleinSlabMap_eq_iff
  disjoint e := by
    refine ⟨Metric.ball e (1 / 4), Metric.ball_mem_nhds e (by norm_num), fun γ hγ => ?_⟩
    obtain ⟨_, ⟨z, hz, rfl⟩, hγz⟩ := hγ
    rw [Metric.mem_ball] at hz hγz
    refine KleinBottleGroup.eq_one_of_dist_lt (x := z.1) ?_
    have h := dist_triangle (γ • z) e z
    rw [dist_comm e z] at h
    exact lt_of_le_of_lt h (by linarith)


section Naturality

variable {P S T W H G : Type*} [TopologicalSpace P] [TopologicalSpace S] [TopologicalSpace T]
  [TopologicalSpace W] [Group H] [Group G] [MulAction H P] [MulAction G S] {r : P → T}
  {p : S → W}

theorem monodromy_naturality (hr : IsCoveringMap r) (hp : IsCoveringMap p) (f : C(T, W))
    (L : C(P, S)) (hL : ∀ z, p (L z) = f (r z)) {t : T} (c : Path.Homotopic.Quotient t t)
    (z : r ⁻¹' {t}) :
    hp.monodromy (c.map f) ⟨L z, (hL z).trans (congrArg f z.2)⟩ =
      ⟨L (hr.monodromy c z), (hL _).trans (congrArg f (hr.monodromy c z).2)⟩ := by
  induction c using Quotient.ind with
  | _ c =>
  refine hp.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk
    { toFun := fun s => L (hr.liftPath c z (c.source.trans z.2.symm) s)
      continuous_toFun := by fun_prop
      source' := by simp only [hr.liftPath_zero]
      target' := rfl }) ?_
  refine congrArg Path.Homotopic.Quotient.mk ?_
  ext s
  change p (L (hr.liftPath c z (c.source.trans z.2.symm) s)) = f (c s)
  rw [hL]
  exact congrArg f (congrFun (hr.liftPath_lifts _ _ _) s)

theorem fundamentalGroupToMulOpposite_map (hr : IsQuotientCoveringMap r H)
    (hp : IsQuotientCoveringMap p G) (f : C(T, W)) (L : C(P, S)) (φ : H →* G)
    (hL : ∀ z, p (L z) = f (r z)) (hLφ : ∀ (h : H) z, L (h • z) = φ h • L z) {t : T}
    (z : r ⁻¹' {t}) (γ : FundamentalGroup T t) :
    hp.fundamentalGroupToMulOpposite ⟨L z, (hL z).trans (congrArg f z.2)⟩
        (FundamentalGroup.map f t γ) =
      MulOpposite.op (φ (hr.fundamentalGroupToMulOpposite z γ).unop) := by
  rw [IsQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff, MulOpposite.unop_op,
    ← hLφ, IsQuotientCoveringMap.unop_fundamentalGroupToMulOpposite_smul]
  exact (congrArg Subtype.val
    (monodromy_naturality hr.isCoveringMap hp.isCoveringMap f L hL γ z)).symm

end Naturality


def kleinTop : SubMulAction torusTranslations E3 where
  carrier := {x | x 2 = 1}
  smul_mem' γ x hx := by
    change ((γ : KleinBottleGroup) • x) 2 = 1
    rw [(KleinBottleGroup.smul_coords _ x).2.2, Int.negOnePow_even _ γ.2, show x 2 = 1 from hx]
    simp

theorem mem_kleinTop {x : E3} : x ∈ kleinTop ↔ x 2 = 1 := Iff.rfl

instance : ContinuousConstSMul torusTranslations kleinTop :=
  ⟨fun γ => ((continuous_const_smul γ).comp continuous_subtype_val).subtype_mk _⟩

theorem convex_kleinTop : Convex ℝ (kleinTop : Set E3) := by
  intro x hx y hy a b ha hb hab
  change (a • x + b • y) 2 = 1
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [show x 2 = 1 from hx, show y 2 = 1 from hy]
  linarith

instance : SimplyConnectedSpace kleinTop :=
  haveI := convex_kleinTop.contractibleSpace ⟨EuclideanSpace.single 2 1, by simp [mem_kleinTop]⟩
  inferInstance

theorem top_mem_slab (z : kleinTop) : z.1 ∈ kleinSlab := by
  rw [mem_kleinSlab, show z.1 2 = 1 from z.2]
  norm_num

def topToSlab : C(kleinTop, kleinSlab) :=
  ⟨fun z => ⟨z.1, top_mem_slab z⟩, continuous_subtype_val.subtype_mk top_mem_slab⟩

theorem kleinLensMap_top (z : kleinTop) : mobiusBundleFunction (kleinLensMap.{u} z.1) = 0 :=
  (bundleQuartic_kleinPoint_eq_zero_iff _ _ _).mpr (by rw [show z.1 2 = 1 from z.2]; norm_num)

theorem exists_kleinTopBox_eq (y : mobiusLens.{u}.Carrier) (hy : mobiusBundleFunction y = 0) :
    ∃ x : E3, x 2 = 1 ∧ 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1 ∧ kleinLensMap.{u} x = y := by
  obtain ⟨x, hx, hxy⟩ := exists_kleinLens_eq y hy.le
  have h1 : x 2 ^ 2 = 1 := by
    rw [← bundleQuartic_kleinPoint_eq_zero_iff (x 0) (x 1)]
    rw [← hxy] at hy
    exact hy
  obtain ⟨x', hx'2, hx'⟩ : ∃ x' : E3, x' 2 = 1 ∧ kleinLensMap.{u} x' = y := by
    have hfac : (x 2 - 1) * (x 2 + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp hfac with h | h
    · exact ⟨x, by linarith, hxy⟩
    · refine ⟨(⟨2 * 0 + 1, 0⟩ : KleinBottleGroup) • x, ?_, ?_⟩
      · rw [(KleinBottleGroup.smul_odd 0 0 x).2.2]
        linarith
      · rw [kleinLensMap_smul hx, hxy]
  obtain ⟨k, m, h0, h0', h1', h1'', h2⟩ := exists_smul_unitSquare x'
  refine ⟨_, by rw [h2, hx'2], h0, h0', h1', h1'', ?_⟩
  rw [kleinLensMap_smul (by rw [hx'2]; norm_num), hx']

theorem mem_range_op_subtype (b : KleinBottleGroupᵐᵒᵖ) :
    b ∈ (MonoidHom.op torusTranslations.subtype).range ↔ Even b.unop.glide := by
  constructor
  · rintro ⟨x, rfl⟩
    exact x.unop.2
  · intro h
    exact ⟨MulOpposite.op ⟨b.unop, h⟩, rfl⟩

theorem index_range_op_subtype : (MonoidHom.op torusTranslations.subtype).range.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨MulOpposite.op ⟨1, 0⟩, fun b => ?_⟩
  rw [mem_range_op_subtype, mem_range_op_subtype, MulOpposite.unop_mul, MulOpposite.unop_op,
    KleinBottleGroup.mul_glide, add_comm, Int.even_add_one]
  by_cases h : Even b.unop.glide <;> simp [h]

section Boundary

variable (f : C(Torus, mobiusBundleSet.{u}))
  (hrange : ∀ y, y ∈ range f ↔ mobiusBundleFunction y.1 = 0)

def boundaryLift (z : kleinTop) : range f :=
  ⟨kleinSlabMap (topToSlab z), (hrange _).mpr (kleinLensMap_top z)⟩

theorem isQuotientCoveringMap_boundaryLift :
    IsQuotientCoveringMap (boundaryLift f hrange) torusTranslations where
  toIsQuotientMap := by
    have hc (j : Fin 3) : Continuous (fun q : E3 => q j) := (contDiff_coord j).continuous
    let K : Set E3 := {x | x 2 = 1 ∧ 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1}
    have hK : IsCompact K := by
      refine isCompact_kleinBox.of_isClosed_subset ?_ ?_
      · exact (isClosed_eq (hc 2) continuous_const).inter
          ((isClosed_le continuous_const (hc 0)).inter ((isClosed_le (hc 0) continuous_const).inter
          ((isClosed_le continuous_const (hc 1)).inter (isClosed_le (hc 1) continuous_const))))
      · rintro x ⟨h2, h0, h0', h1, h1'⟩
        exact ⟨by rw [h2]; norm_num, h0, h0', h1, h1'⟩
    have : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hl : Continuous (boundaryLift f hrange) :=
      (continuous_kleinSlabMap.comp topToSlab.continuous).subtype_mk _
    let g : K → kleinTop := fun z => ⟨z.1, z.2.1⟩
    have hg : Continuous g := continuous_subtype_val.subtype_mk _
    have hcont : Continuous (boundaryLift f hrange ∘ g) := hl.comp hg
    refine Topology.IsQuotientMap.of_comp hg hl ?_
    refine hcont.isClosedMap.isQuotientMap hcont fun y => ?_
    obtain ⟨x, h2, h0, h0', h1, h1', hxy⟩ := exists_kleinTopBox_eq y.1.1 ((hrange y.1).mp y.2)
    exact ⟨⟨x, h2, h0, h0', h1, h1'⟩, Subtype.ext (Subtype.ext hxy)⟩
  apply_eq_iff_mem_orbit {x y} := by
    have hx : x.1 2 ^ 2 ≤ 1 := by rw [show x.1 2 = 1 from x.2]; norm_num
    have hy : y.1 2 ^ 2 ≤ 1 := by rw [show y.1 2 = 1 from y.2]; norm_num
    constructor
    · intro h
      have h' : kleinLensMap.{u} x.1 = kleinLensMap y.1 :=
        congrArg Subtype.val (congrArg Subtype.val h)
      obtain ⟨γ, hγ⟩ := (kleinLensMap_eq_iff hx hy).mp h'
      have h2 := (KleinBottleGroup.smul_coords γ y.1).2.2
      rw [hγ, show x.1 2 = 1 from x.2, show y.1 2 = 1 from y.2, mul_one] at h2
      have hev : Even γ.glide := by
        rw [← Int.negOnePow_eq_one_iff]
        rcases Int.units_eq_one_or γ.glide.negOnePow with h | h
        · exact h
        · rw [h] at h2
          norm_num at h2
      exact ⟨⟨γ, hev⟩, Subtype.ext hγ⟩
    · rintro ⟨γ, rfl⟩
      exact Subtype.ext (Subtype.ext (kleinLensMap_smul hy (γ : KleinBottleGroup)))
  disjoint e := by
    refine ⟨Metric.ball e (1 / 4), Metric.ball_mem_nhds e (by norm_num), fun γ hγ => ?_⟩
    obtain ⟨_, ⟨z, hz, rfl⟩, hγz⟩ := hγ
    rw [Metric.mem_ball] at hz hγz
    refine Subtype.ext (KleinBottleGroup.eq_one_of_dist_lt (x := z.1) ?_)
    have h := dist_triangle (γ • z) e z
    rw [dist_comm e z] at h
    exact lt_of_le_of_lt h (by linarith)

include hrange in
theorem boundary_fundamentalGroup (hf : Injective f) (t : Torus) :
    Injective (FundamentalGroup.map f t) ∧ (FundamentalGroup.map f t).range.index = 2 := by
  let e : Torus ≃ₜ range f := (f.continuous.isClosedEmbedding hf).isEmbedding.toHomeomorph
  have he : ∀ w, f (e.symm w) = w.1 := fun w => congrArg Subtype.val (e.apply_symm_apply w)
  have hq := (isQuotientCoveringMap_boundaryLift f hrange).homeomorph_comp e.symm
  have hL : ∀ z, kleinSlabMap.{u} (topToSlab z) = f ((e.symm ∘ boundaryLift f hrange) z) :=
    fun z => (he (boundaryLift f hrange z)).symm
  obtain ⟨z₀, hz₀⟩ := hq.surjective t
  let z : (e.symm ∘ boundaryLift f hrange) ⁻¹' {t} := ⟨z₀, hz₀⟩
  have key := fundamentalGroupToMulOpposite_map hq isQuotientCoveringMap_kleinSlabMap f topToSlab
    torusTranslations.subtype hL (fun γ w => rfl) z
  have hΨr := hq.fundamentalGroupToMulOpposite_surjective z
  have hΨr' := hq.fundamentalGroupToMulOpposite_injective z
  have hΨp := isQuotientCoveringMap_kleinSlabMap.{u}.fundamentalGroupToMulOpposite_injective
    ⟨topToSlab z, (hL z).trans (congrArg f z.2)⟩
  have hΨp' := isQuotientCoveringMap_kleinSlabMap.{u}.fundamentalGroupToMulOpposite_surjective
    ⟨topToSlab z, (hL z).trans (congrArg f z.2)⟩
  constructor
  · intro γ γ' h
    apply hΨr'
    have h' := congrArg (isQuotientCoveringMap_kleinSlabMap.{u}.fundamentalGroupToMulOpposite
      ⟨topToSlab z, (hL z).trans (congrArg f z.2)⟩) h
    rw [key, key] at h'
    exact MulOpposite.unop_injective (Subtype.val_injective (MulOpposite.op_injective h'))
  · have hr : (FundamentalGroup.map f t).range =
        (MonoidHom.op torusTranslations.subtype).range.comap
          (isQuotientCoveringMap_kleinSlabMap.{u}.fundamentalGroupToMulOpposite
            ⟨topToSlab z, (hL z).trans (congrArg f z.2)⟩) := by
      ext γ
      constructor
      · rintro ⟨δ, rfl⟩
        exact ⟨_, (key δ).symm⟩
      · rintro ⟨x, hx⟩
        obtain ⟨δ, rfl⟩ := hΨr x
        exact ⟨δ, hΨp (by rw [key]; exact hx)⟩
    rw [hr, Subgroup.index_comap_of_surjective _ hΨp', index_range_op_subtype]

end Boundary


theorem mobius_boundary_fundamentalGroup
    (T : TorusPresentation mobiusBundleCarrier.{u}) [Subsingleton (Fin T.externalCount)]
    (i : Fin T.externalCount) (t : Torus) :
    Injective (FundamentalGroup.map (T.external.boundaryMap i) t) ∧
      (FundamentalGroup.map (T.external.boundaryMap i) t).range.index = 2 := by
  refine boundary_fundamentalGroup (T.external.boundaryMap i) (fun y => ?_)
    (T.external.torusMap_isEmbedding i).injective t
  have h1 : y ∈ T.external.image ↔ (𝓡∂ 3).IsBoundaryPoint y :=
    (Set.ext_iff.mp T.external_exhausted y).symm
  rw [mobiusBundleSet_isBoundaryPoint_iff] at h1
  refine Iff.trans ?_ h1
  constructor
  · intro h
    exact Set.mem_iUnion.mpr ⟨i, h⟩
  · intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
    exact Subsingleton.elim j i ▸ hj

theorem twistExternal_incompressible : twistExternal.{u}.incompressible :=
  fun i t => (mobius_boundary_fundamentalGroup twistPresentation i t).1

theorem twistExternal_index_two (t : Torus) :
    (FundamentalGroup.map (twistExternal.{u}.boundaryMap 0) t).range.index = 2 :=
  (mobius_boundary_fundamentalGroup twistPresentation 0 t).2

theorem mobiusTwistedIBundle_boundary_fundamentalGroup
    (i : Fin mobiusTwistedIBundle.{u}.presentation.externalCount) (t : Torus) :
    Injective (FundamentalGroup.map (mobiusTwistedIBundle.{u}.presentation.external.boundaryMap i)
        t) ∧
      (FundamentalGroup.map
        (mobiusTwistedIBundle.{u}.presentation.external.boundaryMap i) t).range.index = 2 :=
  haveI : Subsingleton (Fin mobiusTwistedIBundle.{u}.presentation.externalCount) :=
    inferInstanceAs (Subsingleton (Fin 1))
  mobius_boundary_fundamentalGroup _ i t


def kleinSqueeze (t : ℝ) : ℝ := t / √(1 + t ^ 2)

def kleinStretch (v : ℝ) : ℝ := v / √(1 - v ^ 2)

private theorem one_add_sq_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

theorem contDiff_kleinSqueeze : ContDiff ℝ ∞ kleinSqueeze :=
  contDiff_id.div ((contDiff_const.add (contDiff_id.pow 2)).sqrt fun t h => by
    simp only [id] at h
    linarith [one_add_sq_pos t]) fun t => (Real.sqrt_pos.mpr (one_add_sq_pos t)).ne'

theorem contDiffAt_kleinStretch {v : ℝ} (hv : v ^ 2 < 1) : ContDiffAt ℝ ∞ kleinStretch v :=
  contDiffAt_id.div ((contDiffAt_const.sub (contDiffAt_id.pow 2)).sqrt (by
    simp only [id]
    linarith)) (Real.sqrt_pos.mpr (by linarith)).ne'

theorem kleinSqueeze_neg (t : ℝ) : kleinSqueeze (-t) = -kleinSqueeze t := by
  rw [kleinSqueeze, kleinSqueeze, neg_sq, neg_div]

theorem sq_kleinSqueeze (t : ℝ) : kleinSqueeze t ^ 2 = t ^ 2 / (1 + t ^ 2) := by
  rw [kleinSqueeze, div_pow, Real.sq_sqrt (one_add_sq_pos t).le]

theorem sq_kleinSqueeze_lt (t : ℝ) : kleinSqueeze t ^ 2 < 1 := by
  rw [sq_kleinSqueeze, div_lt_one (one_add_sq_pos t)]
  linarith

theorem kleinStretch_kleinSqueeze (t : ℝ) : kleinStretch (kleinSqueeze t) = t := by
  have h1 : 1 - kleinSqueeze t ^ 2 = (1 + t ^ 2)⁻¹ := by
    rw [sq_kleinSqueeze]
    field_simp [(one_add_sq_pos t).ne']
    ring
  have hs := Real.sqrt_pos.mpr (one_add_sq_pos t)
  rw [kleinStretch, h1, Real.sqrt_inv, div_inv_eq_mul, kleinSqueeze, div_mul_cancel₀ _ hs.ne']

theorem kleinSqueeze_kleinStretch {v : ℝ} (hv : v ^ 2 < 1) : kleinSqueeze (kleinStretch v) = v := by
  have hpos : 0 < 1 - v ^ 2 := by linarith
  have h1 : 1 + kleinStretch v ^ 2 = (1 - v ^ 2)⁻¹ := by
    rw [kleinStretch, div_pow, Real.sq_sqrt hpos.le]
    field_simp [hpos.ne']
    ring
  have hs := Real.sqrt_pos.mpr hpos
  rw [kleinSqueeze, h1, Real.sqrt_inv, div_inv_eq_mul, kleinStretch, div_mul_cancel₀ _ hs.ne']

theorem kleinSqueeze_injective : Injective kleinSqueeze := fun t t' h => by
  rw [← kleinStretch_kleinSqueeze t, h, kleinStretch_kleinSqueeze]


theorem contMDiff_kleinPoint_comp {f0 f1 f2 : E3 → ℝ} (h0 : ContDiff ℝ ∞ f0)
    (h1 : ContDiff ℝ ∞ f1) (h2 : ContDiff ℝ ∞ f2) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x => kleinPoint (f0 x) (f1 x) (f2 x)) := by
  have hw : ContDiff ℝ ∞ (fun x : E3 => kleinWidth (f1 x)) := contDiff_kleinWidth.comp h1
  have hh : ContDiff ℝ ∞ (fun x : E3 => kleinHeight (f1 x) (f2 x)) :=
    Real.contDiff_arsinh.comp (h2.mul hw)
  have harg : ContDiff ℝ ∞ (fun x : E3 => kleinArg (f1 x) (f2 x)) :=
    (Complex.ofRealCLM.contDiff.comp (hh.div_const 2)).add
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul h1)).mul contDiff_const)
  have hph : ContDiff ℝ ∞ (fun x : E3 => kleinPhase (f0 x)) :=
    Complex.contDiff_exp.comp
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul h0)).mul contDiff_const)
  have hp : ContDiff ℝ ∞ (fun x : E3 => kleinPair (f0 x) (f1 x) (f2 x)) :=
    (hph.mul ((Complex.contDiff_sinh.restrict_scalars ℝ).comp harg)).prodMk
      (hph.mul ((Complex.contDiff_cosh.restrict_scalars ℝ).comp harg))
  have hv : ContDiff ℝ ∞ (fun x : E3 => kleinVector (f0 x) (f1 x) (f2 x)) :=
    lensPair.symm.contDiff.comp hp
  have hn : ContDiff ℝ ∞ (fun x : E3 => ‖kleinVector (f0 x) (f1 x) (f2 x)‖⁻¹) :=
    (hv.norm ℝ fun x => kleinVector_ne_zero _ _ _).inv
      fun x => norm_ne_zero_iff.mpr (kleinVector_ne_zero _ _ _)
  exact (hn.smul hv).contMDiff.codRestrict_sphere fun x => kleinVector_normalize_mem _ _ _

def kleinOpen (x : E3) : mobiusLens.{u}.Carrier := kleinLens (x 0) (x 1) (kleinSqueeze (x 2))

def squeezePoint (x : E3) : E3 := !₂[x 0, x 1, kleinSqueeze (x 2)]

theorem squeezePoint_coords (x : E3) : squeezePoint x 0 = x 0 ∧ squeezePoint x 1 = x 1 ∧
    squeezePoint x 2 = kleinSqueeze (x 2) := by
  simp [squeezePoint]

theorem kleinOpen_eq (x : E3) : kleinOpen.{u} x = kleinLensMap (squeezePoint x) := rfl

theorem squeezePoint_mem (x : E3) : squeezePoint x 2 ^ 2 ≤ 1 := by
  rw [(squeezePoint_coords x).2.2]
  exact (sq_kleinSqueeze_lt _).le

theorem kleinSqueeze_units_mul (ε : ℤˣ) (t : ℝ) :
    kleinSqueeze (((ε : ℤ) : ℝ) * t) = ((ε : ℤ) : ℝ) * kleinSqueeze t := by
  rcases Int.units_eq_one_or ε with h | h <;> simp [h, kleinSqueeze_neg]

theorem squeezePoint_smul (γ : KleinBottleGroup) (x : E3) :
    squeezePoint (γ • x) = γ • squeezePoint x := by
  obtain ⟨h0, h1, h2⟩ := KleinBottleGroup.smul_coords γ x
  obtain ⟨g0, g1, g2⟩ := KleinBottleGroup.smul_coords γ (squeezePoint x)
  obtain ⟨s0, s1, s2⟩ := squeezePoint_coords x
  obtain ⟨t0, t1, t2⟩ := squeezePoint_coords (γ • x)
  refine euclidean3_ext' ?_ ?_ ?_
  · rw [t0, g0, h0, s0]
  · rw [t1, g1, h1, s1]
  · rw [t2, g2, h2, s2, kleinSqueeze_units_mul]

theorem squeezePoint_injective : Injective squeezePoint := fun x y h => by
  obtain ⟨s0, s1, s2⟩ := squeezePoint_coords x
  obtain ⟨t0, t1, t2⟩ := squeezePoint_coords y
  refine euclidean3_ext' ?_ ?_ ?_
  · rw [← s0, ← t0, h]
  · rw [← s1, ← t1, h]
  · exact kleinSqueeze_injective (by rw [← s2, ← t2, h])

theorem kleinOpen_smul (γ : KleinBottleGroup) (x : E3) : kleinOpen.{u} (γ • x) = kleinOpen x := by
  rw [kleinOpen_eq, kleinOpen_eq, squeezePoint_smul, kleinLensMap_smul (squeezePoint_mem x)]

theorem kleinOpen_eq_iff {x y : E3} :
    kleinOpen.{u} x = kleinOpen y ↔ ∃ γ : KleinBottleGroup, γ • y = x := by
  rw [kleinOpen_eq, kleinOpen_eq, kleinLensMap_eq_iff (squeezePoint_mem x) (squeezePoint_mem y)]
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨γ, squeezePoint_injective (by rw [squeezePoint_smul, hγ])⟩
  · rintro ⟨γ, rfl⟩
    exact ⟨γ, (squeezePoint_smul γ y).symm⟩

theorem contMDiff_kleinOpen : ContMDiff (𝓡 3) (𝓡 3) ∞ kleinOpen.{u} :=
  contMDiff_lensUp.comp (mobiusLensGroup.projection_isLocalDiffeomorph.contMDiff.comp
    (contMDiff_kleinPoint_comp (contDiff_coord 0) (contDiff_coord 1)
      (contDiff_kleinSqueeze.comp (contDiff_coord 2))))

theorem mobiusBundleFunction_kleinOpen (x : E3) : mobiusBundleFunction (kleinOpen.{u} x) < 0 := by
  have h := (bundleQuartic_kleinPoint_nonpos_iff (x 0) (x 1) (kleinSqueeze (x 2))).mpr
    (sq_kleinSqueeze_lt _).le
  have h' := (bundleQuartic_kleinPoint_eq_zero_iff (x 0) (x 1) (kleinSqueeze (x 2))).not.mpr
    (sq_kleinSqueeze_lt _).ne
  exact lt_of_le_of_ne h h'

theorem exists_kleinOpen_eq (y : mobiusLens.{u}.Carrier) (hy : mobiusBundleFunction y < 0) :
    ∃ x : E3, kleinOpen x = y := by
  obtain ⟨x, hx, hxy⟩ := exists_kleinLens_eq y hy.le
  have hlt : x 2 ^ 2 < 1 := by
    refine lt_of_le_of_ne hx fun h => hy.ne ?_
    rw [← hxy]
    exact (bundleQuartic_kleinPoint_eq_zero_iff _ _ _).mpr h
  refine ⟨!₂[x 0, x 1, kleinStretch (x 2)], ?_⟩
  have e : kleinOpen.{u} !₂[x 0, x 1, kleinStretch (x 2)] =
      kleinLens (x 0) (x 1) (kleinSqueeze (kleinStretch (x 2))) := rfl
  rw [e, kleinSqueeze_kleinStretch hlt]
  exact hxy


theorem contDiffAt_modelFibrePoint {p : ℂ × ℂ} (hab : p.1 ^ 2 - p.2 ^ 2 ≠ 0) :
    ContDiffAt ℝ ∞ modelFibrePoint p := by
  have he : modelFibrePoint = (fun q : ℂ × ℂ => q.1 ^ 2 - q.2 ^ 2) *
      (fun q : ℂ × ℂ => ((‖q.1 ^ 2 - q.2 ^ 2‖ : ℝ) : ℂ))⁻¹ :=
    funext fun q => div_eq_mul_inv _ _
  rw [he]
  have hm : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => q.1 ^ 2 - q.2 ^ 2) p :=
    (contDiffAt_fst.pow 2).sub (contDiffAt_snd.pow 2)
  have hnorm : ContDiffAt ℝ ∞ (norm : ℂ → ℝ) (p.1 ^ 2 - p.2 ^ 2) := contDiffAt_norm ℝ hab
  have hn' : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => ‖q.1 ^ 2 - q.2 ^ 2‖) p := hnorm.comp p hm
  have hn : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => ((‖q.1 ^ 2 - q.2 ^ 2‖ : ℝ) : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p hn'
  exact hm.mul (hn.inv (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hab)))

theorem contDiffAt_modelAnnulusPoint {p : ℂ × ℂ} (h : p.1 - p.2 ≠ 0) :
    ContDiffAt ℝ ∞ modelAnnulusPoint p := by
  have he : modelAnnulusPoint = (fun q : ℂ × ℂ => -(q.1 + q.2)) *
      (fun q : ℂ × ℂ => q.1 - q.2)⁻¹ :=
    funext fun q => div_eq_mul_inv _ _
  rw [he]
  exact (contDiffAt_fst.add contDiffAt_snd).neg.mul ((contDiffAt_fst.sub contDiffAt_snd).inv h)

theorem kleinPhase_sq_eq_circle (a : ℝ) :
    kleinPhase a ^ 2 = ((1 : ℝ) : ℂ) * (Circle.exp (2 * Real.pi * a) : ℂ) := by
  rw [kleinPhase_sq, Circle.coe_exp, Complex.ofReal_one, one_mul]

theorem exp_two_mul_kleinArg_eq (b v : ℝ) :
    Complex.exp (2 * kleinArg b v) =
      ((Real.exp (kleinHeight b v) : ℝ) : ℂ) * (Circle.exp (2 * Real.pi * b) : ℂ) := by
  rw [two_mul_kleinArg, Complex.exp_add, Complex.ofReal_exp, Circle.coe_exp]

theorem modelFibrePoint_kleinPoint (a b v : ℝ) :
    modelFibrePoint (lensPair (kleinPoint a b v : E4)) = -kleinPhase a ^ 2 :=
  congrArg Prod.fst (modelPoint_kleinPoint a b v)

theorem modelAnnulusPoint_kleinPoint (a b v : ℝ) :
    modelAnnulusPoint (lensPair (kleinPoint a b v : E4)) = Complex.exp (2 * kleinArg b v) :=
  congrArg Prod.snd (modelPoint_kleinPoint a b v)

theorem kleinPoint_sq_sub_ne_zero {a b v : ℝ} (hv : v ^ 2 ≤ 1) :
    (lensPair (kleinPoint a b v : E4)).1 ^ 2 - (lensPair (kleinPoint a b v : E4)).2 ^ 2 ≠ 0 :=
  sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero _)
    ((bundleQuartic_kleinPoint_nonpos_iff a b v).mpr hv)

def kleinChartAt (x₀ : E3) (p : ℂ × ℂ) : E3 :=
  !₂[liftAngle (x₀ 0) (-modelFibrePoint p), liftAngle (x₀ 1) (modelAnnulusPoint p),
    kleinStretch (Real.sinh (Real.log ‖modelAnnulusPoint p‖) /
      kleinWidth (liftAngle (x₀ 1) (modelAnnulusPoint p)))]

theorem kleinChartAt_kleinPoint (x₀ : E3) {a b v : ℝ} (ha : |2 * Real.pi * (a - x₀ 0)| < Real.pi)
    (hb : |2 * Real.pi * (b - x₀ 1)| < Real.pi) :
    kleinChartAt x₀ (lensPair (kleinPoint a b v : E4)) = !₂[a, b, kleinStretch v] := by
  have hA : liftAngle (x₀ 0) (-modelFibrePoint (lensPair (kleinPoint a b v : E4))) = a := by
    rw [modelFibrePoint_kleinPoint, neg_neg, kleinPhase_sq_eq_circle]
    exact liftAngle_eq one_pos ha
  have hB : liftAngle (x₀ 1) (modelAnnulusPoint (lensPair (kleinPoint a b v : E4))) = b := by
    rw [modelAnnulusPoint_kleinPoint, exp_two_mul_kleinArg_eq]
    exact liftAngle_eq (Real.exp_pos _) hb
  have hN : ‖modelAnnulusPoint (lensPair (kleinPoint a b v : E4))‖ =
      Real.exp (kleinHeight b v) := by
    rw [modelAnnulusPoint_kleinPoint, Complex.norm_exp, two_mul_kleinArg]
    simp
  rw [kleinChartAt, hA, hB, hN, Real.log_exp, sinh_kleinHeight,
    mul_div_cancel_right₀ _ (kleinWidth_pos b).ne']


theorem kleinInner_kleinPoint (x₀ : E3) {a b v : ℝ} (hb : |2 * Real.pi * (b - x₀ 1)| < Real.pi) :
    Real.sinh (Real.log ‖modelAnnulusPoint (lensPair (kleinPoint a b v : E4))‖) /
      kleinWidth (liftAngle (x₀ 1) (modelAnnulusPoint (lensPair (kleinPoint a b v : E4)))) = v := by
  have hB : liftAngle (x₀ 1) (modelAnnulusPoint (lensPair (kleinPoint a b v : E4))) = b := by
    rw [modelAnnulusPoint_kleinPoint, exp_two_mul_kleinArg_eq]
    exact liftAngle_eq (Real.exp_pos _) hb
  have hN : ‖modelAnnulusPoint (lensPair (kleinPoint a b v : E4))‖ =
      Real.exp (kleinHeight b v) := by
    rw [modelAnnulusPoint_kleinPoint, Complex.norm_exp, two_mul_kleinArg]
    simp
  rw [hB, hN, Real.log_exp, sinh_kleinHeight, mul_div_cancel_right₀ _ (kleinWidth_pos b).ne']

theorem contDiffAt_kleinChartAt (x₀ : E3) {v : ℝ} (hv : v ^ 2 < 1) :
    ContDiffAt ℝ ∞ (kleinChartAt x₀) (lensPair (kleinPoint (x₀ 0) (x₀ 1) v : E4)) := by
  have hab := kleinPoint_sq_sub_ne_zero (a := x₀ 0) (b := x₀ 1) hv.le
  obtain ⟨h1, h2⟩ := sub_ne_zero_of_sq_sub_sq_ne_zero hab
  have hF := contDiffAt_modelFibrePoint hab
  have hU := contDiffAt_modelAnnulusPoint h1
  have h0 : |2 * Real.pi * (x₀ 0 - x₀ 0)| < Real.pi := by simp [Real.pi_pos]
  have h1' : |2 * Real.pi * (x₀ 1 - x₀ 1)| < Real.pi := by simp [Real.pi_pos]
  have hslitA : (Circle.exp (-(2 * Real.pi * x₀ 0)) : ℂ) *
      (-modelFibrePoint (lensPair (kleinPoint (x₀ 0) (x₀ 1) v : E4))) ∈ Complex.slitPlane := by
    rw [modelFibrePoint_kleinPoint, neg_neg, kleinPhase_sq_eq_circle]
    exact mem_slitPlane_circleExp_neg_mul one_pos h0
  have hslitB : (Circle.exp (-(2 * Real.pi * x₀ 1)) : ℂ) *
      modelAnnulusPoint (lensPair (kleinPoint (x₀ 0) (x₀ 1) v : E4)) ∈ Complex.slitPlane := by
    rw [modelAnnulusPoint_kleinPoint, exp_two_mul_kleinArg_eq]
    exact mem_slitPlane_circleExp_neg_mul (Real.exp_pos _) h1'
  have hUne := modelAnnulusPoint_ne_zero hab
  have hLA := (contDiffAt_liftAngle hslitA).comp (f := fun q => -modelFibrePoint q) _ hF.neg
  have hLB := (contDiffAt_liftAngle hslitB).comp _ hU
  have hnorm : ContDiffAt ℝ ∞ (norm : ℂ → ℝ)
      (modelAnnulusPoint (lensPair (kleinPoint (x₀ 0) (x₀ 1) v : E4))) := contDiffAt_norm ℝ hUne
  have hN := hnorm.comp (lensPair (kleinPoint (x₀ 0) (x₀ 1) v : E4)) hU
  have hlog := (Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr hUne)).comp
    (lensPair (kleinPoint (x₀ 0) (x₀ 1) v : E4)) hN
  have hV := (Real.contDiff_sinh.contDiffAt.comp (lensPair (kleinPoint (x₀ 0) (x₀ 1) v : E4))
    hlog).div (contDiff_kleinWidth.contDiffAt.comp (lensPair (kleinPoint (x₀ 0) (x₀ 1) v : E4))
      hLB) (kleinWidth_pos _).ne'
  have hval := kleinInner_kleinPoint x₀ (a := x₀ 0) (v := v) h1'
  refine contDiffAt_euclidean.2 fun i => ?_
  fin_cases i
  · exact hLA
  · exact hLB
  · have hv' : (Real.sinh (Real.log
        ‖modelAnnulusPoint (lensPair (kleinPoint (x₀ 0) (x₀ 1) v : E4))‖) / kleinWidth
        (liftAngle (x₀ 1) (modelAnnulusPoint (lensPair (kleinPoint (x₀ 0) (x₀ 1) v : E4))))) ^ 2 <
          1 := by
      rw [hval]
      exact hv
    exact (contDiffAt_kleinStretch hv').comp (lensPair (kleinPoint (x₀ 0) (x₀ 1) v : E4)) hV


def kleinSpherePoint (x : E3) : Metric.sphere (0 : E4) 1 :=
  kleinPoint (x 0) (x 1) (kleinSqueeze (x 2))

theorem contMDiff_kleinSpherePoint : ContMDiff (𝓡 3) (𝓡 3) ∞ kleinSpherePoint :=
  contMDiff_kleinPoint_comp (contDiff_coord 0) (contDiff_coord 1)
    (contDiff_kleinSqueeze.comp (contDiff_coord 2))

private theorem isInvertible_of_bijective_E3 {f : E3 →L[ℝ] E3} (hf : Bijective f) :
    f.IsInvertible :=
  ⟨(LinearEquiv.ofBijective (f : E3 →ₗ[ℝ] E3) hf).toContinuousLinearEquiv,
    by ext; rfl⟩

private theorem eventually_abs_lt (x₀ : E3) (j : Fin 3) :
    ∀ᶠ x in 𝓝 x₀, |2 * Real.pi * (x j - x₀ j)| < Real.pi :=
  ((continuous_const.mul ((contDiff_coord j).continuous.sub continuous_const)).abs.continuousAt
    ).eventually_lt continuousAt_const (by simp [Real.pi_pos])

theorem mfderiv_kleinSpherePoint_bijective (x₀ : E3) :
    Bijective (mfderiv (𝓡 3) (𝓡 3) kleinSpherePoint x₀) := by
  have hv : kleinSqueeze (x₀ 2) ^ 2 < 1 := sq_kleinSqueeze_lt _
  have hg : MDifferentiableAt (𝓡 3) (𝓡 3)
      (fun w : Metric.sphere (0 : E4) 1 => kleinChartAt x₀ (lensPair (w : E4)))
      (kleinSpherePoint x₀) := by
    have hc : ContDiffAt ℝ ∞ (fun w : E4 => kleinChartAt x₀ (lensPair w))
        (kleinSpherePoint x₀ : E4) :=
      (contDiffAt_kleinChartAt x₀ hv).comp (kleinSpherePoint x₀ : E4)
        lensPair.contDiff.contDiffAt
    exact (hc.contMDiffAt.comp (kleinSpherePoint x₀)
      contMDiff_coe_sphere.contMDiffAt).mdifferentiableAt (by simp)
  have hgf : (fun w : Metric.sphere (0 : E4) 1 => kleinChartAt x₀ (lensPair (w : E4))) ∘
      kleinSpherePoint =ᶠ[𝓝 x₀] id := by
    filter_upwards [eventually_abs_lt x₀ 0, eventually_abs_lt x₀ 1] with x hx0 hx1
    change kleinChartAt x₀ (lensPair (kleinPoint (x 0) (x 1) (kleinSqueeze (x 2)) : E4)) = x
    rw [kleinChartAt_kleinPoint x₀ hx0 hx1, kleinStretch_kleinSqueeze]
    exact euclidean3_ext' (by simp) (by simp) (by simp)
  exact bijective_mfderiv_of_leftInverse
    ((contMDiff_kleinSpherePoint x₀).mdifferentiableAt (by simp)) hg hgf rfl

theorem isLocalDiffeomorph_kleinSpherePoint :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ kleinSpherePoint := by
  have h := contMDiff_kleinSpherePoint.contMDiffOn.isLocalDiffeomorphOn_of_isInvertible_mfderiv
    isOpen_univ (by simp) fun x hx =>
      isInvertible_of_bijective_E3 (mfderiv_kleinSpherePoint_bijective x)
  exact isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ.mpr h

def lensUpDiffeo : mobiusLensGroup.Orbit ≃ₘ⟮𝓡 3, 𝓡 3⟯ mobiusLens.{u}.Carrier where
  toFun := lensUp
  invFun := lensDown
  left_inv := lensDown_lensUp
  right_inv := lensUp_lensDown
  contMDiff_toFun := contMDiff_lensUp
  contMDiff_invFun := contMDiff_lensDown

theorem isLocalDiffeomorph_kleinOpen : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ kleinOpen.{u} :=
  fun x => IsLocalDiffeomorphAt.comp (hf := IsLocalDiffeomorphAt.comp
    (hf := isLocalDiffeomorph_kleinSpherePoint x)
    (hg := mobiusLensGroup.projection_isLocalDiffeomorph _))
    (hg := lensUpDiffeo.isLocalDiffeomorph _)


def kleinQuotient : TwistedKleinBundle → mobiusLens.{u}.Carrier :=
  Quotient.lift kleinOpen fun a b h => by
    obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact kleinOpen_smul γ b

theorem kleinQuotient_mk (x : E3) : kleinQuotient.{u} (Quotient.mk'' x) = kleinOpen x := rfl

theorem isLocalDiffeomorph_kleinQuotient :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ kleinQuotient.{u} := by
  intro q
  obtain ⟨x, rfl⟩ := Quotient.mk''_surjective q
  obtain ⟨Ψ, hx, heq⟩ := isLocalDiffeomorph_orbitMk (𝓡 3) KleinBottleGroup E3 x
  obtain ⟨Φ, hxΦ, hΦ⟩ := isLocalDiffeomorph_kleinOpen.{u} x
  have hΨx : Ψ x = Quotient.mk'' x := (heq hx).symm
  refine ⟨Ψ.symm.trans Φ, ⟨?_, ?_⟩, fun y hy => ?_⟩
  · rw [← hΨx]
    exact Ψ.toPartialEquiv.map_source hx
  · change Ψ.toPartialEquiv.symm (Quotient.mk'' x) ∈ Φ.source
    rw [← hΨx, Ψ.toPartialEquiv.left_inv hx]
    exact hxΦ
  · have hy1 : y ∈ Ψ.toPartialEquiv.target := hy.1
    have hy2 : Ψ.toPartialEquiv.symm y ∈ Φ.source := hy.2
    have hy' : y = Quotient.mk'' (Ψ.toPartialEquiv.symm y) := by
      rw [heq (Ψ.toPartialEquiv.map_target hy1), Ψ.toPartialEquiv.right_inv hy1]
    change kleinQuotient y = Φ (Ψ.toPartialEquiv.symm y)
    rw [← hΦ hy2]
    conv_lhs => rw [hy']
    rfl

theorem injective_kleinQuotient : Injective kleinQuotient.{u} := by
  rintro ⟨x⟩ ⟨y⟩ h
  obtain ⟨γ, hγ⟩ := kleinOpen_eq_iff.mp (h : kleinOpen.{u} x = kleinOpen y)
  exact Quot.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨γ, hγ⟩))

theorem range_kleinQuotient :
    range kleinQuotient.{u} = {y | mobiusBundleFunction y < 0} := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := Quotient.mk''_surjective q
    exact mobiusBundleFunction_kleinOpen x
  · intro hy
    obtain ⟨x, hx⟩ := exists_kleinOpen_eq y hy
    exact ⟨Quotient.mk'' x, hx⟩

def kleinImage : TopologicalSpace.Opens mobiusLens.{u}.Carrier :=
  isLocalDiffeomorph_kleinQuotient.image

theorem mem_kleinImage {y : mobiusLens.{u}.Carrier} :
    y ∈ kleinImage ↔ mobiusBundleFunction y < 0 := by
  change y ∈ isLocalDiffeomorph_kleinQuotient.image.1 ↔ _
  rw [IsLocalDiffeomorph.image_coe, range_kleinQuotient]
  rfl

def kleinDiffeo : TwistedKleinBundle ≃ₘ⟮𝓡 3, 𝓡 3⟯ kleinImage.{u} :=
  DifferentialGeometry.Topology.Manifold.diffeomorphOntoImage kleinQuotient
    isLocalDiffeomorph_kleinQuotient injective_kleinQuotient

theorem isInteriorPoint_mobiusBundleSet_iff (x : mobiusBundleSet.{u}) :
    (𝓡∂ 3).IsInteriorPoint x ↔ mobiusBundleFunction x.val < 0 := by
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint, mobiusBundleSet_isBoundaryPoint_iff]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

def kleinInteriorEquiv :
    kleinImage.{u} ≃ₘ⟮𝓡 3, mobiusBundleCarrier.{u}.model⟯
      mobiusBundleCarrier.{u}.pieceInterior ⊤ where
  toFun y := ⟨⟨y.1, (mem_kleinImage.1 y.2).le⟩,
    ⟨trivial, (isInteriorPoint_mobiusBundleSet_iff ⟨y.1, (mem_kleinImage.1 y.2).le⟩).2
      (mem_kleinImage.1 y.2)⟩⟩
  invFun x := ⟨x.1.1, mem_kleinImage.2 ((isInteriorPoint_mobiusBundleSet_iff x.1).1 x.2.2)⟩
  left_inv y := rfl
  right_inv x := rfl
  contMDiff_toFun := by
    refine (ContMDiff.subtypeVal_comp_iff (mobiusBundleCarrier.{u}.pieceInterior ⊤) _).1 ?_
    refine (mobiusBundleAtlas.{u}.contMDiff_iff_subtype_val _).2 ?_
    exact contMDiff_subtype_val
  contMDiff_invFun := by
    refine (ContMDiff.subtypeVal_comp_iff kleinImage.{u} _).1 ?_
    have hval : ContMDiff mobiusBundleCarrier.{u}.model (𝓡 3) ∞
        (fun x : mobiusBundleCarrier.{u}.Carrier =>
          @Subtype.val mobiusLens.{u}.Carrier (· ∈ mobiusBundleSet.{u}) x) :=
      mobiusBundleAtlas.{u}.contMDiff_subtype_val
    exact hval.comp (contMDiff_subtype_val (U := mobiusBundleCarrier.{u}.pieceInterior ⊤))

def mobiusKleinInteriorDiffeo :
    mobiusBundleCarrier.{u}.pieceInterior ⊤ ≃ₘ⟮mobiusBundleCarrier.{u}.model, 𝓡 3⟯
      TwistedKleinBundle :=
  kleinInteriorEquiv.symm.trans kleinDiffeo.symm

def mobiusBundle_interiorGeometry : mobiusBundleCarrier.{u}.InteriorGeometry ⊤ :=
  interiorGeometryOfDiffeomorph twistedKleinBundleGeometry mobiusBundleCarrier.{u} ⊤
    mobiusKleinInteriorDiffeo

theorem mobiusBundle_interiorGeometry_model :
    letI := DifferentialGeometry.Manifold.interiorChartedSpace mobiusBundleCarrier.{u}.model ∞
      (M := mobiusBundleCarrier.{u}.pieceInterior ⊤)
    letI := DifferentialGeometry.Manifold.interiorIsManifold mobiusBundleCarrier.{u}.model ∞
      (M := mobiusBundleCarrier.{u}.pieceInterior ⊤)
    mobiusBundle_interiorGeometry.{u}.model = ThurstonModel.euclidean :=
  rfl

end GC.Geometry

import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1ModelRadial
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SolidTorus
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Chapter-14 assembly, item L1, group G3a: the model space of the solid torus in `S³`

The map `modelSphere len : ℝ² × ℝ → S³`, `(w, v) ↦ (w / √2, √(1 - ‖w‖² / 2) e^{2π i v / (4 len)})`
(Clifford coordinates) is periodic of period `4 len` in `v`, has Clifford height `‖w‖² - 1`, so
it carries `{‖w‖ ≤ 1}` onto the standard solid torus (`modelSphere_mem_solidTorusSet_iff`), and on
every slab `{‖w‖ < 13/10, a < v < a + 4 len}` it is a partial diffeomorphism onto an open set of
`S³` (`modelSphereChart`, explicit inverse through the argument of the second coordinate).
-/

set_option autoImplicit false

noncomputable section

open Set Function Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped ContDiff Topology Manifold Real

universe u

namespace GC.GraphManifold.Assembly

attribute [local instance] fact_finrank_euclideanSpace_four finrank_real_complex_fact'

/-- The plane of the model as the complex line. -/
def modelPlaneComplex : ModelPlane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm

/-- The angular scale of the model of combinatorial length `len`. -/
def modelAngleScale (len : ℕ) : ℝ := 2 * π / (4 * len)

theorem modelAngleScale_pos {len : ℕ} (hlen : 0 < len) : 0 < modelAngleScale len := by
  unfold modelAngleScale
  have : (0 : ℝ) < len := Nat.cast_pos.mpr hlen
  positivity

theorem modelAngleScale_mul {len : ℕ} (hlen : 0 < len) :
    modelAngleScale len * (4 * len) = 2 * π := by
  unfold modelAngleScale
  have : (len : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hlen.ne'
  field_simp

/-- The first Clifford coordinate of the model point. -/
def modelFirst (w : ModelPlane) : ℂ := (Real.sqrt 2)⁻¹ • modelPlaneComplex w

/-- The second Clifford coordinate of the model point. -/
def modelSecond (len : ℕ) (p : ModelSpace) : ℂ :=
  (Real.sqrt (1 - ‖p.1‖ ^ 2 / 2) : ℂ) * (Circle.exp (modelAngleScale len * p.2) : ℂ)

theorem norm_modelFirst_sq (w : ModelPlane) : ‖modelFirst w‖ ^ 2 = ‖w‖ ^ 2 / 2 := by
  rw [modelFirst, norm_smul, LinearIsometryEquiv.norm_map, mul_pow, norm_inv,
    Real.norm_of_nonneg (Real.sqrt_nonneg 2), inv_pow, Real.sq_sqrt (by norm_num)]
  ring

theorem norm_modelSecond_sq (len : ℕ) {p : ModelSpace} (hp : ‖p.1‖ ^ 2 ≤ 2) :
    ‖modelSecond len p‖ ^ 2 = 1 - ‖p.1‖ ^ 2 / 2 := by
  rw [modelSecond, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by linarith)]

theorem modelSphere_norm (len : ℕ) {p : ModelSpace} (hp : ‖p.1‖ ^ 2 ≤ 2) :
    ‖modelFirst p.1‖ ^ 2 + ‖modelSecond len p‖ ^ 2 = 1 := by
  rw [norm_modelFirst_sq, norm_modelSecond_sq len hp]
  ring

/-- **The model map into `S³`.** -/
def modelSphere (len : ℕ) (p : ModelSpace) : SphereCarrier.{u} :=
  if hp : ‖p.1‖ ^ 2 ≤ 2 then sphereOfPair (modelFirst p.1) (modelSecond len p) (modelSphere_norm len hp)
  else sphereOfPair 1 0 (by simp)

theorem modelSphere_of_le (len : ℕ) {p : ModelSpace} (hp : ‖p.1‖ ^ 2 ≤ 2) :
    modelSphere.{u} len p = sphereOfPair (modelFirst p.1) (modelSecond len p)
      (modelSphere_norm len hp) := by
  rw [modelSphere, dite_eq_left hp]

theorem sphereFirst_modelSphere (len : ℕ) {p : ModelSpace} (hp : ‖p.1‖ ^ 2 ≤ 2) :
    sphereFirst (modelSphere.{u} len p) = modelFirst p.1 := by
  rw [modelSphere_of_le len hp, sphereFirst_sphereOfPair]

theorem sphereSecond_modelSphere (len : ℕ) {p : ModelSpace} (hp : ‖p.1‖ ^ 2 ≤ 2) :
    sphereSecond (modelSphere.{u} len p) = modelSecond len p := by
  rw [modelSphere_of_le len hp, sphereSecond_sphereOfPair]

theorem cliffordHeight_modelSphere (len : ℕ) {p : ModelSpace} (hp : ‖p.1‖ ^ 2 ≤ 2) :
    cliffordHeight (modelSphere.{u} len p) = ‖p.1‖ ^ 2 - 1 := by
  rw [cliffordHeight, sphereFirst_modelSphere len hp, sphereSecond_modelSphere len hp,
    norm_modelFirst_sq, norm_modelSecond_sq len hp]
  ring

/-- The model map carries `{‖w‖ ≤ 1}` onto the standard solid torus. -/
theorem modelSphere_mem_solidTorusSet_iff (len : ℕ) {p : ModelSpace} (hp : ‖p.1‖ ^ 2 ≤ 2) :
    modelSphere.{u} len p ∈ solidTorusSet.{u} ↔ ‖p.1‖ ≤ 1 := by
  change cliffordHeight (modelSphere.{u} len p) ≤ 0 ↔ _
  rw [cliffordHeight_modelSphere len hp, sub_nonpos, sq_le_one_iff₀ (norm_nonneg _)]

/-- The model map has period `4 len` in the height. -/
theorem modelSphere_add_period {len : ℕ} (hlen : 0 < len) (p : ModelSpace) (m : ℤ) :
    modelSphere.{u} len (p.1, p.2 + 4 * len * m) = modelSphere.{u} len p := by
  by_cases hp : ‖p.1‖ ^ 2 ≤ 2
  · have he : Circle.exp (modelAngleScale len * (p.2 + 4 * len * m)) =
        Circle.exp (modelAngleScale len * p.2) := by
      rw [Circle.exp_eq_exp]
      refine ⟨m, ?_⟩
      rw [mul_add, show modelAngleScale len * (4 * len * m) = m * (modelAngleScale len * (4 * len))
        by ring, modelAngleScale_mul hlen]
    apply sphere_ext
    · rw [sphereFirst_modelSphere len (p := (p.1, p.2 + 4 * len * m)) hp,
        sphereFirst_modelSphere len hp]
    · rw [sphereSecond_modelSphere len (p := (p.1, p.2 + 4 * len * m)) hp,
        sphereSecond_modelSphere len hp]
      simp only [modelSecond, he]
  · rw [modelSphere, dite_eq_right hp, modelSphere, dite_eq_right hp]

/-- Two model points with the same image differ by a multiple of the period. -/
theorem modelSphere_eq_iff {len : ℕ} (hlen : 0 < len) {p p' : ModelSpace} (hp : ‖p.1‖ ^ 2 < 2)
    (hp' : ‖p'.1‖ ^ 2 < 2) :
    modelSphere.{u} len p = modelSphere.{u} len p' ↔
      p.1 = p'.1 ∧ ∃ m : ℤ, p'.2 = p.2 + 4 * len * m := by
  constructor
  · intro h
    have h1 := congrArg sphereFirst h
    have h2 := congrArg sphereSecond h
    rw [sphereFirst_modelSphere len hp.le, sphereFirst_modelSphere len hp'.le] at h1
    rw [sphereSecond_modelSphere len hp.le, sphereSecond_modelSphere len hp'.le] at h2
    have hw : p.1 = p'.1 := by
      have := (smul_right_injective ℂ (inv_ne_zero (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne')
        |>.comp modelPlaneComplex.injective) h1
      exact this
    refine ⟨hw, ?_⟩
    simp only [modelSecond, hw] at h2
    have hr : (Real.sqrt (1 - ‖p'.1‖ ^ 2 / 2) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact (Real.sqrt_pos.mpr (by linarith)).ne'
    have he := mul_left_cancel₀ hr h2
    have he' : Circle.exp (modelAngleScale len * p.2) = Circle.exp (modelAngleScale len * p'.2) :=
      Subtype.ext he
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp he'
    refine ⟨-m, ?_⟩
    have hk := modelAngleScale_mul hlen
    have hκ := modelAngleScale_pos hlen
    have : modelAngleScale len * (p'.2 - (p.2 + 4 * len * (-m : ℤ))) = 0 := by
      push_cast
      rw [← hk] at hm
      linear_combination (-1 : ℝ) * hm
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hκ.ne'
    · linarith
  · rintro ⟨hw, m, hm⟩
    have : p' = (p.1, p.2 + 4 * len * m) := Prod.ext hw.symm hm
    rw [this, modelSphere_add_period hlen]

/-! ## The slab charts -/

/-- The slab of height `4 len` above `a`. -/
def modelSlab (len : ℕ) (a : ℝ) : Set ModelSpace :=
  {p | ‖p.1‖ < 13 / 10 ∧ a < p.2 ∧ p.2 < a + 4 * len}

theorem isOpen_modelSlab (len : ℕ) (a : ℝ) : IsOpen (modelSlab len a) :=
  (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
    ((isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const))

/-- The centre angle of the slab. -/
def modelSlabAngle (len : ℕ) (a : ℝ) : ℝ := modelAngleScale len * (a + 2 * len)

/-- The inverse of the model map on a slab. -/
def modelSlabInv (len : ℕ) (a : ℝ) (q : SphereCarrier.{u}) : ModelSpace :=
  (Real.sqrt 2 • modelPlaneComplex.symm (sphereFirst q),
    a + 2 * len + arg (sphereSecond q * (Circle.exp (-modelSlabAngle len a) : ℂ)) /
      modelAngleScale len)

/-- The image of a slab. -/
def modelSlabTarget (len : ℕ) (a : ℝ) : Set SphereCarrier.{u} :=
  {q | Real.sqrt 2 * ‖sphereFirst q‖ < 13 / 10 ∧
    sphereSecond q * (Circle.exp (-modelSlabAngle len a) : ℂ) ∈ slitPlane}

theorem isOpen_modelSlabTarget (len : ℕ) (a : ℝ) : IsOpen (modelSlabTarget.{u} len a) :=
  (isOpen_lt (continuous_const.mul (continuous_norm.comp contMDiff_sphereFirst.continuous))
    continuous_const).inter
    (isOpen_slitPlane.preimage (contMDiff_sphereSecond.continuous.mul continuous_const))

theorem norm_sq_lt_two_of_mem_modelSlab {len : ℕ} {a : ℝ} {p : ModelSpace}
    (hp : p ∈ modelSlab len a) : ‖p.1‖ ^ 2 < 2 := by
  have h0 := norm_nonneg p.1
  nlinarith [hp.1]

theorem modelSecond_mul_exp (len : ℕ) (a : ℝ) (p : ModelSpace) :
    modelSecond len p * (Circle.exp (-modelSlabAngle len a) : ℂ) =
      (Real.sqrt (1 - ‖p.1‖ ^ 2 / 2) : ℂ) *
        (Circle.exp (modelAngleScale len * p.2 - modelSlabAngle len a) : ℂ) := by
  rw [modelSecond, mul_assoc, ← Circle.coe_mul, ← Circle.exp_add, ← sub_eq_add_neg]

theorem arg_modelSecond_mul_exp {len : ℕ} (hlen : 0 < len) {a : ℝ} {p : ModelSpace}
    (hp : p ∈ modelSlab len a) :
    arg (modelSecond len p * (Circle.exp (-modelSlabAngle len a) : ℂ)) =
      modelAngleScale len * p.2 - modelSlabAngle len a := by
  have hr : 0 < Real.sqrt (1 - ‖p.1‖ ^ 2 / 2) := by
    have := norm_sq_lt_two_of_mem_modelSlab hp
    exact Real.sqrt_pos.mpr (by linarith)
  have hk := modelAngleScale_mul hlen
  have hκ := modelAngleScale_pos hlen
  have hθ : modelAngleScale len * p.2 - modelSlabAngle len a ∈ Ioo (-π) π := by
    rw [modelSlabAngle]
    obtain ⟨-, h1, h2⟩ := hp
    constructor
    · nlinarith
    · nlinarith
  rw [modelSecond_mul_exp, Circle.coe_exp, exp_mul_I]
  exact arg_mul_cos_add_sin_mul_I hr ⟨hθ.1, hθ.2.le⟩

/-- **The slab chart of the model map.** -/
def modelSphereChart {len : ℕ} (hlen : 0 < len) (a : ℝ) :
    PartialDiffeomorph 𝓘(ℝ, ModelSpace) (𝓡 3) ModelSpace SphereCarrier.{u} ∞ where
  toFun := modelSphere.{u} len
  invFun := modelSlabInv.{u} len a
  source := modelSlab len a
  target := modelSlabTarget.{u} len a
  map_source' := by
    intro p hp
    have hp2 := (norm_sq_lt_two_of_mem_modelSlab hp).le
    refine ⟨?_, ?_⟩
    · rw [sphereFirst_modelSphere len hp2, modelFirst, norm_smul, LinearIsometryEquiv.norm_map,
        norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg 2),
        mul_inv_cancel_left₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
      exact hp.1
    · rw [sphereSecond_modelSphere len hp2, mem_slitPlane_iff_arg,
        arg_modelSecond_mul_exp hlen hp]
      have hk := modelAngleScale_mul hlen
      have hκ := modelAngleScale_pos hlen
      refine ⟨?_, ?_⟩
      · rw [modelSlabAngle]
        obtain ⟨-, -, h2⟩ := hp
        nlinarith
      · rw [modelSecond_mul_exp]
        refine mul_ne_zero ?_ (Circle.coe_ne_zero _)
        rw [Complex.ofReal_ne_zero]
        have := norm_sq_lt_two_of_mem_modelSlab hp
        exact (Real.sqrt_pos.mpr (by linarith)).ne'
  map_target' := by
    intro q hq
    have hκ := modelAngleScale_pos hlen
    have hk := modelAngleScale_mul hlen
    obtain ⟨h1, h2⟩ := hq
    have harg := mem_slitPlane_iff_arg.mp h2
    have hlo := neg_pi_lt_arg (sphereSecond q * (Circle.exp (-modelSlabAngle len a) : ℂ))
    have hhi := lt_of_le_of_ne (arg_le_pi (sphereSecond q * (Circle.exp (-modelSlabAngle len a) :
      ℂ))) harg.1
    refine ⟨?_, ?_, ?_⟩
    · change ‖Real.sqrt 2 • modelPlaneComplex.symm (sphereFirst q)‖ < 13 / 10
      rw [norm_smul, LinearIsometryEquiv.norm_map, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
      exact h1
    · change a < a + 2 * len + _ / _
      have : -π / modelAngleScale len < arg (sphereSecond q *
          (Circle.exp (-modelSlabAngle len a) : ℂ)) / modelAngleScale len :=
        div_lt_div_of_pos_right hlo hκ
      have hpi : π / modelAngleScale len = 2 * len := by
        rw [div_eq_iff hκ.ne']
        linarith
      rw [neg_div, hpi] at this
      linarith
    · change a + 2 * len + _ / _ < a + 4 * len
      have : arg (sphereSecond q * (Circle.exp (-modelSlabAngle len a) : ℂ)) / modelAngleScale len <
          π / modelAngleScale len := div_lt_div_of_pos_right hhi hκ
      have hpi : π / modelAngleScale len = 2 * len := by
        rw [div_eq_iff hκ.ne']
        linarith
      rw [hpi] at this
      linarith
  left_inv' := by
    intro p hp
    have hp2 := (norm_sq_lt_two_of_mem_modelSlab hp).le
    have hκ := modelAngleScale_pos hlen
    refine Prod.ext ?_ ?_
    · change Real.sqrt 2 • modelPlaneComplex.symm (sphereFirst (modelSphere.{u} len p)) = p.1
      rw [sphereFirst_modelSphere len hp2, modelFirst, map_smul,
        LinearIsometryEquiv.symm_apply_apply, smul_smul,
        mul_inv_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne', one_smul]
    · change a + 2 * len + arg (sphereSecond (modelSphere.{u} len p) *
        (Circle.exp (-modelSlabAngle len a) : ℂ)) / modelAngleScale len = p.2
      rw [sphereSecond_modelSphere len hp2, arg_modelSecond_mul_exp hlen hp, modelSlabAngle]
      field_simp
      ring
  right_inv' := by
    intro q hq
    have hκ := modelAngleScale_pos hlen
    have hw : ‖(modelSlabInv.{u} len a q).1‖ ^ 2 ≤ 2 := by
      have h1 := hq.1
      have : ‖(modelSlabInv.{u} len a q).1‖ = Real.sqrt 2 * ‖sphereFirst q‖ := by
        simp only [modelSlabInv, norm_smul, LinearIsometryEquiv.norm_map,
          Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
      rw [this]
      have h0 : 0 ≤ Real.sqrt 2 * ‖sphereFirst q‖ := by positivity
      nlinarith
    change modelSphere.{u} len (modelSlabInv.{u} len a q) = q
    apply sphere_ext
    · rw [sphereFirst_modelSphere len hw, modelSlabInv, modelFirst,
        LinearIsometryEquiv.map_smul, LinearIsometryEquiv.apply_symm_apply, smul_smul,
        inv_mul_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne', one_smul]
    · rw [sphereSecond_modelSphere len hw]
      set z := sphereSecond q * (Circle.exp (-modelSlabAngle len a) : ℂ) with hz
      have hnorm : Real.sqrt (1 - ‖(modelSlabInv.{u} len a q).1‖ ^ 2 / 2) = ‖z‖ := by
        have : ‖(modelSlabInv.{u} len a q).1‖ ^ 2 = 2 * ‖sphereFirst q‖ ^ 2 := by
          simp only [modelSlabInv, norm_smul, LinearIsometryEquiv.norm_map,
            Real.norm_of_nonneg (Real.sqrt_nonneg 2), mul_pow, Real.sq_sqrt (by norm_num :
              (0 : ℝ) ≤ 2)]
        rw [this, hz, norm_mul, Circle.norm_coe, mul_one,
          show 1 - 2 * ‖sphereFirst q‖ ^ 2 / 2 = ‖sphereSecond q‖ ^ 2 by
            have := norm_sphereFirst_sq_add q
            linarith,
          Real.sqrt_sq (norm_nonneg _)]
      have hangle : modelAngleScale len * (modelSlabInv.{u} len a q).2 =
          modelSlabAngle len a + arg z := by
        simp only [modelSlabInv, modelSlabAngle, hz]
        field_simp
      rw [modelSecond, hnorm, hangle, Circle.exp_add, Circle.coe_mul, Circle.coe_exp (arg z),
        mul_comm (Circle.exp (modelSlabAngle len a) : ℂ), ← mul_assoc,
        norm_mul_exp_arg_mul_I, hz, mul_assoc, ← Circle.coe_mul, ← Circle.exp_add,
        neg_add_cancel, Circle.exp_zero, Circle.coe_one, mul_one]
  open_source := isOpen_modelSlab len a
  open_target := isOpen_modelSlabTarget.{u} len a
  contMDiffOn_toFun := by
    refine contMDiffOn_of_sphereFirst_sphereSecond (isOpen_modelSlab len a) ?_ ?_
    · have h : ContMDiffOn 𝓘(ℝ, ModelSpace) 𝓘(ℝ, ℂ) ∞ (fun p : ModelSpace => modelFirst p.1)
          (modelSlab len a) :=
        ((((Real.sqrt 2)⁻¹ • (modelPlaneComplex.toContinuousLinearEquiv :
          ModelPlane →L[ℝ] ℂ)).contDiff.comp contDiff_fst).contMDiff.contMDiffOn)
      exact h.congr (fun p hp => sphereFirst_modelSphere len
        (norm_sq_lt_two_of_mem_modelSlab hp).le)
    · have hsq : ContDiffOn ℝ ∞ (fun p : ModelSpace => Real.sqrt (1 - ‖p.1‖ ^ 2 / 2))
          (modelSlab len a) := by
        intro p hp
        have hpos : 0 < 1 - ‖p.1‖ ^ 2 / 2 := by
          have := norm_sq_lt_two_of_mem_modelSlab hp
          linarith
        have hn : ContDiff ℝ ∞ (fun p : ModelSpace => ‖p.1‖ ^ 2) :=
          (contDiff_norm_sq ℝ).comp contDiff_fst
        exact ((Real.contDiffAt_sqrt hpos.ne').comp p
          ((contDiff_const.sub (hn.div_const 2)).contDiffAt)).contDiffWithinAt
      have hexp : ContDiff ℝ ∞ (fun p : ModelSpace =>
          (Circle.exp (modelAngleScale len * p.2) : ℂ)) := by
        have : (fun p : ModelSpace => (Circle.exp (modelAngleScale len * p.2) : ℂ)) =
            fun p : ModelSpace => Complex.exp ((modelAngleScale len * p.2 : ℝ) * I) := by
          funext p
          rw [Circle.coe_exp]
        rw [this]
        exact Complex.contDiff_exp.comp
          ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_snd)).mul contDiff_const)
      have h : ContMDiffOn 𝓘(ℝ, ModelSpace) 𝓘(ℝ, ℂ) ∞ (fun p : ModelSpace => modelSecond len p)
          (modelSlab len a) := by
        have h1 : ContDiffOn ℝ ∞ (fun p : ModelSpace => (Real.sqrt (1 - ‖p.1‖ ^ 2 / 2) : ℂ))
            (modelSlab len a) := Complex.ofRealCLM.contDiff.comp_contDiffOn hsq
        exact (h1.mul hexp.contDiffOn).contMDiffOn
      exact h.congr (fun p hp => sphereSecond_modelSphere len
        (norm_sq_lt_two_of_mem_modelSlab hp).le)
  contMDiffOn_invFun := by
    have hfirst : ContMDiffOn (𝓡 3) 𝓘(ℝ, ModelPlane) ∞
        (fun q : SphereCarrier.{u} => Real.sqrt 2 • modelPlaneComplex.symm (sphereFirst q))
        (modelSlabTarget.{u} len a) :=
      (((Real.sqrt 2 • (modelPlaneComplex.symm.toContinuousLinearEquiv :
        ℂ →L[ℝ] ModelPlane)).contDiff.contMDiff).comp contMDiff_sphereFirst).contMDiffOn
    have harg : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞
        (fun q : SphereCarrier.{u} => arg (sphereSecond q *
          (Circle.exp (-modelSlabAngle len a) : ℂ))) (modelSlabTarget.{u} len a) := by
      intro q hq
      have hz := hq.2
      have hlog : ContDiffAt ℝ ∞ Complex.log
          (sphereSecond q * (Circle.exp (-modelSlabAngle len a) : ℂ)) :=
        (Complex.contDiffAt_log hz).restrict_scalars ℝ
      have hargd : ContDiffAt ℝ ∞ (fun z : ℂ => arg z)
          (sphereSecond q * (Circle.exp (-modelSlabAngle len a) : ℂ)) := by
        have : (fun z : ℂ => arg z) = fun z => (Complex.log z).im := by
          funext z
          rw [Complex.log_im]
        rw [this]
        exact Complex.imCLM.contDiff.contDiffAt.comp _ hlog
      have hmul : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℂ) ∞ (fun q : SphereCarrier.{u} => sphereSecond q *
          (Circle.exp (-modelSlabAngle len a) : ℂ)) q :=
        ((contDiff_id.mul contDiff_const).contMDiff.comp contMDiff_sphereSecond) q
      exact (hargd.contMDiffAt.comp q hmul).contMDiffWithinAt
    have hsecond : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞
        (fun q : SphereCarrier.{u} => a + 2 * len + arg (sphereSecond q *
          (Circle.exp (-modelSlabAngle len a) : ℂ)) / modelAngleScale len)
        (modelSlabTarget.{u} len a) := by
      have hf : ContDiff ℝ ∞ (fun x : ℝ => a + 2 * len + x / modelAngleScale len) :=
        contDiff_const.add (contDiff_id.div_const _)
      exact hf.contMDiff.comp_contMDiffOn harg
    exact hfirst.prodMk_space hsecond

theorem modelSphereChart_apply {len : ℕ} (hlen : 0 < len) (a : ℝ) (p : ModelSpace) :
    modelSphereChart.{u} hlen a p = modelSphere.{u} len p := rfl

theorem modelSphereChart_source {len : ℕ} (hlen : 0 < len) (a : ℝ) :
    (modelSphereChart.{u} hlen a).source = modelSlab len a := rfl

end GC.GraphManifold.Assembly

import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.OnePiece
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MobiusBlockAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MobiusBaseModel

/-!
Regular radial coordinates for the actual Möbius model annulus, with its inversion deck map.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.GraphManifold

attribute [local instance] finrank_real_complex_fact'

def mobiusRegularRadialScale (v : Circle) : ℝ :=
  Real.sqrt (12 + 4 * (v : ℂ).im ^ 2)

theorem mobiusRegularRadialScale_pos (v : Circle) : 0 < mobiusRegularRadialScale v :=
  Real.sqrt_pos.mpr (by positivity)

theorem mobiusRegularRadialScale_sq (v : Circle) :
    mobiusRegularRadialScale v ^ 2 = 12 + 4 * (v : ℂ).im ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem mobiusRegularRadialScale_inv (v : Circle) :
    mobiusRegularRadialScale v⁻¹ = mobiusRegularRadialScale v := by
  simp [mobiusRegularRadialScale]

def mobiusRegularRadius (v : Circle) (y : ℝ) : ℝ :=
  (mobiusRegularRadialScale v * y +
    Real.sqrt ((mobiusRegularRadialScale v * y) ^ 2 + 4)) / 2

theorem mobiusRegularRadius_pos (v : Circle) (y : ℝ) : 0 < mobiusRegularRadius v y := by
  have hs := Real.sqrt_nonneg ((mobiusRegularRadialScale v * y) ^ 2 + 4)
  have hsq := Real.sq_sqrt (show 0 ≤ (mobiusRegularRadialScale v * y) ^ 2 + 4 by positivity)
  dsimp only [mobiusRegularRadius]
  nlinarith [sq_nonneg (Real.sqrt ((mobiusRegularRadialScale v * y) ^ 2 + 4) +
    mobiusRegularRadialScale v * y)]

theorem mobiusRegularRadius_quadratic (v : Circle) (y : ℝ) :
    mobiusRegularRadius v y ^ 2 -
      mobiusRegularRadialScale v * y * mobiusRegularRadius v y = 1 := by
  have hsq := Real.sq_sqrt (show 0 ≤ (mobiusRegularRadialScale v * y) ^ 2 + 4 by positivity)
  dsimp only [mobiusRegularRadius]
  nlinarith

theorem mobiusRegularRadius_sub_inv (v : Circle) (y : ℝ) :
    mobiusRegularRadius v y - (mobiusRegularRadius v y)⁻¹ =
      mobiusRegularRadialScale v * y := by
  have hr := (mobiusRegularRadius_pos v y).ne'
  apply (mul_right_inj' hr).mp
  rw [mul_sub, mul_inv_cancel₀ hr]
  nlinarith [mobiusRegularRadius_quadratic v y]

theorem mobiusRegularRadius_inv_neg (v : Circle) (y : ℝ) :
    mobiusRegularRadius v⁻¹ (-y) = (mobiusRegularRadius v y)⁻¹ := by
  have hr := (mobiusRegularRadius_pos v y).ne'
  apply (mul_right_inj' hr).mp
  rw [mul_inv_cancel₀ hr]
  have hsq := Real.sq_sqrt (show 0 ≤ (mobiusRegularRadialScale v * y) ^ 2 + 4 by positivity)
  simp only [mobiusRegularRadius, mobiusRegularRadialScale_inv, mul_neg, neg_sq]
  nlinarith

def mobiusRegularAnnulusPoint (v : Circle) (y : ℝ) : ℂ :=
  (mobiusRegularRadius v y : ℂ) * (v : ℂ)

theorem mobiusRegularAnnulusPoint_ne_zero (v : Circle) (y : ℝ) :
    mobiusRegularAnnulusPoint v y ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (mobiusRegularRadius_pos v y).ne')
    (Circle.coe_ne_zero v)

theorem norm_mobiusRegularAnnulusPoint (v : Circle) (y : ℝ) :
    ‖mobiusRegularAnnulusPoint v y‖ = mobiusRegularRadius v y := by
  simp only [mobiusRegularAnnulusPoint, norm_mul, Circle.norm_coe, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (mobiusRegularRadius_pos v y).le]

theorem mobiusRegularAnnulusPoint_inv_neg (v : Circle) (y : ℝ) :
    mobiusRegularAnnulusPoint v⁻¹ (-y) = (mobiusRegularAnnulusPoint v y)⁻¹ := by
  simp [mobiusRegularAnnulusPoint, mobiusRegularRadius_inv_neg, mul_inv_rev, mul_comm]

theorem joukowski_radial_norm_sq (v : Circle) (r : ℝ) (hr : 0 < r) :
    ‖joukowski ((r : ℂ) * (v : ℂ))‖ ^ 2 =
      (9 / 16 : ℝ) * ((r - r⁻¹) ^ 2 + 4 - 4 * (v : ℂ).im ^ 2) := by
  have hv : (v : ℂ).re ^ 2 + (v : ℂ).im ^ 2 = 1 := by
    have h := Circle.normSq_coe v
    change (v : ℂ).re * (v : ℂ).re + (v : ℂ).im * (v : ℂ).im = 1 at h
    nlinarith
  have hi : (((r : ℂ) * (v : ℂ))⁻¹) = (r⁻¹ : ℂ) * conj (v : ℂ) := by
    rw [mul_inv_rev, ← Circle.coe_inv_eq_conj, Circle.coe_inv]
    simp [mul_comm]
  have hri : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  have hj : joukowski ((r : ℂ) * (v : ℂ)) =
      ((3 / 4 : ℝ) : ℂ) *
        (((r + r⁻¹) * (v : ℂ).re : ℝ) +
          (((r - r⁻¹) * (v : ℂ).im : ℝ) : ℂ) * Complex.I) := by
    rw [joukowski, hi]
    apply Complex.ext <;> simp <;> ring
  have hn0 : Complex.normSq (((3 / 4 : ℝ) : ℂ)) = (9 / 16 : ℝ) := by
    norm_num [Complex.normSq_apply]
  have hn1 : Complex.normSq
      (((r + r⁻¹) * (v : ℂ).re : ℝ) +
        (((r - r⁻¹) * (v : ℂ).im : ℝ) : ℂ) * Complex.I) =
      (r + r⁻¹) ^ 2 * (v : ℂ).re ^ 2 +
        (r - r⁻¹) ^ 2 * (v : ℂ).im ^ 2 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [← Complex.normSq_eq_norm_sq, hj, Complex.normSq_mul, hn0, hn1]
  calc
    (9 / 16 : ℝ) * ((r + r⁻¹) ^ 2 * (v : ℂ).re ^ 2 +
        (r - r⁻¹) ^ 2 * (v : ℂ).im ^ 2) =
      (9 / 16 : ℝ) * ((r - r⁻¹) ^ 2 *
        ((v : ℂ).re ^ 2 + (v : ℂ).im ^ 2) +
        4 * (r * r⁻¹) * (v : ℂ).re ^ 2) := by ring
    _ = (9 / 16 : ℝ) * ((r - r⁻¹) ^ 2 + 4 - 4 * (v : ℂ).im ^ 2) := by
      rw [hv, hri]
      nlinarith [hv]

theorem joukowski_mobiusRegularAnnulusPoint_norm_sq (v : Circle) (y : ℝ) :
    ‖joukowski (mobiusRegularAnnulusPoint v y)‖ ^ 2 =
      9 + (9 / 16 : ℝ) * (mobiusRegularRadialScale v) ^ 2 * (y ^ 2 - 1) := by
  rw [mobiusRegularAnnulusPoint,
    joukowski_radial_norm_sq v _ (mobiusRegularRadius_pos v y),
    mobiusRegularRadius_sub_inv, mul_pow]
  nlinarith [mobiusRegularRadialScale_sq v]

theorem mobiusRegularAnnulusPoint_mem_iff (v : Circle) (y : ℝ) :
    ‖joukowski (mobiusRegularAnnulusPoint v y)‖ ≤ 3 ↔ y ^ 2 ≤ 1 := by
  have hsq := joukowski_mobiusRegularAnnulusPoint_norm_sq v y
  have ha : 0 < (mobiusRegularRadialScale v) ^ 2 := sq_pos_of_pos
    (mobiusRegularRadialScale_pos v)
  have hn := norm_nonneg (joukowski (mobiusRegularAnnulusPoint v y))
  constructor <;> intro h <;> nlinarith

def mobiusRegularHeight (u : ℂ) : ℝ :=
  (‖u‖ - ‖u‖⁻¹) / mobiusRegularRadialScale (unitOf u)

theorem mobiusRegularRadius_eq_of_sub_inv (v : Circle) (y r : ℝ) (hr : 0 < r)
    (h : r - r⁻¹ = mobiusRegularRadialScale v * y) : mobiusRegularRadius v y = r := by
  have hR := mobiusRegularRadius_pos v y
  have heq := (mobiusRegularRadius_sub_inv v y).trans h.symm
  have hprod : (mobiusRegularRadius v y - r) * (mobiusRegularRadius v y * r + 1) = 0 := by
    have hc := congrArg (fun a : ℝ => a * (mobiusRegularRadius v y * r)) heq
    field_simp at hc
    nlinarith [hc]
  have hp : 0 < mobiusRegularRadius v y * r + 1 := by positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hp.ne')

theorem mobiusRegularRadius_height {u : ℂ} (hu : u ≠ 0) :
    mobiusRegularRadius (unitOf u) (mobiusRegularHeight u) = ‖u‖ := by
  apply mobiusRegularRadius_eq_of_sub_inv _ _ _ (norm_pos_iff.mpr hu)
  rw [mobiusRegularHeight, mul_div_cancel₀ _ (mobiusRegularRadialScale_pos _).ne']

theorem mobiusRegularAnnulusPoint_height {u : ℂ} (hu : u ≠ 0) :
    mobiusRegularAnnulusPoint (unitOf u) (mobiusRegularHeight u) = u := by
  rw [mobiusRegularAnnulusPoint, mobiusRegularRadius_height hu, coe_norm_mul_unitOf]

theorem unitOf_mobiusRegularAnnulusPoint (v : Circle) (y : ℝ) :
    unitOf (mobiusRegularAnnulusPoint v y) = v :=
  unitOf_ofReal_mul (mobiusRegularRadius_pos v y) v

theorem mobiusRegularHeight_annulusPoint (v : Circle) (y : ℝ) :
    mobiusRegularHeight (mobiusRegularAnnulusPoint v y) = y := by
  rw [mobiusRegularHeight, norm_mobiusRegularAnnulusPoint,
    unitOf_mobiusRegularAnnulusPoint, mobiusRegularRadius_sub_inv]
  exact mul_div_cancel_left₀ y (mobiusRegularRadialScale_pos v).ne'

theorem mobiusRegularHeight_inv {u : ℂ} (hu : u ≠ 0) :
    mobiusRegularHeight u⁻¹ = -mobiusRegularHeight u := by
  rw [mobiusRegularHeight, mobiusRegularHeight, norm_inv, unitOf_inv hu,
    mobiusRegularRadialScale_inv, inv_inv]
  ring

theorem mobiusRegularHeight_mem_iff {u : ℂ} (hu : u ≠ 0) :
    ‖joukowski u‖ ≤ 3 ↔ mobiusRegularHeight u ^ 2 ≤ 1 := by
  rw [← mobiusRegularAnnulusPoint_height hu]
  rw [mobiusRegularAnnulusPoint_mem_iff, mobiusRegularHeight_annulusPoint]


theorem contMDiff_mobiusRegularRadialScale :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ mobiusRegularRadialScale := by
  have hi : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun v : Circle => (v : ℂ).im) :=
    Complex.imCLM.contDiff.contMDiff.comp contMDiff_coe_sphere
  have h : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞
      (fun v : Circle => 12 + 4 * (v : ℂ).im ^ 2) :=
    contMDiff_const.add (contMDiff_const.mul (hi.pow 2))
  intro v
  exact (Real.contDiffAt_sqrt (by positivity)).comp_contMDiffAt h.contMDiffAt

theorem contMDiff_mobiusRegularRadius :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : Circle × ℝ => mobiusRegularRadius p.1 p.2) := by
  have h : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : Circle × ℝ => mobiusRegularRadialScale p.1 * p.2) :=
    (contMDiff_mobiusRegularRadialScale.comp contMDiff_fst).mul contMDiff_snd
  have hs : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : Circle × ℝ => Real.sqrt ((mobiusRegularRadialScale p.1 * p.2) ^ 2 + 4)) := by
    intro p
    exact (Real.contDiffAt_sqrt (by positivity)).comp_contMDiffAt
      ((h.pow 2).add contMDiff_const).contMDiffAt
  exact (h.add hs).div₀ contMDiff_const (fun p => by norm_num)

theorem contMDiff_mobiusRegularAnnulusPoint :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) ∞
      (fun p : Circle × ℝ => mobiusRegularAnnulusPoint p.1 p.2) := by
  have hr : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) ∞
      (fun p : Circle × ℝ => (mobiusRegularRadius p.1 p.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.contMDiff.comp contMDiff_mobiusRegularRadius
  have hv : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) ∞
      (fun p : Circle × ℝ => (p.1 : ℂ)) :=
    contMDiff_coe_sphere.comp contMDiff_fst
  exact (contDiff_fst.mul contDiff_snd).comp_contMDiff (hr.prodMk_space hv)

theorem contMDiffAt_mobiusRegularHeight {u : ℂ} (hu : u ≠ 0) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ mobiusRegularHeight u := by
  have hn : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (fun z : ℂ => ‖z‖) u :=
    (contDiffAt_norm ℝ hu).contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ, ℂ) (𝓡 1) ∞ unitOf u :=
    contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hu)
  exact (hn.sub (hn.inv₀ (norm_ne_zero_iff.mpr hu))).div₀
    (contMDiff_mobiusRegularRadialScale.contMDiffAt.comp u hv)
    (mobiusRegularRadialScale_pos _).ne'

def mobiusPuncturedComplex : TopologicalSpace.Opens ℂ :=
  ⟨{z | z ≠ 0}, isOpen_ne⟩

def mobiusRegularRadialDiffeomorph :
    (Circle × ℝ) ≃ₘ⟮(𝓡 1).prod 𝓘(ℝ, ℝ), 𝓘(ℝ, ℂ)⟯ mobiusPuncturedComplex where
  toFun p := ⟨mobiusRegularAnnulusPoint p.1 p.2,
    mobiusRegularAnnulusPoint_ne_zero p.1 p.2⟩
  invFun z := (unitOf z.val, mobiusRegularHeight z.val)
  left_inv p := by
    exact Prod.ext (unitOf_mobiusRegularAnnulusPoint p.1 p.2)
      (mobiusRegularHeight_annulusPoint p.1 p.2)
  right_inv z := Subtype.ext (mobiusRegularAnnulusPoint_height z.property)
  contMDiff_toFun := by
    intro p
    exact (ContMDiffAt.subtypeVal_comp_iff mobiusPuncturedComplex _ p).mp
      contMDiff_mobiusRegularAnnulusPoint.contMDiffAt
  contMDiff_invFun := by
    intro z
    exact ((contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds z.property)).comp z
      contMDiff_subtype_val.contMDiffAt).prodMk
      ((contMDiffAt_mobiusRegularHeight z.property).comp z
        contMDiff_subtype_val.contMDiffAt)


theorem mobiusBandCover_neg_neg (z : Circle) (y : ℝ) :
    mobiusBandCover (-z, -y) = mobiusBandCover (z, y) := by
  have he : Circle.exp (Complex.arg (z : ℂ) + Real.pi) = -z := by
    apply Circle.ext
    have h := coe_circleExp_add_int_mul_pi (Complex.arg (z : ℂ)) 1
    simpa only [Int.cast_one, one_mul, zpow_one, neg_one_mul,
      Circle.exp_arg, Circle.coe_neg] using h
  rw [← he, mobiusBandCover_exp, mobiusProj_add_pi]
  exact (mobiusBandCover_exp (Complex.arg (z : ℂ)) y).symm.trans
    (congrArg (fun t : Circle => mobiusBandCover (t, y)) (Circle.exp_arg z))

def mobiusRegularBaseParam (p : Circle × unitInterval) : mobiusSurface.{u}.Carrier :=
  ⟨ULift.up (mobiusBandCover (p.1, 2 * (p.2 : ℝ) - 1)), by
    change mobiusWidth (mobiusBandCover (p.1, 2 * (p.2 : ℝ) - 1)) ≤ 1
    rw [mobiusWidth_cover]
    nlinarith [p.2.property.1, p.2.property.2]⟩

theorem mobiusRegularBaseParam_deck (p : Circle × unitInterval) :
    mobiusRegularBaseParam.{u} (-p.1, unitInterval.symm p.2) =
      mobiusRegularBaseParam.{u} p := by
  apply Subtype.ext
  apply ULift.ext
  change mobiusBandCover (-p.1, 2 * (1 - (p.2 : ℝ)) - 1) =
    mobiusBandCover (p.1, 2 * (p.2 : ℝ) - 1)
  rw [show 2 * (1 - (p.2 : ℝ)) - 1 = -(2 * (p.2 : ℝ) - 1) by ring]
  exact mobiusBandCover_neg_neg p.1 _

theorem mobiusRegularBaseParam_surjective :
    Function.Surjective mobiusRegularBaseParam.{u} := by
  intro x
  have hx := (Set.ext_iff.mp mobiusSet_eq_image.{u} x.val).mp x.property
  obtain ⟨p, hp, he⟩ := hx
  let t : unitInterval := ⟨(p.2 + 1) / 2, by constructor <;> linarith [hp.2.1, hp.2.2]⟩
  refine ⟨(Circle.exp p.1, t), ?_⟩
  apply Subtype.ext
  change ULift.up (mobiusBandCover (Circle.exp p.1, 2 * ((p.2 + 1) / 2) - 1)) = x.val
  rw [show 2 * ((p.2 + 1) / 2) - 1 = p.2 by ring, mobiusBandCover_exp]
  exact he


theorem contMDiff_mobiusRegularBaseParam :
    ContMDiff ((𝓡 1).prod (𝓡∂ 1))
      (SurfaceModel.model mobiusSurface.{u}.kind) ∞ mobiusRegularBaseParam.{u} := by
  apply (mobiusAtlas.contMDiff_iff_subtype_val _).mpr
  have ht : ContMDiff ((𝓡 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : Circle × unitInterval => 2 * (p.2 : ℝ) - 1) :=
    (contMDiff_const.mul (contMDiff_subtypeVal_Icc.comp contMDiff_snd)).sub contMDiff_const
  exact contMDiff_mobiusLift_up.comp
    (contMDiff_mobiusCover.comp (contMDiff_fst.prodMk ht))


end GC.GraphManifold

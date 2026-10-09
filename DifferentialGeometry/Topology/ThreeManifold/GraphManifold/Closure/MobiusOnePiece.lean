import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MobiusRegularCoordinates
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.LensCover
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MobiusTwistedCover

/-!
The regular two-sheeted normalized cover of the actual Möbius bundle carrier.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.GraphManifold

attribute [local instance] finrank_real_complex_fact'

def mobiusRegularDeck (p : (Circle × unitInterval) × Circle) :
    (Circle × unitInterval) × Circle := ((-p.1.1, unitInterval.symm p.1.2), p.2⁻¹)

def mobiusRegularModel (p : (Circle × unitInterval) × Circle) : ℂ × ℂ :=
  ((p.1.1 : ℂ), mobiusRegularAnnulusPoint p.2 (2 * (p.1.2 : ℝ) - 1))

theorem mobiusRegularModel_deck (p : (Circle × unitInterval) × Circle) :
    mobiusRegularModel (mobiusRegularDeck p) = modelDeck (mobiusRegularModel p) := by
  apply Prod.ext
  · rfl
  · change mobiusRegularAnnulusPoint p.2⁻¹ (2 * (1 - (p.1.2 : ℝ)) - 1) = _
    rw [show 2 * (1 - (p.1.2 : ℝ)) - 1 = -(2 * (p.1.2 : ℝ) - 1) by ring]
    exact mobiusRegularAnnulusPoint_inv_neg p.2 _

theorem mobiusRegularModel_injective : Function.Injective mobiusRegularModel := by
  intro p q h
  have h1 : p.1.1 = q.1.1 := Circle.ext (congrArg Prod.fst h)
  have h2 := congrArg (fun z : ℂ × ℂ => unitOf z.2) h
  change unitOf (mobiusRegularAnnulusPoint p.2 (2 * (p.1.2 : ℝ) - 1)) =
    unitOf (mobiusRegularAnnulusPoint q.2 (2 * (q.1.2 : ℝ) - 1)) at h2
  rw [unitOf_mobiusRegularAnnulusPoint, unitOf_mobiusRegularAnnulusPoint] at h2
  have ht := congrArg (fun z : ℂ × ℂ => mobiusRegularHeight z.2) h
  change mobiusRegularHeight (mobiusRegularAnnulusPoint p.2 (2 * (p.1.2 : ℝ) - 1)) =
    mobiusRegularHeight (mobiusRegularAnnulusPoint q.2 (2 * (q.1.2 : ℝ) - 1)) at ht
  rw [mobiusRegularHeight_annulusPoint, mobiusRegularHeight_annulusPoint] at ht
  have h3 : p.1.2 = q.1.2 := Subtype.ext (by linarith)
  exact Prod.ext (Prod.ext h1 h3) h2

theorem mobiusRegularModel_mem (p : (Circle × unitInterval) × Circle) :
    ‖joukowski (mobiusRegularModel p).2‖ ≤ 3 := by
  apply (mobiusRegularAnnulusPoint_mem_iff _ _).mpr
  nlinarith [p.1.2.property.1, p.1.2.property.2]

theorem exists_mobiusRegularSphere (p : (Circle × unitInterval) × Circle) :
    ∃ x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      bundleQuartic (lensPair x) ≤ 0 ∧ modelPoint (lensPair x) = mobiusRegularModel p :=
  exists_sphere_modelPoint _ _ (Circle.norm_coe p.1.1)
    (mobiusRegularAnnulusPoint_ne_zero _ _) (mobiusRegularModel_mem p)

def mobiusRegularSphere (p : (Circle × unitInterval) × Circle) :
    sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := (exists_mobiusRegularSphere p).choose

theorem mobiusRegularSphere_quartic (p : (Circle × unitInterval) × Circle) :
    bundleQuartic (lensPair (mobiusRegularSphere p)) ≤ 0 :=
  (exists_mobiusRegularSphere p).choose_spec.1

theorem mobiusRegularSphere_model (p : (Circle × unitInterval) × Circle) :
    modelPoint (lensPair (mobiusRegularSphere p)) = mobiusRegularModel p :=
  (exists_mobiusRegularSphere p).choose_spec.2

def mobiusRegularTotalCover (p : (Circle × unitInterval) × Circle) :
    mobiusBundleCarrier.{u}.Carrier :=
  ⟨lensUp (mobiusLensGroup.projection (mobiusRegularSphere p)),
    mobiusRegularSphere_quartic p⟩

theorem mobiusRegularTotalCover_eq_iff (p q : (Circle × unitInterval) × Circle) :
    mobiusRegularTotalCover.{u} p = mobiusRegularTotalCover.{u} q ↔
      q = p ∨ q = mobiusRegularDeck p := by
  have he : mobiusRegularTotalCover.{u} p = mobiusRegularTotalCover.{u} q ↔
      mobiusLensGroup.projection (mobiusRegularSphere p) =
        mobiusLensGroup.projection (mobiusRegularSphere q) := by
    constructor
    · intro h
      exact congrArg (fun x : mobiusBundleCarrier.{u}.Carrier => lensDown x.val) h
    · intro h
      exact Subtype.ext (congrArg lensUp h)
  rw [he, projection_eq_iff_modelPoint _ _ (mobiusRegularSphere_quartic p)
    (mobiusRegularSphere_quartic q), mobiusRegularSphere_model, mobiusRegularSphere_model,
    ← mobiusRegularModel_deck]
  exact or_congr (mobiusRegularModel_injective.eq_iff) (mobiusRegularModel_injective.eq_iff)

theorem mobiusRegularTotalCover_surjective :
    Function.Surjective mobiusRegularTotalCover.{u} := by
  intro a
  obtain ⟨x, hx, hq⟩ := exists_sphere_rep a
  have hd := sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero x) hq
  obtain ⟨hm, hp⟩ := sub_ne_zero_of_sq_sub_sq_ne_zero hd
  let w := modelAnnulusPoint (lensPair x)
  have hw : w ≠ 0 := div_ne_zero (neg_ne_zero.mpr hp) hm
  have hJ : ‖joukowski w‖ ≤ 3 := by
    rw [joukowski_modelAnnulusPoint hd]
    exact (bundleQuartic_nonpos_iff hd).mp hq
  have hy := (mobiusRegularHeight_mem_iff hw).mp hJ
  let t : unitInterval := ⟨(mobiusRegularHeight w + 1) / 2, by
    constructor <;> nlinarith [sq_nonneg (mobiusRegularHeight w + 1),
      sq_nonneg (mobiusRegularHeight w - 1)]⟩
  let z : Circle := unitOf ((lensPair x).1 ^ 2 - (lensPair x).2 ^ 2)
  let p : (Circle × unitInterval) × Circle := ((z, t), unitOf w)
  have he : mobiusRegularModel p = modelPoint (lensPair x) := by
    apply Prod.ext
    · change (unitOf ((lensPair x).1 ^ 2 - (lensPair x).2 ^ 2) : ℂ) = _
      change (unitOf ((lensPair x).1 ^ 2 - (lensPair x).2 ^ 2) : ℂ) =
        modelFibrePoint (lensPair x)
      rw [coe_unitOf hd]
      simp [modelFibrePoint, div_eq_mul_inv, mul_comm]
    · change mobiusRegularAnnulusPoint (unitOf w)
        (2 * ((mobiusRegularHeight w + 1) / 2) - 1) = w
      rw [show 2 * ((mobiusRegularHeight w + 1) / 2) - 1 = mobiusRegularHeight w by ring]
      exact mobiusRegularAnnulusPoint_height hw
  refine ⟨p, ?_⟩
  apply Subtype.ext
  change lensUp (mobiusLensGroup.projection (mobiusRegularSphere p)) = a.val
  rw [← lensUp_lensDown a.val, hx]
  apply congrArg lensUp
  apply (projection_eq_iff_modelPoint _ _ (mobiusRegularSphere_quartic p) hq).mpr
  exact Or.inl (by rw [mobiusRegularSphere_model, he])

def mobiusSphereScale (w : ℂ) : ℝ := (Real.sqrt (2 * (‖w‖ ^ 2 + 1)))⁻¹

theorem mobiusSphereScale_pos (w : ℂ) : 0 < mobiusSphereScale w :=
  inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

theorem mobiusSphereScale_norm_identity (w : ℂ) :
    mobiusSphereScale w ^ 2 * (‖w - 1‖ ^ 2 + ‖w + 1‖ ^ 2) = 1 := by
  have he : ‖w - 1‖ ^ 2 + ‖w + 1‖ ^ 2 = 2 * (‖w‖ ^ 2 + 1) := by
    rw [norm_sub_sq_real, norm_add_sq_real]
    norm_num
    ring
  rw [he, mobiusSphereScale, inv_pow, Real.sq_sqrt (by positivity),
    inv_mul_cancel₀ (by positivity)]

def mobiusSphereFormula (w : ℂ) (κ : Circle) : EuclideanSpace ℝ (Fin 4) :=
  lensPair.symm (((mobiusSphereScale w : ℂ) * κ) * (w - 1),
    ((mobiusSphereScale w : ℂ) * κ) * (w + 1))

theorem mobiusSphereFormula_mem (w : ℂ) (κ : Circle) :
    mobiusSphereFormula w κ ∈ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have he := norm_sq_eq_lensPair (mobiusSphereFormula w κ)
  simp only [mobiusSphereFormula, lensPair.apply_symm_apply] at he
  change ‖mobiusSphereFormula w κ‖ ^ 2 =
    ‖(mobiusSphereScale w : ℂ) * κ * (w - 1)‖ ^ 2 +
      ‖(mobiusSphereScale w : ℂ) * κ * (w + 1)‖ ^ 2 at he
  simp only [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (mobiusSphereScale_pos w).le] at he
  rw [mul_pow, mul_pow, ← mul_add, mobiusSphereScale_norm_identity] at he
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp he

def mobiusSphereParam (w : ℂ) (κ : Circle) : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  ⟨mobiusSphereFormula w κ, mobiusSphereFormula_mem w κ⟩

theorem mobiusSphereParam_annulus (w : ℂ) (κ : Circle) :
    modelAnnulusPoint (lensPair (mobiusSphereParam w κ)) = w := by
  have hc : (mobiusSphereScale w : ℂ) * κ ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (mobiusSphereScale_pos w).ne')
      (Circle.coe_ne_zero κ)
  change modelAnnulusPoint (lensPair (lensPair.symm _)) = w
  rw [lensPair.apply_symm_apply, modelAnnulusPoint]
  dsimp only
  rw [show ((mobiusSphereScale w : ℂ) * κ) * (w - 1) -
    ((mobiusSphereScale w : ℂ) * κ) * (w + 1) =
      -2 * ((mobiusSphereScale w : ℂ) * κ) by ring,
    div_eq_iff (mul_ne_zero (by norm_num) hc)]
  ring

theorem contMDiff_mobiusSphereScale :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ mobiusSphereScale := by
  have hn : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (fun w : ℂ => 2 * (‖w‖ ^ 2 + 1)) :=
    contMDiff_const.mul ((contDiff_norm_sq ℝ).contMDiff.add contMDiff_const)
  have hs : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
      (fun w : ℂ => Real.sqrt (2 * (‖w‖ ^ 2 + 1))) := by
    intro w
    exact (Real.contDiffAt_sqrt (by positivity)).comp_contMDiffAt hn.contMDiffAt
  exact hs.inv₀ (fun w => (Real.sqrt_pos.mpr (by positivity)).ne')

theorem contMDiff_mobiusSphereFormula :
    ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ∞
      (fun p : ℂ × Circle => mobiusSphereFormula p.1 p.2) := by
  have hr : ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℂ × Circle => (mobiusSphereScale p.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.contMDiff.comp
      (contMDiff_mobiusSphereScale.comp contMDiff_fst)
  have hk : ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℂ × Circle => (p.2 : ℂ)) := contMDiff_coe_sphere.comp contMDiff_snd
  have hc := (contDiff_fst.mul contDiff_snd).comp_contMDiff (hr.prodMk_space hk)
  have hm : ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℂ × Circle => (mobiusSphereScale p.1 : ℂ) * p.2 * (p.1 - 1)) :=
    (contDiff_fst.mul contDiff_snd).comp_contMDiff
    (hc.prodMk_space (contMDiff_fst.sub contMDiff_const))
  have hp : ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℂ × Circle => (mobiusSphereScale p.1 : ℂ) * p.2 * (p.1 + 1)) :=
    (contDiff_fst.mul contDiff_snd).comp_contMDiff
    (hc.prodMk_space (contMDiff_fst.add contMDiff_const))
  exact lensPair.symm.contDiff.contMDiff.comp (hm.prodMk_space hp)

theorem contMDiff_mobiusSphereParam :
    ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞
      (fun p : ℂ × Circle => mobiusSphereParam p.1 p.2) := by
  exact contMDiff_mobiusSphereFormula.codRestrict_sphere
    (fun p => mobiusSphereFormula_mem p.1 p.2)

theorem mobiusSphereParam_fibre (w : ℂ) (κ : Circle) (hw : w ≠ 0) :
    modelFibrePoint (lensPair (mobiusSphereParam w κ)) = -(κ : ℂ) ^ 2 * (unitOf w : ℂ) := by
  let r := mobiusSphereScale w
  let c : ℂ := (r : ℂ) * κ
  have hr : 0 < r := mobiusSphereScale_pos w
  have hc : ‖c‖ = r := by
    rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hp : lensPair (mobiusSphereParam w κ) = (c * (w - 1), c * (w + 1)) :=
    lensPair.apply_symm_apply _
  have hd : (c * (w - 1)) ^ 2 - (c * (w + 1)) ^ 2 = -4 * c ^ 2 * w := by ring
  have hn : ‖(c * (w - 1)) ^ 2 - (c * (w + 1)) ^ 2‖ = 4 * r ^ 2 * ‖w‖ := by
    rw [hd, norm_mul, norm_mul, norm_neg, norm_pow, hc]
    norm_num
  have hnz : (((4 * r ^ 2 * ‖w‖ : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr.ne'))
      (norm_ne_zero_iff.mpr hw))
  rw [modelFibrePoint, hp]
  dsimp only
  rw [hn, hd, coe_unitOf hw, div_eq_iff hnz]
  dsimp only [c]
  rw [Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)]

theorem mobiusSphereParam_regularModel (p : (Circle × unitInterval) × Circle) (κ : Circle)
    (hκ : κ ^ 2 = -p.1.1 * p.2⁻¹) :
    modelPoint (lensPair (mobiusSphereParam (mobiusRegularModel p).2 κ)) =
      mobiusRegularModel p := by
  apply Prod.ext
  · change modelFibrePoint (lensPair (mobiusSphereParam (mobiusRegularModel p).2 κ)) = _
    rw [mobiusSphereParam_fibre _ κ
      (show (mobiusRegularModel p).2 ≠ 0 from mobiusRegularAnnulusPoint_ne_zero _ _)]
    change -(κ : ℂ) ^ 2 *
      (unitOf (mobiusRegularAnnulusPoint p.2 (2 * (p.1.2 : ℝ) - 1)) : ℂ) = (p.1.1 : ℂ)
    rw [unitOf_mobiusRegularAnnulusPoint, ← Circle.coe_pow, hκ]
    simp
  · exact mobiusSphereParam_annulus _ κ

theorem mobiusSphereParam_regularQuartic (p : (Circle × unitInterval) × Circle) (κ : Circle)
    (hκ : κ ^ 2 = -p.1.1 * p.2⁻¹) :
    bundleQuartic (lensPair (mobiusSphereParam (mobiusRegularModel p).2 κ)) ≤ 0 := by
  have hf := congrArg Prod.fst (mobiusSphereParam_regularModel p κ hκ)
  have hd : (lensPair (mobiusSphereParam (mobiusRegularModel p).2 κ)).1 ^ 2 -
      (lensPair (mobiusSphereParam (mobiusRegularModel p).2 κ)).2 ^ 2 ≠ 0 := by
    intro hz
    change modelFibrePoint _ = (p.1.1 : ℂ) at hf
    simp only [modelFibrePoint, hz, norm_zero, Complex.ofReal_zero, zero_div] at hf
    exact Circle.coe_ne_zero p.1.1 hf.symm
  rw [bundleQuartic_nonpos_iff hd, ← joukowski_modelAnnulusPoint hd]
  have ha := congrArg Prod.snd (mobiusSphereParam_regularModel p κ hκ)
  change modelAnnulusPoint (lensPair (mobiusSphereParam (mobiusRegularModel p).2 κ)) =
    (mobiusRegularModel p).2 at ha
  rw [ha]
  exact mobiusRegularModel_mem p

theorem mobiusRegularTotalCover_formula (p : (Circle × unitInterval) × Circle) (κ : Circle)
    (hκ : κ ^ 2 = -p.1.1 * p.2⁻¹) :
    (mobiusRegularTotalCover.{u} p).val =
      lensUp (mobiusLensGroup.projection (mobiusSphereParam (mobiusRegularModel p).2 κ)) := by
  apply congrArg lensUp
  apply (projection_eq_iff_modelPoint _ _ (mobiusRegularSphere_quartic p)
    (mobiusSphereParam_regularQuartic p κ hκ)).mpr
  exact Or.inl ((mobiusSphereParam_regularModel p κ hκ).trans
    (mobiusRegularSphere_model p).symm)

def mobiusRegularRootPhase (p : (Circle × unitInterval) × Circle) : Circle := -p.1.1 * p.2⁻¹

theorem contMDiff_mobiusRegularRootPhase :
    ContMDiff (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) (𝓡 1) ∞
      mobiusRegularRootPhase := by
  have hz : ContMDiff (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) (𝓡 1) ∞
      (fun p : (Circle × unitInterval) × Circle => p.1.1) :=
    contMDiff_fst.comp contMDiff_fst
  have hv : ContMDiff (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) (𝓡 1) ∞
      (fun p : (Circle × unitInterval) × Circle => p.2) := contMDiff_snd
  change ContMDiff (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) (𝓡 1) ∞
    (fun p : (Circle × unitInterval) × Circle => -p.1.1 * p.2⁻¹)
  have h := (contMDiff_const (c := (-1 : Circle)).mul hz).mul hv.inv
  convert h using 1
  funext p
  apply Circle.ext
  simp

theorem contMDiff_mobiusRegularIntervalHeight :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (fun t : unitInterval => 2 * (t : ℝ) - 1) :=
  (contMDiff_const.mul contMDiff_subtypeVal_Icc).sub contMDiff_const

theorem contMDiff_mobiusRegularHeightParam :
    ContMDiff (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : (Circle × unitInterval) × Circle => 2 * (p.1.2 : ℝ) - 1) :=
  contMDiff_mobiusRegularIntervalHeight.comp (contMDiff_snd.comp contMDiff_fst)

theorem contMDiff_mobiusRegularAnnulusPair :
    ContMDiff (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : (Circle × unitInterval) × Circle => (p.2, 2 * (p.1.2 : ℝ) - 1)) :=
  contMDiff_snd.prodMk contMDiff_mobiusRegularHeightParam

theorem contMDiff_mobiusRegularAnnulusParam :
    ContMDiff (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (Circle × unitInterval) × Circle => (mobiusRegularModel p).2) := by
  have h := contMDiff_mobiusRegularAnnulusPoint.comp contMDiff_mobiusRegularAnnulusPair
  simpa only [Function.comp_def, mobiusRegularModel] using h

def mobiusRegularLocalLift (p q : (Circle × unitInterval) × Circle) :
    sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  mobiusSphereParam (mobiusRegularModel q).2
    (localRoot 2 (mobiusRegularRootPhase p) (mobiusRegularRootPhase q))

theorem contMDiffAt_mobiusRegularLocalLift (p : (Circle × unitInterval) × Circle) :
    ContMDiffAt (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) (𝓡 3) ∞
      (mobiusRegularLocalLift p) p := by
  have hκ : ContMDiffAt (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) (𝓡 1) ∞
      (fun q => localRoot 2 (mobiusRegularRootPhase p) (mobiusRegularRootPhase q)) p :=
    (contMDiffAt_localRoot 2 _).comp p contMDiff_mobiusRegularRootPhase.contMDiffAt
  have hpair := contMDiff_mobiusRegularAnnulusParam.contMDiffAt.prodMk hκ
  have h := contMDiff_mobiusSphereParam.contMDiffAt.comp p hpair
  exact h.congr (fun q hq => rfl) rfl

theorem contMDiffAt_mobiusRegularProjectedLift (p : (Circle × unitInterval) × Circle) :
    ContMDiffAt (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) (𝓡 3) ∞
      (fun q => mobiusLensGroup.projection (mobiusRegularLocalLift p q)) p :=
  mobiusLensGroup.projection_isLocalDiffeomorph.contMDiff.contMDiffAt.comp p
    (contMDiffAt_mobiusRegularLocalLift p)

theorem contMDiff_mobiusRegularTotalCover_val :
    ContMDiff (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) (𝓡 3) ∞
      (fun p => (mobiusRegularTotalCover.{u} p).val) := by
  intro p
  have h := contMDiff_lensUp.contMDiffAt.comp p (contMDiffAt_mobiusRegularProjectedLift p)
  have he : (fun q => (mobiusRegularTotalCover.{u} q).val) =
      fun q => lensUp.{u} (mobiusLensGroup.projection (mobiusRegularLocalLift p q)) := by
    funext q
    exact mobiusRegularTotalCover_formula q _ (localRoot_pow 2 _ _)
  rw [he]
  exact h

theorem contMDiff_mobiusRegularTotalCover :
    ContMDiff (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) mobiusBundleCarrier.{u}.model ∞
      mobiusRegularTotalCover.{u} :=
  (mobiusBundleAtlas.contMDiff_iff_subtype_val _).mpr contMDiff_mobiusRegularTotalCover_val

def mobiusSphereInverse (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) : ℂ × Circle :=
  (modelAnnulusPoint (lensPair x), unitOf ((lensPair x).2 - (lensPair x).1))

theorem mobiusSphereParam_phase (w : ℂ) (κ : Circle) :
    unitOf ((lensPair (mobiusSphereParam w κ)).2 -
      (lensPair (mobiusSphereParam w κ)).1) = κ := by
  change unitOf ((lensPair (lensPair.symm _)).2 - (lensPair (lensPair.symm _)).1) = κ
  rw [lensPair.apply_symm_apply]
  change unitOf (((mobiusSphereScale w : ℂ) * κ) * (w + 1) -
    ((mobiusSphereScale w : ℂ) * κ) * (w - 1)) = κ
  rw [show ((mobiusSphereScale w : ℂ) * κ) * (w + 1) -
    ((mobiusSphereScale w : ℂ) * κ) * (w - 1) =
      ((2 * mobiusSphereScale w : ℝ) : ℂ) * κ by push_cast; ring]
  exact unitOf_ofReal_mul (by positivity [mobiusSphereScale_pos w]) κ

theorem mobiusSphereInverse_param (p : ℂ × Circle) :
    mobiusSphereInverse (mobiusSphereParam p.1 p.2) = p :=
  Prod.ext (mobiusSphereParam_annulus p.1 p.2) (mobiusSphereParam_phase p.1 p.2)

theorem mobiusSphereParam_sub_ne_zero (p : ℂ × Circle) :
    (lensPair (mobiusSphereParam p.1 p.2)).2 -
      (lensPair (mobiusSphereParam p.1 p.2)).1 ≠ 0 := by
  change (lensPair (lensPair.symm _)).2 - (lensPair (lensPair.symm _)).1 ≠ 0
  rw [lensPair.apply_symm_apply]
  change (mobiusSphereScale p.1 : ℂ) * p.2 * (p.1 + 1) -
    (mobiusSphereScale p.1 : ℂ) * p.2 * (p.1 - 1) ≠ 0
  rw [show (mobiusSphereScale p.1 : ℂ) * p.2 * (p.1 + 1) -
    (mobiusSphereScale p.1 : ℂ) * p.2 * (p.1 - 1) =
      ((2 * mobiusSphereScale p.1 : ℝ) : ℂ) * p.2 by push_cast; ring]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity [mobiusSphereScale_pos p.1]))
    (Circle.coe_ne_zero p.2)

theorem contMDiffAt_mobiusSphereInverse (p : ℂ × Circle) :
    ContMDiffAt (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞ mobiusSphereInverse
      (mobiusSphereParam p.1 p.2) := by
  have hdiff := mobiusSphereParam_sub_ne_zero p
  have hl : ContMDiff (𝓡 3) 𝓘(ℝ, ℂ × ℂ) ∞
      (fun x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 => lensPair x) :=
    lensPair.contDiff.contMDiff.comp contMDiff_coe_sphere
  have ha : ContDiffAt ℝ ∞ modelAnnulusPoint (lensPair (mobiusSphereParam p.1 p.2)) := by
    change ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => -(q.1 + q.2) / (q.1 - q.2)) _
    have h : ContDiffAt ℝ ∞
        ((fun q : ℂ × ℂ => -(q.1 + q.2)) * (fun q => q.1 - q.2)⁻¹)
        (lensPair (mobiusSphereParam p.1 p.2)) :=
      ((contDiffAt_fst.add contDiffAt_snd).neg).mul
      ((contDiffAt_fst.sub contDiffAt_snd).inv (by intro h; exact hdiff (sub_eq_zero.mpr
        (sub_eq_zero.mp h).symm)))
    convert h using 1
    funext q
    exact div_eq_mul_inv _ _
  have hm : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℂ) ∞
      (fun x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 => modelAnnulusPoint (lensPair x))
      (mobiusSphereParam p.1 p.2) :=
    ha.contMDiffAt.comp (f := fun x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 => lensPair x)
      (mobiusSphereParam p.1 p.2) hl.contMDiffAt
  have hs : ContMDiff (𝓡 3) 𝓘(ℝ, ℂ) ∞
      (fun x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 => (lensPair x).2 - (lensPair x).1) :=
    (contDiff_snd.sub contDiff_fst).contMDiff.comp hl
  have hk := (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hdiff)).comp
    (mobiusSphereParam p.1 p.2) hs.contMDiffAt
  exact hm.prodMk hk

theorem mobiusSphereParam_derivative_injective (p : ℂ × Circle) :
    Function.Injective (mfderiv (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
      (fun q : ℂ × Circle => mobiusSphereParam q.1 q.2) p) := by
  have hg := (contMDiffAt_mobiusSphereInverse p).mdifferentiableAt (by norm_num)
  have hf := contMDiff_mobiusSphereParam.mdifferentiable (by norm_num) p
  have he : mobiusSphereInverse ∘ (fun q : ℂ × Circle => mobiusSphereParam q.1 q.2) = id :=
    funext mobiusSphereInverse_param
  have hc := mfderiv_comp p hg hf
  rw [he, mfderiv_id] at hc
  intro v w hvw
  have h := congrArg (fun L => L v) hc
  have h' := congrArg (fun L => L w) hc
  change v = mfderiv (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) mobiusSphereInverse
    (mobiusSphereParam p.1 p.2) (mfderiv (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
      (fun q : ℂ × Circle => mobiusSphereParam q.1 q.2) p v) at h
  change w = mfderiv (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) mobiusSphereInverse
    (mobiusSphereParam p.1 p.2) (mfderiv (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
      (fun q : ℂ × Circle => mobiusSphereParam q.1 q.2) p w) at h' 
  simpa only [ContinuousLinearMap.id_apply] using h.trans ((congrArg _ hvw).trans h'.symm)

theorem isLocalDiffeomorph_mobiusSphereParam :
    IsLocalDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞
      (fun p : ℂ × Circle => mobiusSphereParam p.1 p.2) :=
  DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    contMDiff_mobiusSphereParam mobiusSphereParam_derivative_injective (by simp)

theorem mobiusRegularDeck_involutive : Function.Involutive mobiusRegularDeck := by
  intro p
  apply Prod.ext
  · exact Prod.ext (neg_neg _) (unitInterval.symm_symm _)
  · exact inv_inv _

theorem continuous_mobiusRegularDeck : Continuous mobiusRegularDeck :=
  (continuous_fst.fst.neg.prodMk (unitInterval.continuous_symm.comp continuous_fst.snd)).prodMk
    continuous_snd.inv

theorem mobiusRegularDeck_ne_self (p : (Circle × unitInterval) × Circle) :
    mobiusRegularDeck p ≠ p := by
  intro h
  have hz := congrArg (fun q : (Circle × unitInterval) × Circle => (q.1.1 : ℂ)) h
  change -(p.1.1 : ℂ) = (p.1.1 : ℂ) at hz
  apply Circle.coe_ne_zero p.1.1
  linear_combination (-1 / 2 : ℂ) * hz

theorem mobiusRegularTotalCover_preimage_image (s : Set ((Circle × unitInterval) × Circle)) :
    mobiusRegularTotalCover.{u} ⁻¹' (mobiusRegularTotalCover.{u} '' s) =
      s ∪ mobiusRegularDeck ⁻¹' s := by
  ext p
  constructor
  · rintro ⟨q, hq, he⟩
    rcases (mobiusRegularTotalCover_eq_iff q p).mp he with hp | hp
    · exact Or.inl (hp ▸ hq)
    · exact Or.inr (by
        change mobiusRegularDeck p ∈ s
        rw [hp, mobiusRegularDeck_involutive]
        exact hq)
  · rintro (hp | hp)
    · exact ⟨p, hp, rfl⟩
    · exact ⟨mobiusRegularDeck p, hp,
        ((mobiusRegularTotalCover_eq_iff p (mobiusRegularDeck p)).mpr (Or.inr rfl)).symm⟩

theorem isOpenMap_mobiusRegularTotalCover : IsOpenMap mobiusRegularTotalCover.{u} := by
  have hc := contMDiff_mobiusRegularTotalCover.continuous
  have hq := hc.isClosedMap.isQuotientMap hc mobiusRegularTotalCover_surjective
  intro s hs
  apply hq.isOpen_preimage.mp
  rw [mobiusRegularTotalCover_preimage_image]
  exact hs.union (hs.preimage continuous_mobiusRegularDeck)

theorem isLocalHomeomorph_mobiusRegularTotalCover :
    IsLocalHomeomorph mobiusRegularTotalCover.{u} := by
  intro p
  obtain ⟨A, B, hA, hB, hpA, hpB, hAB⟩ :=
    t2_separation (mobiusRegularDeck_ne_self p).symm
  let S := A ∩ mobiusRegularDeck ⁻¹' B
  have hS : IsOpen S := hA.inter (hB.preimage continuous_mobiusRegularDeck)
  have hpS : p ∈ S := ⟨hpA, hpB⟩
  have hinj : Set.InjOn mobiusRegularTotalCover.{u} S := by
    intro a ha b hb he
    rcases (mobiusRegularTotalCover_eq_iff a b).mp he with hab | hab
    · exact hab.symm
    · exact (Set.disjoint_left.mp hAB hb.1 (hab.symm ▸ ha.2)).elim
  let e := hinj.toPartialEquiv mobiusRegularTotalCover.{u} S
  let Φ := OpenPartialHomeomorph.ofContinuousOpen e
    contMDiff_mobiusRegularTotalCover.continuous.continuousOn
    isOpenMap_mobiusRegularTotalCover hS
  exact ⟨Φ, hpS, rfl⟩

def mobiusRegularInverse (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    (Circle × unitInterval) × Circle :=
  ((unitOf ((lensPair x).1 ^ 2 - (lensPair x).2 ^ 2),
    Set.projIcc 0 1 zero_le_one ((mobiusRegularHeight (modelAnnulusPoint (lensPair x)) + 1) / 2)),
      unitOf (modelAnnulusPoint (lensPair x)))

theorem mobiusRegularInverse_height_bound (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (hq : bundleQuartic (lensPair x) ≤ 0) :
    (mobiusRegularHeight (modelAnnulusPoint (lensPair x)) + 1) / 2 ∈ Icc (0 : ℝ) 1 := by
  have hd := sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero x) hq
  obtain ⟨hm, hp⟩ := sub_ne_zero_of_sq_sub_sq_ne_zero hd
  have hw : modelAnnulusPoint (lensPair x) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hp) hm
  have hJ : ‖joukowski (modelAnnulusPoint (lensPair x))‖ ≤ 3 := by
    rw [joukowski_modelAnnulusPoint hd]
    exact (bundleQuartic_nonpos_iff hd).mp hq
  have hy := (mobiusRegularHeight_mem_iff hw).mp hJ
  have ha := (sq_le_one_iff_abs_le_one _).mp hy
  rw [abs_le] at ha
  constructor <;> linarith [ha.1, ha.2]

theorem mobiusRegularInverse_model (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (hq : bundleQuartic (lensPair x) ≤ 0) :
    mobiusRegularModel (mobiusRegularInverse x) = modelPoint (lensPair x) := by
  have hd := sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero x) hq
  obtain ⟨hm, hp⟩ := sub_ne_zero_of_sq_sub_sq_ne_zero hd
  have hw : modelAnnulusPoint (lensPair x) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hp) hm
  apply Prod.ext
  · change (unitOf ((lensPair x).1 ^ 2 - (lensPair x).2 ^ 2) : ℂ) =
      modelFibrePoint (lensPair x)
    rw [coe_unitOf hd]
    simp [modelFibrePoint, div_eq_mul_inv, mul_comm]
  · change mobiusRegularAnnulusPoint (unitOf (modelAnnulusPoint (lensPair x)))
      (2 * (Set.projIcc 0 1 zero_le_one
        ((mobiusRegularHeight (modelAnnulusPoint (lensPair x)) + 1) / 2) : ℝ) - 1) = _
    rw [Set.projIcc_of_mem zero_le_one (mobiusRegularInverse_height_bound x hq)]
    rw [show 2 * ((mobiusRegularHeight (modelAnnulusPoint (lensPair x)) + 1) / 2) - 1 =
      mobiusRegularHeight (modelAnnulusPoint (lensPair x)) by ring]
    exact mobiusRegularAnnulusPoint_height hw

theorem mobiusRegularInverse_sphere (p : (Circle × unitInterval) × Circle) :
    mobiusRegularInverse (mobiusRegularSphere p) = p :=
  mobiusRegularModel_injective ((mobiusRegularInverse_model _
    (mobiusRegularSphere_quartic p)).trans (mobiusRegularSphere_model p))

theorem mobiusRegularTotalCover_inverse_val (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (hq : bundleQuartic (lensPair x) ≤ 0) :
    (mobiusRegularTotalCover.{u} (mobiusRegularInverse x)).val =
      lensUp (mobiusLensGroup.projection x) := by
  apply congrArg lensUp
  apply (projection_eq_iff_modelPoint _ _ (mobiusRegularSphere_quartic _) hq).mpr
  exact Or.inl ((mobiusRegularInverse_model x hq).symm.trans
    (mobiusRegularSphere_model _).symm)

section InverseSmooth

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiff_mobiusAnnulusPoint_comp
    (f : M → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) (hf : ContMDiff I (𝓡 3) ∞ f)
    (hq : ∀ x, bundleQuartic (lensPair (f x)) ≤ 0) :
    ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun x => modelAnnulusPoint (lensPair (f x))) := by
  have hl : ContMDiff I 𝓘(ℝ, ℂ × ℂ) ∞ (fun x => lensPair (f x)) :=
    lensPair.contDiff.contMDiff.comp (contMDiff_coe_sphere.comp hf)
  intro x
  have hd := sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero (f x)) (hq x)
  have hsub := (sub_ne_zero_of_sq_sub_sq_ne_zero hd).1
  have ha : ContDiffAt ℝ ∞ modelAnnulusPoint (lensPair (f x)) := by
    have h : ContDiffAt ℝ ∞
        ((fun q : ℂ × ℂ => -(q.1 + q.2)) * (fun q => q.1 - q.2)⁻¹) (lensPair (f x)) :=
      ((contDiffAt_fst.add contDiffAt_snd).neg).mul
        ((contDiffAt_fst.sub contDiffAt_snd).inv hsub)
    convert h using 1
    funext q
    exact div_eq_mul_inv _ _
  exact ha.contMDiffAt.comp (f := fun y => lensPair (f y)) x hl.contMDiffAt

theorem contMDiff_mobiusRegularInverse_comp
    (f : M → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) (hf : ContMDiff I (𝓡 3) ∞ f)
    (hq : ∀ x, bundleQuartic (lensPair (f x)) ≤ 0) :
    ContMDiff I (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) ∞ (fun x => mobiusRegularInverse (f x)) := by
  have hl : ContMDiff I 𝓘(ℝ, ℂ × ℂ) ∞ (fun x => lensPair (f x)) :=
    lensPair.contDiff.contMDiff.comp (contMDiff_coe_sphere.comp hf)
  have hd (x : M) := sq_sub_sq_ne_zero_of_bundleQuartic_nonpos
    (lensPair_ne_zero (f x)) (hq x)
  have hw (x : M) : modelAnnulusPoint (lensPair (f x)) ≠ 0 := by
    obtain ⟨hm, hp⟩ := sub_ne_zero_of_sq_sub_sq_ne_zero (hd x)
    exact div_ne_zero (neg_ne_zero.mpr hp) hm
  have hu := contMDiff_mobiusAnnulusPoint_comp f hf hq
  have hv : ContMDiff I (𝓡 1) ∞ (fun x => unitOf (modelAnnulusPoint (lensPair (f x)))) :=
    contMDiffOn_unitOf.comp_contMDiff hu hw
  have hh : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => mobiusRegularHeight (modelAnnulusPoint (lensPair (f x)))) := by
    intro x
    exact (contMDiffAt_mobiusRegularHeight (hw x)).comp x hu.contMDiffAt
  have ht : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => (mobiusRegularHeight (modelAnnulusPoint (lensPair (f x))) + 1) / 2) :=
    (hh.add contMDiff_const).div₀ contMDiff_const (fun x => by norm_num)
  have hi : ContMDiff I (𝓡∂ 1) ∞
      (fun x => (mobiusRegularInverse (f x)).1.2) := by
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    refine ⟨(continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).comp
      ht.continuous, ?_⟩
    convert ht using 1
    funext x
    exact congrArg Subtype.val
      (Set.projIcc_of_mem zero_le_one (mobiusRegularInverse_height_bound (f x) (hq x)))
  have hz : ContMDiff I (𝓡 1) ∞
      (fun x => unitOf ((lensPair (f x)).1 ^ 2 - (lensPair (f x)).2 ^ 2)) := by
    have hp : ContMDiff I 𝓘(ℝ, ℂ) ∞
        (fun x => (lensPair (f x)).1 ^ 2 - (lensPair (f x)).2 ^ 2) :=
      ((contDiff_fst.pow 2).sub (contDiff_snd.pow 2)).contMDiff.comp hl
    exact contMDiffOn_unitOf.comp_contMDiff hp hd
  exact (hz.prodMk hi).prodMk hv

end InverseSmooth

theorem contMDiffAt_mobiusRegularCover_inverse
    (φ : OpenPartialHomeomorph ((Circle × unitInterval) × Circle)
      mobiusBundleCarrier.{u}.Carrier)
    (hφ : (φ : ((Circle × unitInterval) × Circle) → mobiusBundleCarrier.{u}.Carrier) =
      mobiusRegularTotalCover.{u})
    (a : mobiusBundleCarrier.{u}.Carrier) (ha : a ∈ φ.target) :
    ContMDiffAt mobiusBundleCarrier.{u}.model (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) ∞ φ.symm a := by
  let : ChartedSpace (EuclideanHalfSpace 3) mobiusBundleCarrier.{u}.Carrier :=
    inferInstanceAs (ChartedSpace (EuclideanHalfSpace 3) mobiusBundleSet.{u})
  let p := φ.symm a
  have hp : mobiusRegularTotalCover.{u} p = a := by
    rw [← hφ]
    exact φ.right_inv ha
  let hLens := mobiusLensGroup.projection_isLocalDiffeomorph (mobiusRegularSphere p)
  let γ := hLens.localInverse
  let V : TopologicalSpace.Opens mobiusBundleCarrier.{u}.Carrier :=
    ⟨(fun q => lensDown q.val) ⁻¹' γ.source,
      γ.open_source.preimage (contMDiff_lensDown.continuous.comp continuous_subtype_val)⟩
  let r : mobiusBundleCarrier.{u}.Carrier → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
    fun q => γ (lensDown q.val)
  let R : mobiusBundleCarrier.{u}.Carrier → (Circle × unitInterval) × Circle :=
    fun q => mobiusRegularInverse (r q)
  have he : lensDown a.val = mobiusLensGroup.projection (mobiusRegularSphere p) := by
    rw [← hp]
    rfl
  have haV : a ∈ V := by
    change lensDown a.val ∈ γ.source
    rw [he]
    exact hLens.localInverse_mem_source
  have hRa : R a = p := by
    change mobiusRegularInverse (γ (lensDown a.val)) = p
    rw [he, hLens.localInverse_left_inv hLens.localInverse_mem_target]
    exact mobiusRegularInverse_sphere p
  have hr : ContMDiff mobiusBundleCarrier.{u}.model (𝓡 3) ∞ (fun q : V => r q.val) := by
    change ContMDiff (𝓡∂ 3) (𝓡 3) ∞ (fun q : V => r q.val)
    exact γ.contMDiffOn_toFun.comp_contMDiff
      (contMDiff_lensDown.comp (mobiusBundleAtlas.contMDiff_subtype_val.comp
        contMDiff_subtype_val)) (fun q => q.property)
  have hq (q : V) : bundleQuartic (lensPair (r q.val)) ≤ 0 := by
    have hg : mobiusLensGroup.projection (r q.val) = lensDown q.val.val :=
      hLens.localInverse_right_inv q.property
    have h := q.val.property
    change lensDescend bundleQuartic bundleQuartic_invariant (lensDown q.val.val) ≤ 0 at h
    rw [← hg] at h
    exact h
  have hR : ContMDiff mobiusBundleCarrier.{u}.model
      (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) ∞ (fun q : V => R q.val) :=
    contMDiff_mobiusRegularInverse_comp _ hr hq
  have hAtR : ContMDiffAt mobiusBundleCarrier.{u}.model
      (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) ∞ R a :=
    contMDiffAt_subtype_iff.mp (hR ⟨a, haV⟩)
  have hright (q : V) : mobiusRegularTotalCover.{u} (R q.val) = q.val := by
    apply Subtype.ext
    rw [mobiusRegularTotalCover_inverse_val _ (hq q),
      hLens.localInverse_right_inv q.property, lensUp_lensDown]
  have hpφ : p ∈ φ.source := φ.map_target ha
  have hnear : ∀ᶠ q in nhds a, R q ∈ φ.source :=
    hAtR.continuousAt.preimage_mem_nhds (hRa ▸ φ.open_source.mem_nhds hpφ)
  apply hAtR.congr_of_eventuallyEq
  filter_upwards [V.isOpen.mem_nhds haV, φ.open_target.mem_nhds ha, hnear] with q hqV hqt hqs
  symm
  apply φ.injOn hqs (φ.map_target hqt)
  rw [hφ, hright ⟨q, hqV⟩, ← hφ, φ.right_inv hqt]

theorem isLocalDiffeomorph_mobiusRegularTotalCover :
    IsLocalDiffeomorph (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) mobiusBundleCarrier.{u}.model ∞
      mobiusRegularTotalCover.{u} := by
  intro p
  obtain ⟨φ, hpφ, hφ⟩ := isLocalHomeomorph_mobiusRegularTotalCover p
  have hf : ContMDiffOn (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) mobiusBundleCarrier.{u}.model ∞
      φ φ.source := by
    rw [← hφ]
    exact contMDiff_mobiusRegularTotalCover.contMDiffOn
  have hg : ContMDiffOn mobiusBundleCarrier.{u}.model (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) ∞
      φ.symm φ.target :=
    fun a ha => (contMDiffAt_mobiusRegularCover_inverse φ hφ.symm a ha).contMDiffWithinAt
  have hl := DifferentialGeometry.OpenPartialHomeomorph.isLocalDiffeomorphAt_of_contMDiffOn
    hf hg hpφ
  rw [← hφ] at hl
  exact hl

theorem exists_mobiusWholeCircleFibration :
    Nonempty (CircleFibration mobiusBundleCarrier.{u} ⊤) := by
  exact ⟨(exists_circleFibration_of_mobiusCover mobiusBundleCarrier.{u} mobiusRegularTotalCover
    isLocalDiffeomorph_mobiusRegularTotalCover mobiusRegularTotalCover_surjective
    mobiusRegularTotalCover_eq_iff).choose⟩

theorem exists_twistedIBundle_singlePieceRaw :
    ∃ G : RawGraphPresentation mobiusBundleCarrier.{u},
      G.components.count = 1 ∧ G.pairing.count = 0 ∧ G.externalCount = 1 := by
  let : ConnectedSpace mobiusBundleCarrier.{u}.Carrier :=
    mobiusRegularTotalCover_surjective.connectedSpace contMDiff_mobiusRegularTotalCover.continuous
  obtain ⟨F⟩ := exists_mobiusWholeCircleFibration.{u}
  let G := singlePieceRawPresentation mobiusBundleCarrier.{u} F
    mobiusPresentation.external mobiusPresentation.external_exhausted
  exact ⟨G, rfl, rfl, rfl⟩

end GC.GraphManifold

import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialEdgeLink
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopBundle

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial
local instance carrierCharts_CircleX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance
local instance carrierSmooth_CircleX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

def radialLoopCoordinateSupply : PartialDiffeomorph ((𝓡 2).prod (𝓡 1)) (𝓡 3)
    (EuclideanSpace ℝ (Fin 2) × Circle) SphereCarrier.{0} ∞ := loopCircleCoordinates

def radialLoopBundleSupply : loopCircleDomain
    ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ (loopCircleBase × Circle) := loopCircleBundle

theorem radialLoop_inverse_height (q : loopCircleBase × Circle) :
    cliffordHeight (radialLoopBundleSupply.symm q).val = 1 - 2 * ‖q.1.val‖ ^ 2 := by
  have hv : (radialLoopBundleSupply.symm q).val =
      radialLoopCoordinateSupply (q.1.val, q.2) := rfl
  have hs : sphereSecond (radialLoopCoordinateSupply (q.1.val, q.2)) =
      modelPlaneComplex q.1.val := loopCircleCoordinates_second q.1.property
  have hh := norm_sphereSecond_sq_eq (radialLoopBundleSupply.symm q).val
  rw [hv, hs, modelPlaneComplex.norm_map] at hh
  rw [hv]
  linarith

theorem radialLoop_height (p : loopCircleDomain) :
    cliffordHeight p.val = 1 - 2 * ‖(radialLoopBundleSupply p).1.val‖ ^ 2 := by
  have hh := radialLoop_inverse_height (radialLoopBundleSupply p)
  rw [radialLoopBundleSupply.symm_apply_apply] at hh
  exact hh

def radialCircleBase : TopologicalSpace.Opens loopCircleBase :=
  ⟨{z | (1 / 2 : ℝ) < ‖z.val‖ ^ 2},
    isOpen_lt continuous_const ((continuous_norm.comp continuous_subtype_val).pow 2)⟩

def radialCircleDomain : TopologicalSpace.Opens carrier.Carrier :=
  ⟨{p | -1 < height p ∧ height p < 0},
    (isOpen_lt continuous_const height_continuous).inter
      (isOpen_lt height_continuous continuous_const)⟩

def radialCircleToLoop (p : radialCircleDomain) : loopCircleDomain :=
  ⟨p.val.val, by
    intro hz
    have hh := norm_sphereFirst_sq_eq p.val.val
    rw [hz, norm_zero, zero_pow (by decide)] at hh
    have hlo : -1 < cliffordHeight p.val.val := p.property.1
    linarith⟩

theorem radialCircleToLoop_smooth :
    ContMDiff (𝓡∂ 3) (𝓡 3) ∞ radialCircleToLoop :=
  (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
    loopCircleDomain radialCircleToLoop).mp
      (contMDiff_solidTorus_val.comp contMDiff_subtype_val)

def radialCircleForward (p : radialCircleDomain) : radialCircleBase × Circle :=
  (⟨(radialLoopBundleSupply (radialCircleToLoop p)).1, by
      have hh := radialLoop_height (radialCircleToLoop p)
      have hn : cliffordHeight p.val.val < 0 := p.property.2
      change (1 / 2 : ℝ) < ‖(radialLoopBundleSupply (radialCircleToLoop p)).1.val‖ ^ 2
      change cliffordHeight p.val.val = _ at hh
      linarith⟩,
    (radialLoopBundleSupply (radialCircleToLoop p)).2)

def radialCircleInverseSphere (q : radialCircleBase × Circle) : radialSphereInterior :=
  ⟨(radialLoopBundleSupply.symm (q.1.val, q.2)).val, by
    change cliffordHeight (radialLoopBundleSupply.symm (q.1.val, q.2)).val < 0
    rw [radialLoop_inverse_height]
    have hq : (1 / 2 : ℝ) < ‖q.1.val.val‖ ^ 2 := q.1.property
    linarith⟩

def radialCircleBackward (q : radialCircleBase × Circle) : radialCircleDomain :=
  ⟨sphereInteriorToCarrier (radialCircleInverseSphere q), by
    change -1 < cliffordHeight (radialLoopBundleSupply.symm (q.1.val, q.2)).val ∧
      cliffordHeight (radialLoopBundleSupply.symm (q.1.val, q.2)).val < 0
    rw [radialLoop_inverse_height]
    have hl : ‖q.1.val.val‖ < 1 := q.1.val.property
    have hn : (1 / 2 : ℝ) < ‖q.1.val.val‖ ^ 2 := q.1.property
    constructor <;> nlinarith [norm_nonneg q.1.val.val]⟩

theorem radialCircleForward_smooth :
    ContMDiff (𝓡∂ 3) ((𝓡 2).prod (𝓡 1)) ∞ radialCircleForward := by
  have hc := radialLoopBundleSupply.contMDiff.comp radialCircleToLoop_smooth
  have hf : ContMDiff (𝓡∂ 3) (𝓡 2) ∞ (fun p => (radialCircleForward p).1) :=
    (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
      radialCircleBase (fun p => (radialCircleForward p).1)).mp hc.fst
  exact hf.prodMk hc.snd

theorem radialCircleInverseSphere_smooth :
    ContMDiff ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ radialCircleInverseSphere := by
  have hi : ContMDiff ((𝓡 2).prod (𝓡 1)) ((𝓡 2).prod (𝓡 1)) ∞
      (fun q : radialCircleBase × Circle => (q.1.val, q.2)) :=
    (contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd
  have hv : ContMDiff (𝓡 3) (𝓡 3) ∞
      (Subtype.val : loopCircleDomain → SphereCarrier.{0}) := contMDiff_subtype_val
  have hh := hv.comp (radialLoopBundleSupply.symm.contMDiff.comp hi)
  exact (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
    radialSphereInterior radialCircleInverseSphere).mp hh

theorem radialCircleBackward_smooth :
    ContMDiff ((𝓡 2).prod (𝓡 1)) (𝓡∂ 3) ∞ radialCircleBackward :=
  (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
    radialCircleDomain radialCircleBackward).mp
      (sphereInteriorToCarrier_smooth.comp radialCircleInverseSphere_smooth)

def radialCircleProduct : radialCircleDomain
    ≃ₘ⟮𝓡∂ 3, (𝓡 2).prod (𝓡 1)⟯ (radialCircleBase × Circle) where
  toFun := radialCircleForward
  invFun := radialCircleBackward
  left_inv := by
    intro p
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (Subtype.val : loopCircleDomain → SphereCarrier.{0})
      (radialLoopBundleSupply.symm_apply_apply (radialCircleToLoop p))
  right_inv := by
    intro q
    have hh := radialLoopBundleSupply.apply_symm_apply (q.1.val, q.2)
    have he : radialCircleToLoop (radialCircleBackward q) =
        radialLoopBundleSupply.symm (q.1.val, q.2) := Subtype.ext rfl
    apply Prod.ext
    · apply Subtype.ext
      change (radialLoopBundleSupply (radialCircleToLoop (radialCircleBackward q))).1 = q.1.val
      rw [he]
      exact congrArg Prod.fst hh
    · change (radialLoopBundleSupply (radialCircleToLoop (radialCircleBackward q))).2 = q.2
      rw [he]
      exact congrArg Prod.snd hh
  contMDiff_toFun := radialCircleForward_smooth
  contMDiff_invFun := radialCircleBackward_smooth

def radialCircleProjection : C(radialCircleDomain, radialCircleBase) :=
  ⟨fun p => (radialCircleProduct p).1, radialCircleProduct.continuous.fst⟩

theorem radialCircleProjection_smooth :
    ContMDiff (𝓡∂ 3) (𝓡 2) ∞ radialCircleProjection := radialCircleProduct.contMDiff.fst

theorem radialCircleProjection_onto (p : radialCircleDomain) :
    Surjective (mfderiv (𝓡∂ 3) (𝓡 2) radialCircleProjection p) := by
  have hd := (radialCircleProduct.mfderivToContinuousLinearEquiv (by simp) p).surjective
  have hc := mfderiv_comp (g := fun q : radialCircleBase × Circle => q.1)
    (f := radialCircleProduct) p mdifferentiableAt_fst
    (radialCircleProduct.contMDiff.mdifferentiableAt (by simp))
  change mfderiv (𝓡∂ 3) (𝓡 2) radialCircleProjection p = _ at hc
  rw [mfderiv_fst] at hc
  intro v
  obtain ⟨w, hw⟩ := hd (v, (0 : TangentSpace (𝓡 1) (radialCircleProduct p).2))
  refine ⟨w, ?_⟩
  rw [hc]
  exact congrArg Prod.fst hw

theorem radialCircleProjection_height (p : radialCircleDomain) :
    height p.val = 1 - 2 * ‖(radialCircleProjection p).val.val‖ ^ 2 :=
  radialLoop_height (radialCircleToLoop p)

theorem radialCircleProjection_complex (p : radialCircleDomain) :
    modelPlaneComplex (radialCircleProjection p).val.val = sphereSecond p.val.val :=
  modelPlaneComplex.apply_symm_apply _

theorem radialCircleProduct_meridian (p : radialCircleDomain) :
    (radialCircleProduct p).2 = unitOf (sphereFirst p.val.val) := rfl

end GC.GraphManifold.Assembly.FC39P0.X135Radial

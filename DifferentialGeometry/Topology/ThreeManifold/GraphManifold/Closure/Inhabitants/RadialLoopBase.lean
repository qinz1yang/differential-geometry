import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialSeamFaceLink

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial
local instance carrierCharts_LoopBaseX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance
local instance carrierSmooth_LoopBaseX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

def radialLoopSeam (c : Circle) : radialNegativeSeam :=
  ⟨((1, c), -(1 / 2 : ℝ)), by constructor <;> norm_num⟩

theorem radialLoopSeam_smooth : ContMDiff (𝓡 1) signedCollarModel ∞ radialLoopSeam := by
  apply (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
    radialNegativeSeam radialLoopSeam).mp
  exact (contMDiff_const.prodMk contMDiff_id).prodMk contMDiff_const

def radialLoopCarrier (c : Circle) : carrier.Carrier :=
  negativeSeamToCarrier (radialLoopSeam c)

theorem radialLoopCarrier_height (c : Circle) : height (radialLoopCarrier c) =
    -(1 / 2 : ℝ) := height_negativeSeam _

def radialLoopPoint (c : Circle) : radialCircleDomain :=
  ⟨radialLoopCarrier c, by
    change -1 < height (radialLoopCarrier c) ∧ height (radialLoopCarrier c) < 0
    rw [radialLoopCarrier_height]
    norm_num⟩

theorem radialLoopPoint_smooth : ContMDiff (𝓡 1) (𝓡∂ 3) ∞ radialLoopPoint := by
  apply (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
    radialCircleDomain radialLoopPoint).mp
  exact negativeSeamToCarrier_smooth.comp radialLoopSeam_smooth

def radialLoopBase (c : Circle) : radialCircleBase := radialCircleProjection (radialLoopPoint c)

theorem radialLoopBase_smooth : ContMDiff (𝓡 1) (𝓡 2) ∞ radialLoopBase :=
  radialCircleProjection_smooth.comp radialLoopPoint_smooth

theorem radialLoopBase_norm (c : Circle) : ‖(radialLoopBase c).val.val‖ ^ 2 = (3 / 4 : ℝ) := by
  have hh := radialCircleProjection_height (radialLoopPoint c)
  change height (radialLoopCarrier c) = 1 - 2 * ‖(radialLoopBase c).val.val‖ ^ 2 at hh
  rw [radialLoopCarrier_height] at hh
  linarith

theorem radialLoopBase_complex (c : Circle) :
    modelPlaneComplex (radialLoopBase c).val.val = seamSecond (-(1 / 2 : ℝ)) • (c : ℂ) := by
  rw [radialLoopBase, radialCircleProjection_complex]
  change sphereSecond (cliffordSeamMap ((1, c), -(1 / 2 : ℝ))) = _
  exact sphereSecond_cliffordSeamMap _

theorem radialLoopBase_cbase (c : Circle) : radialLoopBase c ∈ radialCircleBundle.cbase := by
  change (3 / 4 : ℝ) ≤ ‖(radialLoopBase c).val.val‖ ^ 2 ∧
    ‖(radialLoopBase c).val.val‖ ^ 2 ≤ (7 / 8 : ℝ)
  rw [radialLoopBase_norm]
  norm_num

theorem radialLoopBase_defining (c : Circle) : radialCircleDefining (0 : Fin 2)
    (radialLoopBase c) = 0 := by
  change (3 / 4 : ℝ) - ‖(radialLoopBase c).val.val‖ ^ 2 = 0
  rw [radialLoopBase_norm]
  ring

end GC.GraphManifold.Assembly.FC39P0.X135Radial

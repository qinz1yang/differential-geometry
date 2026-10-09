import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialPiecePartition

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial
local instance carrierCharts_RimBaseX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance
local instance carrierSmooth_RimBaseX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

def radialRimSeam (c : Circle) : radialNegativeSeam :=
  ⟨((1, c), -(3 / 4 : ℝ)), by constructor <;> norm_num⟩

theorem radialRimSeam_smooth : ContMDiff (𝓡 1) signedCollarModel ∞ radialRimSeam := by
  apply (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
    radialNegativeSeam radialRimSeam).mp
  exact (contMDiff_const.prodMk contMDiff_id).prodMk contMDiff_const

def radialRimCarrier (c : Circle) : carrier.Carrier :=
  negativeSeamToCarrier (radialRimSeam c)

theorem radialRimCarrier_height (c : Circle) : height (radialRimCarrier c) =
    -(3 / 4 : ℝ) := height_negativeSeam _

def radialRimPoint (c : Circle) : radialCircleDomain :=
  ⟨radialRimCarrier c, by
    change -1 < height (radialRimCarrier c) ∧ height (radialRimCarrier c) < 0
    rw [radialRimCarrier_height]
    norm_num⟩

theorem radialRimPoint_smooth : ContMDiff (𝓡 1) (𝓡∂ 3) ∞ radialRimPoint := by
  apply (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
    radialCircleDomain radialRimPoint).mp
  exact negativeSeamToCarrier_smooth.comp radialRimSeam_smooth

def radialRimBase (c : Circle) : radialCircleBase := radialCircleProjection (radialRimPoint c)

theorem radialRimBase_smooth : ContMDiff (𝓡 1) (𝓡 2) ∞ radialRimBase :=
  radialCircleProjection_smooth.comp radialRimPoint_smooth

theorem radialRimBase_norm (c : Circle) : ‖(radialRimBase c).val.val‖ ^ 2 = (7 / 8 : ℝ) := by
  have hh := radialCircleProjection_height (radialRimPoint c)
  change height (radialRimCarrier c) = 1 - 2 * ‖(radialRimBase c).val.val‖ ^ 2 at hh
  rw [radialRimCarrier_height] at hh
  linarith

theorem radialRimBase_complex (c : Circle) :
    modelPlaneComplex (radialRimBase c).val.val = seamSecond (-(3 / 4 : ℝ)) • (c : ℂ) := by
  rw [radialRimBase, radialCircleProjection_complex]
  change sphereSecond (cliffordSeamMap ((1, c), -(3 / 4 : ℝ))) = _
  exact sphereSecond_cliffordSeamMap _

theorem radialRimBase_cbase (c : Circle) : radialRimBase c ∈ radialCircleBundle.cbase := by
  change (3 / 4 : ℝ) ≤ ‖(radialRimBase c).val.val‖ ^ 2 ∧
    ‖(radialRimBase c).val.val‖ ^ 2 ≤ (7 / 8 : ℝ)
  rw [radialRimBase_norm]
  norm_num

theorem radial_projection_rim_iff {p : radialCircleDomain} {c : Circle} :
    radialCircleProjection p = radialRimBase c ↔
      height p.val = -(3 / 4 : ℝ) ∧ edgeLongitude p.val = c := by
  constructor
  · intro hp
    have hh := radialCircleProjection_height p
    rw [hp, radialRimBase_norm] at hh
    have ht : height p.val = -(3 / 4 : ℝ) := by linarith
    refine ⟨ht, ?_⟩
    change unitOf (sphereSecond p.val.val) = c
    have hz := radialCircleProjection_complex p
    rw [hp, radialRimBase_complex] at hz
    rw [← hz]
    exact unitOf_smul (seamSecond_pos (by norm_num)) _
  · rintro ⟨ht, hc⟩
    have hmem : p.val.val ∈ cliffordSeamTarget :=
      ⟨(radialCircleToLoop p).property, sphereSecond_ne_zero_of_mem p.val.property⟩
    have hn := seamSecond_cliffordHeight hmem
    change seamSecond (height p.val) = ‖sphereSecond p.val.val‖ at hn
    rw [ht] at hn
    apply Subtype.ext
    apply Subtype.ext
    apply modelPlaneComplex.injective
    rw [radialCircleProjection_complex, radialRimBase_complex]
    rw [hn]
    rw [← hc]
    change sphereSecond p.val.val = ‖sphereSecond p.val.val‖ •
      (unitOf (sphereSecond p.val.val) : ℂ)
    exact (norm_smul_unitOf (sphereSecond p.val.val)).symm

theorem radial_rim_fibre (c : Circle) : radialEdgeBundle.rim c =
    radialCircleBundle.fibre (radialRimBase c) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have ht : height q.val = -(3 / 4 : ℝ) := hq.2
    have hc : edgeLongitude q.val = c := hq.1
    have hd : q.val ∈ radialCircleDomain := by
      change -1 < height q.val ∧ height q.val < 0
      rw [ht]
      norm_num
    refine ⟨⟨q.val, hd⟩, ?_, rfl⟩
    exact (radial_projection_rim_iff (p := ⟨q.val, hd⟩) (c := c)).mpr ⟨ht, hc⟩
  · rintro ⟨q, hq, rfl⟩
    have hp : radialCircleProjection q = radialRimBase c := hq
    obtain ⟨ht, hc⟩ := (radial_projection_rim_iff (p := q) (c := c)).mp hp
    have hd : q.val ∈ radialCarrierInterior := by
      change height q.val < 0
      rw [ht]
      norm_num
    exact ⟨⟨q.val, hd⟩, ⟨hc, ht⟩, rfl⟩

theorem radial_vertical_height : radialEdgeBundle.vertical =
    {p : carrier.Carrier | height p = -(3 / 4 : ℝ)} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq.2
  · intro hp
    change height p = -(3 / 4 : ℝ) at hp
    have hn : p ∈ radialCarrierInterior := by
      change height p < 0
      rw [hp]
      norm_num
    exact ⟨⟨p, hn⟩, ⟨mem_univ _, hp⟩, rfl⟩

theorem radial_edge_region : radialEdgeBundle.edgePiece ∩ radialCircleBundle.region =
    radialEdgeBundle.vertical := by
  rw [radial_edge_height, radialCircleBundle_region, radial_vertical_height]
  ext p
  constructor
  · intro hp
    exact le_antisymm hp.1 hp.2.1
  · intro hp
    change height p = -(3 / 4 : ℝ) at hp
    change height p ≤ -(3 / 4 : ℝ) ∧
      -(3 / 4 : ℝ) ≤ height p ∧ height p ≤ -(1 / 2 : ℝ)
    rw [hp]
    norm_num

end GC.GraphManifold.Assembly.FC39P0.X135Radial

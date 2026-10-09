import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialTorusInterior
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialEdgeCircle
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Inclusion
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundarySource
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundary
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.OpenTarget

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

local instance edgeFibreCellCharts_X135 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  Handle.closedCellChartedSpaceSucc 1

local instance edgeFibreCellSmooth_X135 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  Handle.closedCellIsManifold 1

local instance carrierCharts_FibresX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_FibresX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

local instance fibreSourceBoundary_X135 :
    HasSmoothBoundary (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 2) (𝓡∂ 2) := inferInstance

local instance closedFibreCharts_X135 :
    ChartedSpace (EuclideanHalfSpace 3) closedSolidTorusCarrier.Carrier :=
  closedSolidTorusCarrier.charts

local instance closedFibreSmooth_X135 : IsManifold (𝓡∂ 3) ∞
    closedSolidTorusCarrier.Carrier := closedSolidTorusCarrier.smooth

def edgeCoreFibreAt (c : Circle) (x : ClosedCell 2) : radialEdgeSet :=
  radialEdgeFromClosed (closedSolidTorusMeridianDisk c x)

theorem edgeCoreFibreAt_product (c : Circle) (x : ClosedCell 2) :
    edgeCoreFibreAt c x = edgeClosedCellProduct (x, c) := by
  change edgeProductMap (solidTorusDiscCircle
    (solidTorusDiscCircle.symm (GC.Seifert.unitDiscClosedCell.{0}.symm x, c))) =
      edgeProductMap (GC.Seifert.unitDiscClosedCell.{0}.symm x, c)
  rw [solidTorusDiscCircle.apply_symm_apply]

theorem edgeCoreFibreAt_embedding (c : Circle) :
    IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ (edgeCoreFibreAt c) :=
  DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp
    (𝓡∂ 2) (𝓡∂ 3) (closedSolidTorusMeridianDisk c)
    (closedSolidTorusMeridianDisk_isSmoothEmbedding c) radialEdgeFromClosed

theorem edgeCoreFibreAt_height (c : Circle) (x : ClosedCell 2) :
    cliffordHeight (edgeCoreFibreAt c x).val ≤ -(3 / 4 : ℝ) :=
  sub_nonpos.mp (show cliffordHeight (edgeCoreFibreAt c x).val - (-(3 / 4 : ℝ)) ≤ 0
    from (edgeCoreFibreAt c x).property)

def edgeFibreSphereInterior (c : Circle) (x : ClosedCell 2) : radialSphereInterior :=
  ⟨(edgeCoreFibreAt c x).val, (edgeCoreFibreAt_height c x).trans_lt (by norm_num)⟩

theorem edgeFibreSphereInterior_embedding (c : Circle) :
    IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ (edgeFibreSphereInterior c) := by
  apply DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen
    (𝓡∂ 2) (𝓡 3) radialSphereInterior (edgeFibreSphereInterior c)
  exact radialEdgeAtlas.isSmoothEmbedding_subtype_val.comp_of_smoothBoundary
    (edgeCoreFibreAt_embedding c)

def edgeFibreAt (c : Circle) (x : ClosedCell 2) : carrier.Carrier :=
  sphereInteriorToCarrier (edgeFibreSphereInterior c x)

def radialCarrierInterior : TopologicalSpace.Opens carrier.Carrier :=
  ⟨{p | height p < 0}, isOpen_lt height_continuous continuous_const⟩

def sphereToOpenCarrier (p : radialSphereInterior) : radialCarrierInterior :=
  ⟨sphereInteriorToCarrier p, by
    change cliffordHeight p.val < 0
    exact p.property⟩

def openCarrierToSphere (p : radialCarrierInterior) : radialSphereInterior :=
  ⟨p.val.val, by
    change height p.val < 0
    exact p.property⟩

def sphereInteriorOpenCarrier :
    radialSphereInterior ≃ₘ⟮𝓡 3, 𝓡∂ 3⟯ radialCarrierInterior where
  toFun := sphereToOpenCarrier
  invFun := openCarrierToSphere
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl
  contMDiff_toFun :=
    (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
      radialCarrierInterior sphereToOpenCarrier).mp sphereInteriorToCarrier_smooth
  contMDiff_invFun :=
    (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
      radialSphereInterior openCarrierToSphere).mp
        (contMDiff_solidTorus_val.comp contMDiff_subtype_val)

theorem sphereInteriorToCarrier_openEmbedding :
    Topology.IsOpenEmbedding sphereInteriorToCarrier :=
  radialCarrierInterior.isOpen.isOpenEmbedding_subtypeVal.comp
    sphereInteriorOpenCarrier.toHomeomorph.isOpenEmbedding

theorem sphereInteriorToCarrier_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡∂ 3) ∞ sphereInteriorToCarrier := by
  intro p
  change IsLocalDiffeomorphAt (𝓡 3) (𝓡∂ 3) ∞
    ((Subtype.val : radialCarrierInterior → carrier.Carrier) ∘ sphereInteriorOpenCarrier) p
  exact (sphereInteriorOpenCarrier.isLocalDiffeomorph p).comp (𝓡∂ 3) carrier.Carrier
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val radialCarrierInterior
      (sphereInteriorOpenCarrier p))

end GC.GraphManifold.Assembly.FC39P0.X135Radial

import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialTorusEdge
import DifferentialGeometry.Topology.Manifold.ProductSectionEmbedding
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Manifold.BoundaryTangentFlow.CircleRotation

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly.FC39P0
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

local instance edgeCircleCellCharts_X135 :
    ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) := Handle.closedCellChartedSpaceSucc 1

local instance edgeCircleCellSmooth_X135 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  Handle.closedCellIsManifold 1

local instance edgeCircleClosedCharts_X135 :
    ChartedSpace (EuclideanHalfSpace 3) closedSolidTorusCarrier.Carrier :=
  closedSolidTorusCarrier.charts

local instance edgeCircleClosedSmooth_X135 :
    IsManifold (𝓡∂ 3) ∞ closedSolidTorusCarrier.Carrier := closedSolidTorusCarrier.smooth

local instance carrierCharts_EdgeCircleX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_EdgeCircleX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

def radialEdgeProjection (p : radialEdgeSet) : Circle := (edgeProductInverse p).2

theorem radialEdgeProjection_smooth :
    ContMDiff (𝓡∂ 3) (𝓡 1) ∞ radialEdgeProjection := edgeProductInverse_smooth.snd

theorem radialEdgeProjection_onto (p : radialEdgeSet) :
    Surjective (mfderiv (𝓡∂ 3) (𝓡 1) radialEdgeProjection p) := by
  have hd := (edgeProduct.symm.mfderivToContinuousLinearEquiv (by simp) p).surjective
  have hchain := mfderiv_comp (g := fun q : UnitDisc.{0} × Circle => q.2)
    (f := edgeProductInverse) p mdifferentiableAt_snd
    (edgeProductInverse_smooth.mdifferentiableAt (by simp))
  change mfderiv (𝓡∂ 3) (𝓡 1) radialEdgeProjection p = _ at hchain
  rw [mfderiv_snd] at hchain
  intro v
  obtain ⟨w, hw⟩ := hd ((0 : TangentSpace (𝓡∂ 2) (edgeProductInverse p).1), v)
  refine ⟨w, ?_⟩
  rw [hchain]
  change (mfderiv (𝓡∂ 3) ((𝓡∂ 2).prod (𝓡 1)) edgeProductInverse p w).2 = v
  change mfderiv (𝓡∂ 3) ((𝓡∂ 2).prod (𝓡 1)) edgeProductInverse p w = (0, v) at hw
  exact congrArg Prod.snd hw

def radialEdgeFibre (x : ClosedCell 2) : radialEdgeSet := edgeClosedCellProduct (x, 1)

def radialEdgeFromClosed :
    closedSolidTorusCarrier.Carrier ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ radialEdgeSet :=
  GC.Seifert.solidTorusClosedSolidTorus.{0}.symm.trans
    (solidTorusDiscCircle.trans edgeProduct)

theorem radialEdgeFibre_embedding :
    IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ radialEdgeFibre := by
  have he := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp
    (𝓡∂ 2) (𝓡∂ 3) (closedSolidTorusMeridianDisk 1)
    (closedSolidTorusMeridianDisk_isSmoothEmbedding 1) radialEdgeFromClosed
  convert he using 1
  funext x
  change edgeProductMap (GC.Seifert.unitDiscClosedCell.{0}.symm x, 1) =
    edgeProductMap (solidTorusDiscCircle
      (solidTorusDiscCircle.symm (GC.Seifert.unitDiscClosedCell.{0}.symm x, 1)))
  rw [solidTorusDiscCircle.apply_symm_apply]

theorem radialEdgeProjection_product (q : UnitDisc.{0} × Circle) :
    radialEdgeProjection (edgeProductMap q) = q.2 := by
  have hphase := congrArg (fun z : UnitDisc.{0} × Circle => z.2) (edgeProduct_left q)
  exact hphase

theorem radialEdgeFibre_range : range radialEdgeFibre = radialEdgeProjection ⁻¹' {1} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    change radialEdgeProjection
      (edgeProductMap (GC.Seifert.unitDiscClosedCell.{0}.symm x, 1)) = 1
    rw [radialEdgeProjection_product]
  · intro hp
    have hphase : (edgeProductInverse p).2 = 1 := hp
    refine ⟨GC.Seifert.unitDiscClosedCell.{0} (edgeProductInverse p).1, ?_⟩
    change edgeProductMap
      (GC.Seifert.unitDiscClosedCell.{0}.symm
        (GC.Seifert.unitDiscClosedCell.{0} (edgeProductInverse p).1), 1) = p
    rw [GC.Seifert.unitDiscClosedCell.symm_apply_apply, ← hphase]
    exact edgeProduct_right p

theorem radialEdge_boundary_iff {p : radialEdgeSet} :
    (𝓡∂ 3).IsBoundaryPoint p ↔ cliffordHeight p.val = -(3 / 4 : ℝ) := by
  erw [SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff (𝓡 3) (n := 2)
    finrank_euclideanSpace_fin edgeCoreDefiner_smooth 0 edgeCoreDefiner_regular]
  exact sub_eq_zero

theorem radialEdge_height_coordinates (p : radialEdgeSet) :
    cliffordHeight p.val = ‖(edgeProductInverse p).1.down.val‖ ^ 2 / 4 - 1 := by
  have hh := edgeHalfCarrier_height (edgeProductInverse p)
  change cliffordHeight (edgeProductMap (edgeProductInverse p)).val = _ at hh
  rw [edgeProduct_right] at hh
  exact hh

def radialEdgeRotation (p : radialEdgeSet) (t : ℝ) : radialEdgeSet :=
  edgeProductMap ((edgeProductInverse p).1, Circle.exp t * (edgeProductInverse p).2)

theorem radialEdgeRotation_smooth (p : radialEdgeSet) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 3) ∞ (radialEdgeRotation p) :=
  edgeProductMap_smooth.comp
    (contMDiff_const.prodMk (contMDiff_circleExp.mul contMDiff_const))

theorem radialEdgeRotation_zero (p : radialEdgeSet) : radialEdgeRotation p 0 = p := by
  change edgeProductMap ((edgeProductInverse p).1, Circle.exp 0 * (edgeProductInverse p).2) = p
  rw [Circle.exp_zero, one_mul]
  exact edgeProduct_right p

theorem radialEdgeRotation_boundary (p : radialEdgeSet) (hp : (𝓡∂ 3).IsBoundaryPoint p)
    (t : ℝ) : (𝓡∂ 3).IsBoundaryPoint (radialEdgeRotation p t) := by
  apply radialEdge_boundary_iff.mpr
  have hh := radialEdge_boundary_iff.mp hp
  rw [radialEdge_height_coordinates p] at hh
  change height (edgeHalfCarrier
    ((edgeProductInverse p).1, Circle.exp t * (edgeProductInverse p).2)) = _
  rw [edgeHalfCarrier_height]
  exact hh

theorem radialEdgeRotation_projection (p : radialEdgeSet) (t : ℝ) :
    radialEdgeProjection (radialEdgeRotation p t) =
      Circle.exp t * (edgeProductInverse p).2 :=
  radialEdgeProjection_product _

theorem radialEdgeRotation_derivative (p : radialEdgeSet) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (radialEdgeProjection ∘ radialEdgeRotation p) 0 ≠ 0 := by
  have heq : radialEdgeProjection ∘ radialEdgeRotation p =
      (fun t : ℝ => Circle.exp t * (edgeProductInverse p).2) := by
    funext t
    exact radialEdgeRotation_projection p t
  rw [heq]
  intro hzero
  have hrotation := DifferentialGeometry.Manifold.BoundaryTangentFlow.mfderiv_coe_rotation
    (edgeProductInverse p).2
  rw [hzero, zero_apply] at hrotation
  have hcz : (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun w : Circle => (w : ℂ))
      (edgeProductInverse p).2) 0 = 0 := map_zero _
  have hz : ((edgeProductInverse p).2 : ℂ) ≠ 0 := by
    intro hz
    have hn := Circle.norm_coe (edgeProductInverse p).2
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  exact (mul_ne_zero Complex.I_ne_zero hz) (hrotation.symm.trans hcz)

def radialEdgeCircle : Assembly.EdgeCirclePiece carrier where
  piece := radialEdgePiece
  proj := radialEdgeProjection
  proj_smooth := radialEdgeProjection_smooth
  proj_submersion := radialEdgeProjection_onto
  boundary_submersion := fun p hp =>
    ⟨radialEdgeRotation p, radialEdgeRotation_smooth p, radialEdgeRotation_zero p,
      radialEdgeRotation_boundary p hp, radialEdgeRotation_derivative p⟩
  fibre := radialEdgeFibre
  fibre_embedding := radialEdgeFibre_embedding
  fibre_range := radialEdgeFibre_range
  interior := by
    intro p hp
    obtain ⟨q, rfl⟩ := hp
    exact (solidTorus_isInteriorPoint_iff (edgeToCarrier q)).mpr
      ((sub_nonpos.mp
        (show cliffordHeight q.val - (-(3 / 4 : ℝ)) ≤ 0 from q.property)).trans_lt
          (by norm_num))

end GC.GraphManifold.Assembly.FC39P0.X135Radial

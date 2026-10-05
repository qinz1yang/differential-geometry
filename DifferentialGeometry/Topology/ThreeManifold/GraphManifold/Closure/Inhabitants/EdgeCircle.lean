import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RegularCut
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateParts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Adapters
import DifferentialGeometry.Topology.Manifold.ProductSectionEmbedding
import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpaceProdLeft
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportTarget
import DifferentialGeometry.Topology.Manifold.BoundaryTangentFlow.CircleRotation

/-!
A genuine hemisphere solid torus in the sphere-circle product has its circle projection,
boundary rotation, and an embedded closed disk fibre in the native half-space model.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.Seifert GC.GraphManifold DifferentialGeometry.Manifold
open scoped Manifold ContDiff

namespace GC.GraphManifold.Assembly

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

local instance edgeCircleOriginalCharts :
    ChartedSpace (ModelProd (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin 1)))
      (UnitDisc.{0} × Circle) :=
  prodChartedSpace (EuclideanHalfSpace 2) UnitDisc (EuclideanSpace ℝ (Fin 1)) Circle

private def edgeCircleIndex : Fin standardRegularSystem.count := ⟨0, by decide⟩

private def edgeCircleTheta : (UnitDisc.{0} × Circle) ≃ₘ⟮
    (𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯ (standardRegularPiece edgeCircleIndex).Piece :=
  productCarrierEmbeddedPieces.theta edgeCircleIndex

private abbrev edgeCircleEmbedding : PieceEmbedding (NoCuts.carrier sphereTwoTimesCircleLift) :=
  { standardRegularPiece edgeCircleIndex with
    injective := (productCarrierHemisphere_injective true).comp edgeCircleTheta.symm.injective }

private def edgeCircleProjection (q : edgeCircleEmbedding.Piece) : Circle :=
  (edgeCircleTheta.symm q).2

private theorem edgeCircleProjection_smooth :
    ContMDiff (𝓡∂ 3) (𝓡 1) ∞ edgeCircleProjection :=
  contMDiff_snd.comp edgeCircleTheta.symm.contMDiff

private theorem edgeCircleProjection_onto (q : edgeCircleEmbedding.Piece) :
    Surjective (mfderiv (𝓡∂ 3) (𝓡 1) edgeCircleProjection q) := by
  obtain ⟨e, he⟩ := edgeCircleTheta.symm.isInvertible_mfderiv (x := q) (by simp)
  have h : Bijective (mfderiv (𝓡∂ 3) ((𝓡∂ 2).prod (𝓡 1)) edgeCircleTheta.symm q) := by
    rw [← he, ContinuousLinearEquiv.coe_coe]
    exact e.bijective
  change Surjective (mfderiv (𝓡∂ 3) (𝓡 1) (Prod.snd ∘ edgeCircleTheta.symm) q)
  rw [mfderiv_comp q mdifferentiableAt_snd
    (edgeCircleTheta.symm.mdifferentiable (by simp) q), mfderiv_snd]
  change Surjective (fun v => (mfderiv (𝓡∂ 3) ((𝓡∂ 2).prod (𝓡 1))
    edgeCircleTheta.symm q v).2)
  intro v
  obtain ⟨w, hw⟩ := h.surjective (0, v)
  exact ⟨w, congrArg Prod.snd hw⟩

private def edgeCircleRotation (q : edgeCircleEmbedding.Piece) (t : ℝ) :
    edgeCircleEmbedding.Piece :=
  edgeCircleTheta ((edgeCircleTheta.symm q).1, Circle.exp t * (edgeCircleTheta.symm q).2)

private theorem edgeCircleRotation_smooth (q : edgeCircleEmbedding.Piece) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 3) ∞ (edgeCircleRotation q) :=
  edgeCircleTheta.contMDiff.comp
    (contMDiff_const.prodMk (contMDiff_circleExp.mul contMDiff_const))

private theorem edgeCircleRotation_zero (q : edgeCircleEmbedding.Piece) :
    edgeCircleRotation q 0 = q := by
  simpa only [edgeCircleRotation, Circle.exp_zero, one_mul] using
    edgeCircleTheta.apply_symm_apply q

private theorem edgeCircleRotation_boundary (q : edgeCircleEmbedding.Piece)
    (hq : (𝓡∂ 3).IsBoundaryPoint q) (t : ℝ) :
    (𝓡∂ 3).IsBoundaryPoint (edgeCircleRotation q t) := by
  have hb := ((edgeCircleTheta.symm.isLocalDiffeomorph q).isBoundaryPoint_iff
    (by simp)).mp hq
  apply ((edgeCircleTheta.isLocalDiffeomorph
    ((edgeCircleTheta.symm q).1, Circle.exp t * (edgeCircleTheta.symm q).2))
    |>.isBoundaryPoint_iff (by simp)).mp
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint] at hb ⊢
  change edgeCircleTheta.symm q ∉ ((𝓡∂ 2).prod (𝓡 1)).interior _ at hb
  change ((edgeCircleTheta.symm q).1, Circle.exp t * (edgeCircleTheta.symm q).2) ∉
    ((𝓡∂ 2).prod (𝓡 1)).interior _
  have hc : (𝓡 1).interior Circle = univ := ModelWithCorners.interior_eq_univ
  rw [ModelWithCorners.interior_prod, mem_prod, hc] at hb ⊢
  simp only [mem_univ, and_true] at hb ⊢
  exact hb

private theorem edgeCircleRotation_derivative (q : edgeCircleEmbedding.Piece) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (edgeCircleProjection ∘ edgeCircleRotation q) 0 ≠ 0 := by
  have heq : edgeCircleProjection ∘ edgeCircleRotation q =
      fun t : ℝ => Circle.exp t * (edgeCircleTheta.symm q).2 := by
    funext t
    exact congrArg Prod.snd (edgeCircleTheta.symm_apply_apply _)
  rw [heq]
  intro hzero
  have h := DifferentialGeometry.Manifold.BoundaryTangentFlow.mfderiv_coe_rotation
    (edgeCircleTheta.symm q).2
  simp only [hzero, zero_apply] at h
  have hz := (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun w : Circle => (w : ℂ))
    (edgeCircleTheta.symm q).2).map_zero
  exact (mul_ne_zero Complex.I_ne_zero (Circle.coe_ne_zero _)) (h.symm.trans hz)

private def edgeCircleFibre (x : ClosedCell 2) : edgeCircleEmbedding.Piece :=
  edgeCircleTheta (unitDiscClosedCell.{0}.symm x, 1)

private theorem edgeCircleFibre_embedding :
    IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ edgeCircleFibre := by
  have hf : IsSmoothEmbedding (𝓡∂ 2) ((𝓡∂ 2).prod (𝓡 1)) ∞
      (fun x : ClosedCell 2 => (unitDiscClosedCell.{0}.symm x, (1 : Circle))) :=
    (isSmoothEmbedding_prodMk_const (I := 𝓡∂ 2) (1 : Circle)).comp_diffeomorph
      unitDiscClosedCell.{0}.symm
  let e := euclideanHalfSpaceProdLeftHomeomorph 1 1
  let L := euclideanHalfSpaceProdLeftCoordinates 1 1
  have hc : ∀ y, (𝓡∂ 3) (e y) = L (((𝓡∂ 2).prod (𝓡 1)) y) :=
    euclideanHalfSpaceProdLeftHomeomorph_model 1 1
  have hs := isSmoothEmbedding_chartedSpaceTransHomeomorph_target
    ((𝓡∂ 2).prod (𝓡 1)) (𝓡∂ 3) e L hc (𝓡∂ 2) hf
  let edgeCircleOriginalLocal :
      ChartedSpace (ModelProd (EuclideanHalfSpace (1 + 1)) (EuclideanSpace ℝ (Fin 1)))
        (UnitDisc.{0} × Circle) := edgeCircleOriginalCharts
  let edgeCircleOriginalSmooth : IsManifold ((𝓡∂ 2).prod (𝓡 1)) ∞
      (UnitDisc.{0} × Circle) := IsManifold.prod UnitDisc Circle
  let edgeCircleProductCharts :
      ChartedSpace (EuclideanHalfSpace 3) (UnitDisc.{0} × Circle) :=
    chartedSpaceTransHomeomorph (M := UnitDisc.{0} × Circle) e
  let edgeCircleProductSmooth : IsManifold (𝓡∂ 3) ∞ (UnitDisc.{0} × Circle) :=
    euclideanHalfSpaceProdLeft_isManifold 1 1 (UnitDisc.{0} × Circle)
  let D : (UnitDisc.{0} × Circle) ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ edgeCircleEmbedding.Piece :=
    { toEquiv := edgeCircleTheta.toEquiv
      contMDiff_toFun := (contMDiff_chartedSpaceTransHomeomorph_source_iff
        ((𝓡∂ 2).prod (𝓡 1)) (𝓡∂ 3) e L hc (𝓡∂ 3)).mpr edgeCircleTheta.contMDiff
      contMDiff_invFun := (contMDiff_chartedSpaceTransHomeomorph_iff
        ((𝓡∂ 2).prod (𝓡 1)) (𝓡∂ 3) e L hc (𝓡∂ 3)).mpr
          edgeCircleTheta.symm.contMDiff }
  exact hs.diffeomorph_comp D

private theorem edgeCircleFibre_range :
    range edgeCircleFibre = edgeCircleProjection ⁻¹' {1} := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    change (edgeCircleTheta.symm (edgeCircleTheta (unitDiscClosedCell.symm x, 1))).2 = 1
    rw [edgeCircleTheta.symm_apply_apply]
  · intro hq
    change (edgeCircleTheta.symm q).2 = 1 at hq
    refine ⟨unitDiscClosedCell (edgeCircleTheta.symm q).1, ?_⟩
    change edgeCircleTheta (unitDiscClosedCell.symm
      (unitDiscClosedCell (edgeCircleTheta.symm q).1), 1) = q
    rw [unitDiscClosedCell.symm_apply_apply, ← hq]
    exact edgeCircleTheta.apply_symm_apply q

def standardEdgeCirclePiece : EdgeCirclePiece (NoCuts.carrier sphereTwoTimesCircleLift) where
  piece := edgeCircleEmbedding
  proj := edgeCircleProjection
  proj_smooth := edgeCircleProjection_smooth
  proj_submersion := edgeCircleProjection_onto
  boundary_submersion q hq := ⟨edgeCircleRotation q, edgeCircleRotation_smooth q,
    edgeCircleRotation_zero q, edgeCircleRotation_boundary q hq, edgeCircleRotation_derivative q⟩
  fibre := edgeCircleFibre
  fibre_embedding := edgeCircleFibre_embedding
  fibre_range := edgeCircleFibre_range
  interior := by
    intro y hy
    change y ∈ (𝓡 3).interior _
    rw [ModelWithCorners.interior_eq_univ]
    exact mem_univ y

end GC.GraphManifold.Assembly

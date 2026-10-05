import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Edges
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Adapters
import DifferentialGeometry.Topology.Manifold.ProductSectionEmbedding
import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpaceProdLeft
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportTarget
import DifferentialGeometry.Topology.Manifold.ModelTransportDiffeomorph
import DifferentialGeometry.Topology.Manifold.BoundaryTangentFlow.CircleRotation
import DifferentialGeometry.Topology.Embedding.Diffeomorph

/-!
# FC39 GROUP G, RIMBOX: the edge-circle pieces of the circle components (D62-5)

Lane FC39-RIMBOX-ROUND, disposition D62-5 (external review 62 §六, suggested name
`edgeCirclePiece_of_circleTriv`). For a circle component `j` of the edge export `M`, the whole
fibre-preserving product `circleTriv j : D² × S¹ → W` (smooth, injective, full rank, image the whole
component, slices = whole disks, slice rims = whole rims) is packaged as an `EdgeCirclePiece`:

* the piece is `UnitDisc × Circle` in the half-space model `𝓡∂ 3`
  (`euclideanHalfSpaceProdLeftChartedSpace 1 1`); `solidChart_GRND` is the diffeomorphism to
  `ClosedCell 2 × Circle` with the product model (the model change composed with `unitDiscClosedCell`);
* `map = circleTriv j ∘ solidChart_GRND`, `proj = snd ∘ solidChart_GRND`, `fibre x = solidChart⁻¹ (x, 1)`;
* `boundary_submersion` through the rotation `γ t = solidChart⁻¹ (w, exp(t) z)` (review 62: `γ(s) =
  (w, z e^{is})`), which stays in the model boundary (`solidChart_isBoundaryPoint_iff_GRND`).

The four link clauses of `EdgeComponentsLink` for the piece: `edgeCirclePiece_whole_GRND`,
`edgeCirclePiece_proj_GRND`, `edgeCirclePiece_disk_GRND`, `edgeCirclePiece_rim_GRND`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Manifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsEC_GRND : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothEC_GRND : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

local instance unitDiscSetCompact_GRND : CompactSpace unitDiscSet :=
  isCompact_iff_compactSpace.mp isCompact_unitDiscSet

local instance unitDiscSecondCountable_GRND : SecondCountableTopology UnitDisc.{u} :=
  Homeomorph.ulift.isEmbedding.secondCountableTopology

local instance solidProdCharts_GRND :
    ChartedSpace (ModelProd (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin 1)))
      (UnitDisc.{u} × Circle) :=
  prodChartedSpace (EuclideanHalfSpace 2) UnitDisc (EuclideanSpace ℝ (Fin 1)) Circle

local instance solidProdCharts11_GRND :
    ChartedSpace (ModelProd (EuclideanHalfSpace (1 + 1)) (EuclideanSpace ℝ (Fin 1)))
      (UnitDisc.{u} × Circle) :=
  solidProdCharts_GRND

local instance solidProdSmooth_GRND :
    IsManifold ((𝓡∂ 2).prod (𝓡 1)) ∞ (UnitDisc.{u} × Circle) :=
  IsManifold.prod UnitDisc Circle

local instance solidProdSmooth11_GRND :
    IsManifold ((𝓡∂ (1 + 1)).prod (𝓡 1)) ∞ (UnitDisc.{u} × Circle) :=
  solidProdSmooth_GRND

local instance solidHalfCharts_GRND : ChartedSpace (EuclideanHalfSpace 3) (UnitDisc.{u} × Circle) :=
  euclideanHalfSpaceProdLeftChartedSpace 1 1 (UnitDisc.{u} × Circle)

local instance solidHalfSmooth_GRND : IsManifold (𝓡∂ 3) ∞ (UnitDisc.{u} × Circle) :=
  euclideanHalfSpaceProdLeft_isManifold 1 1 (UnitDisc.{u} × Circle)

/-! ## The solid torus chart -/

/-- The identity of `D² × S¹` from the half-space model `𝓡∂ 3` to the product model. -/
def solidModelChange_GRND :
    (UnitDisc.{u} × Circle) ≃ₘ⟮𝓡∂ 3, (𝓡∂ 2).prod (𝓡 1)⟯ (UnitDisc.{u} × Circle) :=
  (diffeomorphTransHomeomorph ((𝓡∂ 2).prod (𝓡 1)) (𝓡∂ 3)
    (euclideanHalfSpaceProdLeftHomeomorph 1 1) (euclideanHalfSpaceProdLeftCoordinates 1 1)
    (euclideanHalfSpaceProdLeftHomeomorph_model 1 1) ∞).symm

/-- **The solid torus chart** `D² × S¹ (𝓡∂ 3) ≅ ClosedCell 2 × Circle (product model)`. -/
def solidChart_GRND :
    (UnitDisc.{u} × Circle) ≃ₘ⟮𝓡∂ 3, (𝓡∂ 2).prod (𝓡 1)⟯ (ClosedCell 2 × Circle) :=
  solidModelChange_GRND.trans (unitDiscClosedCell.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞))

theorem solidChart_apply_GRND (q : UnitDisc.{u} × Circle) :
    solidChart_GRND q = (unitDiscClosedCell q.1, q.2) :=
  rfl

theorem solidChart_mfderiv_bijective_GRND (q : UnitDisc.{u} × Circle) :
    Bijective (mfderiv (𝓡∂ 3) ((𝓡∂ 2).prod (𝓡 1)) solidChart_GRND q) := by
  obtain ⟨e, he⟩ := solidChart_GRND.isInvertible_mfderiv (x := q) (by simp)
  rw [← he, ContinuousLinearEquiv.coe_coe]
  exact e.bijective

/-- A point of the solid torus is a model-boundary point iff its disk coordinate is on the rim. -/
theorem solidChart_isBoundaryPoint_iff_GRND {q : UnitDisc.{u} × Circle} :
    (𝓡∂ 3).IsBoundaryPoint q ↔ (solidChart_GRND q).1 ∈ diskRim := by
  rw [(solidChart_GRND.isLocalDiffeomorph q).isBoundaryPoint_iff (by simp)]
  change ((𝓡∂ 2).prod (𝓡 1)).IsBoundaryPoint (solidChart_GRND q) ↔
    (𝓡∂ 2).IsBoundaryPoint (solidChart_GRND q).1
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
    ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint]
  change solidChart_GRND q ∉ ((𝓡∂ 2).prod (𝓡 1)).interior _ ↔
    (solidChart_GRND q).1 ∉ (𝓡∂ 2).interior _
  have hc : (𝓡 1).interior Circle = univ := ModelWithCorners.interior_eq_univ
  rw [ModelWithCorners.interior_prod, mem_prod, hc]
  simp only [mem_univ, and_true]

/-- The circle projection of the solid torus. -/
def solidProj_GRND (q : UnitDisc.{u} × Circle) : Circle :=
  (solidChart_GRND q).2

theorem solidProj_smooth_GRND : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ solidProj_GRND.{u} :=
  contMDiff_snd.comp solidChart_GRND.contMDiff

theorem solidProj_submersion_GRND (q : UnitDisc.{u} × Circle) :
    Surjective (mfderiv (𝓡∂ 3) (𝓡 1) solidProj_GRND q) := by
  have h := solidChart_mfderiv_bijective_GRND q
  change Surjective (mfderiv (𝓡∂ 3) (𝓡 1) (Prod.snd ∘ solidChart_GRND) q)
  rw [mfderiv_comp q mdifferentiableAt_snd (solidChart_GRND.mdifferentiable (by simp) q),
    mfderiv_snd]
  change Surjective (fun v => (mfderiv (𝓡∂ 3) ((𝓡∂ 2).prod (𝓡 1)) solidChart_GRND q v).2)
  intro v
  obtain ⟨w, hw⟩ := h.surjective (0, v)
  exact ⟨w, congrArg Prod.snd hw⟩

/-- The rotation of the circle factor through `q`. -/
def solidRotation_GRND (q : UnitDisc.{u} × Circle) (t : ℝ) : UnitDisc.{u} × Circle :=
  solidChart_GRND.symm ((solidChart_GRND q).1, Circle.exp t * (solidChart_GRND q).2)

theorem solidRotation_smooth_GRND (q : UnitDisc.{u} × Circle) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 3) ∞ (solidRotation_GRND q) :=
  solidChart_GRND.symm.contMDiff.comp
    (contMDiff_const.prodMk (contMDiff_circleExp.mul contMDiff_const))

theorem solidRotation_zero_GRND (q : UnitDisc.{u} × Circle) : solidRotation_GRND q 0 = q := by
  simpa only [solidRotation_GRND, Circle.exp_zero, one_mul, Prod.mk.eta] using
    solidChart_GRND.symm_apply_apply q

theorem solidChart_solidRotation_GRND (q : UnitDisc.{u} × Circle) (t : ℝ) :
    solidChart_GRND (solidRotation_GRND q t) =
      ((solidChart_GRND q).1, Circle.exp t * (solidChart_GRND q).2) :=
  solidChart_GRND.apply_symm_apply _

theorem solidRotation_boundary_GRND (q : UnitDisc.{u} × Circle) (hq : (𝓡∂ 3).IsBoundaryPoint q)
    (t : ℝ) : (𝓡∂ 3).IsBoundaryPoint (solidRotation_GRND q t) := by
  rw [solidChart_isBoundaryPoint_iff_GRND] at hq ⊢
  rw [solidChart_solidRotation_GRND]
  exact hq

theorem solidRotation_derivative_GRND (q : UnitDisc.{u} × Circle) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (solidProj_GRND ∘ solidRotation_GRND q) 0 ≠ 0 := by
  have heq : solidProj_GRND ∘ solidRotation_GRND q =
      fun t : ℝ => Circle.exp t * (solidChart_GRND q).2 := by
    funext t
    exact congrArg Prod.snd (solidChart_solidRotation_GRND q t)
  rw [heq]
  intro hzero
  have h := DifferentialGeometry.Manifold.BoundaryTangentFlow.mfderiv_coe_rotation
    (solidChart_GRND q).2
  simp only [hzero, zero_apply] at h
  have hz := (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun w : Circle => (w : ℂ)) (solidChart_GRND q).2).map_zero
  exact (mul_ne_zero Complex.I_ne_zero (Circle.coe_ne_zero _)) (h.symm.trans hz)

/-- The fibre disk over `1`. -/
def solidFibre_GRND (x : ClosedCell 2) : UnitDisc.{u} × Circle :=
  solidChart_GRND.symm (x, 1)

theorem solidFibre_embedding_GRND :
    IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ solidFibre_GRND.{u} := by
  have hf : IsSmoothEmbedding (𝓡∂ 2) ((𝓡∂ 2).prod (𝓡 1)) ∞
      (fun x : ClosedCell 2 => (x, (1 : Circle))) :=
    isSmoothEmbedding_prodMk_const (I := 𝓡∂ 2) (1 : Circle)
  have hg : IsSmoothEmbedding (𝓡∂ 2) ((𝓡∂ 2).prod (𝓡 1)) ∞
      ((unitDiscClosedCell.{u}.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)).symm ∘
        fun x : ClosedCell 2 => (x, (1 : Circle))) :=
    hf.diffeomorph_comp _
  exact isSmoothEmbedding_chartedSpaceTransHomeomorph_target ((𝓡∂ 2).prod (𝓡 1)) (𝓡∂ 3)
    (euclideanHalfSpaceProdLeftHomeomorph 1 1) (euclideanHalfSpaceProdLeftCoordinates 1 1)
    (euclideanHalfSpaceProdLeftHomeomorph_model 1 1) (𝓡∂ 2) hg

theorem solidFibre_range_GRND :
    range solidFibre_GRND.{u} = solidProj_GRND ⁻¹' {1} := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    change (solidChart_GRND (solidChart_GRND.symm (x, 1))).2 = 1
    rw [solidChart_GRND.{u}.apply_symm_apply]
  · intro hq
    change (solidChart_GRND q).2 = 1 at hq
    refine ⟨(solidChart_GRND q).1, ?_⟩
    change solidChart_GRND.symm ((solidChart_GRND q).1, 1) = q
    rw [← hq, Prod.mk.eta]
    exact solidChart_GRND.symm_apply_apply q

/-! ## The edge-circle piece of a circle component -/

variable {W : CompactCarrier.{u}}

/-- **The edge-circle piece of the circle component `j`** (D62-5): `map = circleTriv j ∘ solidChart`. -/
def EdgeComponentModels.edgeCirclePiece_of_circleTriv_GRND {P : EdgeBundle W}
    (M : EdgeComponentModels P) (j : Fin M.circleCount) : EdgeCirclePiece W where
  piece :=
    { Piece := UnitDisc.{u} × Circle
      map := M.circleTriv j ∘ solidChart_GRND
      smooth := (M.circleTriv_smooth j).comp solidChart_GRND.contMDiff
      mfderiv_bijective := fun q => by
        rw [mfderiv_comp q ((M.circleTriv_smooth j).mdifferentiableAt (by simp))
          (solidChart_GRND.mdifferentiable (by simp) q), ContinuousLinearMap.coe_comp]
        exact (M.circleTriv_mfderiv j (solidChart_GRND q)).comp
          (solidChart_mfderiv_bijective_GRND q)
      injective := (M.circleTriv_injective j).comp solidChart_GRND.injective }
  proj := solidProj_GRND
  proj_smooth := solidProj_smooth_GRND
  proj_submersion := solidProj_submersion_GRND
  boundary_submersion q hq := ⟨solidRotation_GRND q, solidRotation_smooth_GRND q,
    solidRotation_zero_GRND q, solidRotation_boundary_GRND q hq, solidRotation_derivative_GRND q⟩
  fibre := solidFibre_GRND
  fibre_embedding := solidFibre_embedding_GRND
  fibre_range := solidFibre_range_GRND
  interior := by
    rintro _ ⟨q, rfl⟩
    exact P.source_interior (M.circleTriv_proj j (solidChart_GRND q).1 (solidChart_GRND q).2).1

theorem EdgeComponentModels.edgeCirclePiece_map_GRND {P : EdgeBundle W}
    (M : EdgeComponentModels P) (j : Fin M.circleCount) (q : UnitDisc.{u} × Circle) :
    (M.edgeCirclePiece_of_circleTriv_GRND j).piece.map q = M.circleTriv j (solidChart_GRND q) :=
  rfl

/-- **`circle_whole`**: the image is the whole component. -/
theorem EdgeComponentModels.edgeCirclePiece_whole_GRND {P : EdgeBundle W}
    (M : EdgeComponentModels P) (j : Fin M.circleCount) :
    range (M.edgeCirclePiece_of_circleTriv_GRND j).piece.map =
      P.wholeComponent (M.componentEquiv (.inr j)) := by
  rw [← M.circleTriv_range j]
  exact solidChart_GRND.surjective.range_comp (M.circleTriv j)

/-- **`circle_proj`**: the piece projects to the circle parametrization of the component. -/
theorem EdgeComponentModels.edgeCirclePiece_proj_GRND {P : EdgeBundle W}
    (M : EdgeComponentModels P) (j : Fin M.circleCount)
    (q : (M.edgeCirclePiece_of_circleTriv_GRND j).piece.Piece) :
    ∃ hx : (M.edgeCirclePiece_of_circleTriv_GRND j).piece.map q ∈ P.source,
      P.proj ⟨(M.edgeCirclePiece_of_circleTriv_GRND j).piece.map q, hx⟩ =
        M.circleBase j ((M.edgeCirclePiece_of_circleTriv_GRND j).proj q) :=
  M.circleTriv_proj j (solidChart_GRND q).1 (solidChart_GRND q).2

/-- **`circle_disk`**: every fibre of the projection is the whole disk. -/
theorem EdgeComponentModels.edgeCirclePiece_disk_GRND {P : EdgeBundle W}
    (M : EdgeComponentModels P) (j : Fin M.circleCount) (z : Circle) :
    (M.edgeCirclePiece_of_circleTriv_GRND j).piece.map ''
        {q | (M.edgeCirclePiece_of_circleTriv_GRND j).proj q = z} =
      P.disk (M.circleBase j z) := by
  rw [← M.circleTriv_disk j z]
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨(solidChart_GRND q).1, ?_⟩
    change M.circleTriv j ((solidChart_GRND q).1, z) = M.circleTriv j (solidChart_GRND q)
    rw [← show (solidChart_GRND q).2 = z from hq]
  · rintro ⟨w, rfl⟩
    refine ⟨solidChart_GRND.{u}.symm (w, z), ?_, ?_⟩
    · change (solidChart_GRND.{u} (solidChart_GRND.{u}.symm (w, z))).2 = z
      rw [solidChart_GRND.{u}.apply_symm_apply]
    · change M.circleTriv j (solidChart_GRND.{u} (solidChart_GRND.{u}.symm (w, z))) = _
      rw [solidChart_GRND.{u}.apply_symm_apply]

/-- **`circle_rim`**: the model-boundary part of every fibre is the whole rim. -/
theorem EdgeComponentModels.edgeCirclePiece_rim_GRND {P : EdgeBundle W}
    (M : EdgeComponentModels P) (j : Fin M.circleCount) (z : Circle) :
    (M.edgeCirclePiece_of_circleTriv_GRND j).piece.map ''
        {q | (M.edgeCirclePiece_of_circleTriv_GRND j).proj q = z ∧ (𝓡∂ 3).IsBoundaryPoint q} =
      P.rim (M.circleBase j z) := by
  rw [← M.circleTriv_rim j z]
  ext y
  constructor
  · rintro ⟨q, ⟨hq, hb⟩, rfl⟩
    refine ⟨(solidChart_GRND q).1, solidChart_isBoundaryPoint_iff_GRND.1 hb, ?_⟩
    change M.circleTriv j ((solidChart_GRND q).1, z) = M.circleTriv j (solidChart_GRND q)
    rw [← show (solidChart_GRND q).2 = z from hq]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨solidChart_GRND.{u}.symm (w, z), ⟨?_, ?_⟩, ?_⟩
    · change (solidChart_GRND.{u} (solidChart_GRND.{u}.symm (w, z))).2 = z
      rw [solidChart_GRND.{u}.apply_symm_apply]
    · refine (solidChart_isBoundaryPoint_iff_GRND (q := solidChart_GRND.{u}.symm (w, z))).2 ?_
      rw [solidChart_GRND.{u}.apply_symm_apply]
      exact hw
    · change M.circleTriv j (solidChart_GRND.{u} (solidChart_GRND.{u}.symm (w, z))) = _
      rw [solidChart_GRND.{u}.apply_symm_apply]

end GC.GraphManifold.Assembly.FC39P0

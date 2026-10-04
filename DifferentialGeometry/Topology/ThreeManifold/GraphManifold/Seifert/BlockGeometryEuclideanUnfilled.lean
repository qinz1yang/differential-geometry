import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockCharts
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsBlockGeometryUnconditional

/-!
# Whole interiors of unfilled annulus and pants blocks

With no filling tubes, the product chart covers the actual carrier interior. Transport from the
standard annulus and unconditional pants geometries gives Euclidean and hyperbolic-product models.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

variable {W : CompactCarrier.{u}} {d : SeifertData}

private theorem unfilled_productRegion_eq (C : SeifertBlockCharts W d)
    (h0 : d.fillingCount = 0) : C.productRegion = W.pieceInterior ⊤ := by
  apply TopologicalSpace.Opens.ext
  ext x
  change x ∈ C.productRegion ↔ x ∈ (⊤ : TopologicalSpace.Opens W.Carrier) ∧ x ∈ W.interior
  constructor
  · intro hx
    exact ⟨trivial, C.productRegion_interior hx⟩
  · intro hx
    rcases C.covers x hx.2 with hp | ⟨m, hm⟩
    · exact hp
    · exact Fin.elim0 (h0 ▸ m)

def SeifertBlockCharts.unfilledProductInteriorDiffeomorph
    (C : SeifertBlockCharts W d) (h0 : d.fillingCount = 0) :
    W.pieceInterior ⊤ ≃ₘ⟮W.model, PlaneCircleModel⟯ (planarOpen d.k × Circle) := by
  rw [← unfilled_productRegion_eq C h0]
  exact C.product.symm

def unfilledT2IntervalGeometry (C : SeifertBlockCharts W d)
    (h0 : d.fillingCount = 0) (hk : d.k = 2) : W.InteriorGeometry ⊤ := by
  have e : W.pieceInterior ⊤ ≃ₘ⟮W.model, PlaneCircleModel⟯ (planarOpen 2 × Circle) := by
    have f := C.unfilledProductInteriorDiffeomorph h0
    rw [hk] at f
    exact f
  exact transportInteriorGeometry
    (e.trans annulusCirclePiece.{u}.chartPieceInteriorDiffeomorph)
    annulusCircleBlock_interiorGeometry.{u}

theorem unfilledT2IntervalGeometry_model (C : SeifertBlockCharts W d)
    (h0 : d.fillingCount = 0) (hk : d.k = 2) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (unfilledT2IntervalGeometry C h0 hk).model = ThurstonModel.euclidean :=
  rfl

def unfilledPantsBlockGeometry (C : SeifertBlockCharts W d)
    (h0 : d.fillingCount = 0) (hk : d.k = 3) : W.InteriorGeometry ⊤ := by
  have e : W.pieceInterior ⊤ ≃ₘ⟮W.model, PlaneCircleModel⟯ (planarOpen 3 × Circle) := by
    have f := C.unfilledProductInteriorDiffeomorph h0
    rw [hk] at f
    exact f
  exact transportInteriorGeometry (e.trans pantsCirclePiece.{u}.chartPieceInteriorDiffeomorph)
    productPantsInteriorGeometry'.{u}

theorem unfilledPantsBlockGeometry_model (C : SeifertBlockCharts W d)
    (h0 : d.fillingCount = 0) (hk : d.k = 3) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (unfilledPantsBlockGeometry C h0 hk).model = ThurstonModel.hyperbolicProduct :=
  rfl

def unfilledBlockGeometry (C : SeifertBlockCharts W d)
    (h0 : d.fillingCount = 0) (hk : d.k = 2 ∨ d.k = 3) : W.InteriorGeometry ⊤ :=
  if htwo : d.k = 2 then unfilledT2IntervalGeometry C h0 htwo
  else unfilledPantsBlockGeometry C h0 (hk.resolve_left htwo)

theorem unfilledBlockGeometry_model (C : SeifertBlockCharts W d)
    (h0 : d.fillingCount = 0) (hk : d.k = 2 ∨ d.k = 3) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (unfilledBlockGeometry C h0 hk).model =
      if d.k = 2 then ThurstonModel.euclidean else ThurstonModel.hyperbolicProduct := by
  by_cases htwo : d.k = 2
  · rw [unfilledBlockGeometry, dite_eq_left htwo, ite_eq_left htwo]
    exact unfilledT2IntervalGeometry_model C h0 htwo
  · rw [unfilledBlockGeometry, dite_eq_right htwo, ite_eq_right htwo]
    exact unfilledPantsBlockGeometry_model C h0 (hk.resolve_left htwo)

def SeifertBlock.unfilledBlockGeometry (B : SeifertBlock W d)
    (h0 : d.fillingCount = 0) (hk : d.k = 2 ∨ d.k = 3) : W.InteriorGeometry ⊤ :=
  GC.Seifert.unfilledBlockGeometry (B.unfilledCharts h0) h0 hk

theorem SeifertBlock.unfilledBlockGeometry_model (B : SeifertBlock W d)
    (h0 : d.fillingCount = 0) (hk : d.k = 2 ∨ d.k = 3) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (B.unfilledBlockGeometry h0 hk).model =
      if d.k = 2 then ThurstonModel.euclidean else ThurstonModel.hyperbolicProduct :=
  GC.Seifert.unfilledBlockGeometry_model (B.unfilledCharts h0) h0 hk

end GC.Seifert

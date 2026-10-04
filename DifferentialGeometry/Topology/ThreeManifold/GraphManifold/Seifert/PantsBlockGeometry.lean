import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsGeometry
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryFlat

/-!
# Pants blocks are `H² × ℝ`, given the pants identification

Chapter 6, packet K16c. `pantsImage = {(z, u) ∈ ℂ × S¹ | planarFunction 3 z < 0}` is the open
pants `P₃°` (the interior of `pantsSurface`, `isInteriorPoint_planarSet_iff`) times the circle, an
open subset of `ℂ × S¹` charted like the flat block's `flatImage`. The identification of the
quotient `PantsQuotient = (pantsGroup × ℤ)\(H² × ℝ)` of `Seifert/PantsGeometry.lean` with it is
the named input `PantsQuotientDiffeo`, the `Nonempty` of that diffeomorphism (its proof is the
fold map of K16d). Given it, `pantsInteriorEquiv` (the interior of the K06b carrier
`productCarrier 3` is `pantsImage`, `isInteriorPoint_productSet_iff`) and the chosen
diffeomorphism give `pantsCircleInteriorDiffeo`, and pulling back `pantsQuotientGeometry` gives
`productPantsInteriorGeometry`. For a product-fibred piece over a `PlanarBase 3`,
`ProductFibredPiece.pieceDiffeomorph` and `pieceInteriorCongr` (lane K16a,
`Seifert/BlockGeometryFlat.lean`) transport it to `P.pantsInteriorGeometry`, and for a Seifert
block with `d.k = 3` to `pantsBlockInteriorGeometry B`; all are of model `.hyperbolicProduct` by
`rfl` (the `_model` lemmas) and complete by `GeometricStructure.pullback`. No goodness hypothesis
is used.

Scope: the geometry lives on the interior of the product piece of the block's own torus
presentation, i.e. on the unfilled pants piece. When the block has fillings
(`0 < d.fillingCount`), the piece of the ambient torus decomposition is the whole block, whose
interior also contains the filling solid tori; that case (cone points, K16d and later) is the
named input `FilledPantsBlockGeometry`: every good open block over `P₃` with fillings and
`openModelOf = .hyperbolicProduct` carries a geometry of model `.hyperbolicProduct` on its whole
interior.
-/

set_option autoImplicit false

universe u

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology

namespace GC.Seifert

attribute [local instance] finrank_real_complex_fact'

def pantsImage : TopologicalSpace.Opens (ℂ × Circle) :=
  ⟨{y | planarFunction 3 y.1 < 0},
    isOpen_lt ((contDiff_planarFunction 3).continuous.comp continuous_fst) continuous_const⟩

theorem mem_pantsImage {y : ℂ × Circle} : y ∈ pantsImage ↔ planarFunction 3 y.1 < 0 :=
  Iff.rfl

def PantsQuotientDiffeo : Prop :=
  Nonempty (PantsQuotient ≃ₘ⟮𝓡 3, 𝓘(ℝ, ℂ).prod (𝓡 1)⟯ pantsImage)

theorem isInteriorPoint_planarSet_iff (k : ℕ) (x : planarSet.{u} k) :
    (𝓡∂ 2).IsInteriorPoint x ↔ planarFunction k x.val.down < 0 := by
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint, planarSet_isBoundaryPoint_iff]
  exact ⟨fun h => lt_of_le_of_ne (x.2 : planarFunction k x.val.down ≤ 0) h, fun h => h.ne⟩

theorem isInteriorPoint_productSet_iff (k : ℕ) (x : productSet.{u} k) :
    (𝓡∂ 3).IsInteriorPoint x ↔ planarFunction k x.val.1.down < 0 := by
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint, productSet_isBoundaryPoint_iff]
  exact ⟨fun h => lt_of_le_of_ne (x.2 : planarFunction k x.val.1.down ≤ 0) h, fun h => h.ne⟩

def pantsCircleCarrier : CompactCarrier.{u} := productCarrier 3 (Or.inr rfl)

def pantsCirclePresentation : TorusPresentation pantsCircleCarrier.{u} :=
  productPresentation 3 (Or.inr rfl)

def pantsCirclePiece :
    ProductFibredPiece pantsCirclePresentation.{u} ⟨0, Nat.one_pos⟩ 3 :=
  productFibredPiece 3 (Or.inr rfl)

def pantsInteriorEquiv :
    pantsImage ≃ₘ⟮𝓘(ℝ, ℂ).prod (𝓡 1), pantsCircleCarrier.{u}.model⟯
      pantsCircleCarrier.{u}.pieceInterior ⊤ where
  toFun y := ⟨⟨(ULift.up y.1.1, y.1.2), (mem_pantsImage.1 y.2).le⟩,
    ⟨trivial, (isInteriorPoint_productSet_iff 3 ⟨(ULift.up y.1.1, y.1.2),
      (mem_pantsImage.1 y.2).le⟩).2 (mem_pantsImage.1 y.2)⟩⟩
  invFun x := ⟨(x.1.1.1.down, x.1.1.2),
    mem_pantsImage.2 ((isInteriorPoint_productSet_iff 3 x.1).1 x.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    refine (ContMDiff.subtypeVal_comp_iff (pantsCircleCarrier.{u}.pieceInterior ⊤) _).1 ?_
    refine ((productAtlas.{u} 3).contMDiff_iff_subtype_val _).2 ?_
    exact (contMDiff_planeLift_up.comp (contMDiff_fst.comp contMDiff_subtype_val)).prodMk
      (contMDiff_snd.comp contMDiff_subtype_val)
  contMDiff_invFun := by
    refine (ContMDiff.subtypeVal_comp_iff pantsImage _).1 ?_
    have hval : ContMDiff pantsCircleCarrier.{u}.model (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞
        (fun x : pantsCircleCarrier.{u}.Carrier =>
          @Subtype.val (PlaneLift.{u} × Circle) (· ∈ productSet.{u} 3) x) :=
      (productAtlas.{u} 3).contMDiff_subtype_val
    have hv := hval.comp (contMDiff_subtype_val (U := pantsCircleCarrier.{u}.pieceInterior ⊤))
    exact (contMDiff_planeLift_down.comp (contMDiff_fst.comp hv)).prodMk (contMDiff_snd.comp hv)

def pantsCircleInteriorDiffeo (h : PantsQuotientDiffeo) :
    pantsCircleCarrier.{u}.pieceInterior ⊤ ≃ₘ⟮pantsCircleCarrier.{u}.model, 𝓡 3⟯
      PantsQuotient :=
  pantsInteriorEquiv.symm.trans h.some.symm

def productPantsInteriorGeometry (h : PantsQuotientDiffeo) :
    pantsCircleCarrier.{u}.InteriorGeometry ⊤ :=
  interiorGeometryOfDiffeomorph pantsQuotientGeometry pantsCircleCarrier.{u} ⊤
    (pantsCircleInteriorDiffeo h)

theorem productPantsInteriorGeometry_model (h : PantsQuotientDiffeo) :
    letI := DifferentialGeometry.Manifold.interiorChartedSpace pantsCircleCarrier.{u}.model ∞
      (M := pantsCircleCarrier.{u}.pieceInterior ⊤)
    letI := DifferentialGeometry.Manifold.interiorIsManifold pantsCircleCarrier.{u}.model ∞
      (M := pantsCircleCarrier.{u}.pieceInterior ⊤)
    (productPantsInteriorGeometry h).model = ThurstonModel.hyperbolicProduct :=
  rfl

section Piece

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {i : Fin T.components.count}
  {k : ℕ}

def ProductFibredPiece.pantsInteriorDiffeo (P : ProductFibredPiece T i k) (hk : k = 3)
    (h : PantsQuotientDiffeo) :
    T.cutCarrier.pieceInterior (T.components.piece i) ≃ₘ⟮T.cutCarrier.model, 𝓡 3⟯
      PantsQuotient := by
  subst hk
  exact (pieceInteriorCongr (P.pieceDiffeomorph pantsCirclePiece.{u})).trans
    (pantsCircleInteriorDiffeo h)

def ProductFibredPiece.pantsInteriorGeometry (P : ProductFibredPiece T i k) (hk : k = 3)
    (h : PantsQuotientDiffeo) : T.cutCarrier.InteriorGeometry (T.components.piece i) :=
  interiorGeometryOfDiffeomorph pantsQuotientGeometry _ _ (P.pantsInteriorDiffeo hk h)

theorem ProductFibredPiece.pantsInteriorGeometry_model (P : ProductFibredPiece T i k)
    (hk : k = 3) (h : PantsQuotientDiffeo) :
    letI := DifferentialGeometry.Manifold.interiorChartedSpace T.cutCarrier.model ∞
      (M := T.cutCarrier.pieceInterior (T.components.piece i))
    letI := DifferentialGeometry.Manifold.interiorIsManifold T.cutCarrier.model ∞
      (M := T.cutCarrier.pieceInterior (T.components.piece i))
    (P.pantsInteriorGeometry hk h).model = ThurstonModel.hyperbolicProduct :=
  rfl

end Piece

def pantsBlockInteriorGeometry {W : CompactCarrier.{u}} {d : SeifertData} (B : SeifertBlock W d)
    (hk : d.k = 3) (h : PantsQuotientDiffeo) :
    B.presentation.cutCarrier.InteriorGeometry (B.presentation.components.piece (B.piece none)) :=
  B.product.pantsInteriorGeometry hk h

theorem pantsBlockInteriorGeometry_model {W : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d) (hk : d.k = 3) (h : PantsQuotientDiffeo) :
    letI := DifferentialGeometry.Manifold.interiorChartedSpace B.presentation.cutCarrier.model ∞
      (M := B.presentation.cutCarrier.pieceInterior
        (B.presentation.components.piece (B.piece none)))
    letI := DifferentialGeometry.Manifold.interiorIsManifold B.presentation.cutCarrier.model ∞
      (M := B.presentation.cutCarrier.pieceInterior
        (B.presentation.components.piece (B.piece none)))
    (pantsBlockInteriorGeometry B hk h).model = ThurstonModel.hyperbolicProduct :=
  rfl

def FilledPantsBlockGeometry : Prop :=
  ∀ (W : CompactCarrier.{u}) (d : SeifertData) (B : SeifertBlock W d), d.k = 3 →
    0 < d.fillingCount → ∀ (hopen : 0 < d.ports) (hgood : ¬ d.IsSolidTorus), B.IsGoodBlock →
      d.openModelOf hopen hgood = .hyperbolicProduct →
        ∃ G : W.InteriorGeometry ⊤,
          letI := DifferentialGeometry.Manifold.interiorChartedSpace W.model ∞
            (M := W.pieceInterior ⊤)
          letI := DifferentialGeometry.Manifold.interiorIsManifold W.model ∞
            (M := W.pieceInterior ⊤)
          G.model = ThurstonModel.hyperbolicProduct

end GC.Seifert

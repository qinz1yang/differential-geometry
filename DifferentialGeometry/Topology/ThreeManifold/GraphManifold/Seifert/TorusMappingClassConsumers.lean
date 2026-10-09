import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClassProof
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeProof
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveAbsorbProof
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryEuclideanTwisted
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.UnionGeometryDispatch
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingEquivalence
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedFinal
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveTerminalProof

/-!
# Unconditional forms of the consumers of `TorusMappingClassLinear`

Lane TMLW. `torusMappingClassLinear_holds` (`Seifert/TorusMappingClassProof.lean`) proves K08's
named input `TorusMappingClassLinear`. Every theorem that took it as the hypothesis `hT`/`hL` is
restated here without that hypothesis and proved by the original theorem applied to the witness;
the consumers themselves are untouched. Groups: the merge move `moveMerge_unconditional`
(chapter 5 move M1; S2 of the sorry ledger is
`exists_complexity_one_of_selfSeam_redundant_unconditional`), Codex X9/X10
(`Seifert/FillingProduct*.lean`, `MoveMergeProduct.lean`, `MoveMergeSelfSeam.lean`),
X13 block charts, X26's twisted I-bundle wrapper, X30's open-block dispatch, X23's filling
equivalence, LS's linear seams, K08's `isotopic_iff_torusMatrix_eq`, and the normalisation line of
`Seifert/Normalize.lean`, which now needs only `MoveSplit` and `MoveTerminal`.
`progress_of_split_of_terminal_modulo_N4` (also under its older name `…_modulo_R1`) feeds it
N2c's `moveSplit` and `moveTerminal'`; since R1 is closed (Codex X22) its only `sorryAx` comes
through the ledger item N4 (`exists_sideData`); these two are the only such theorems of this file.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology

universe u v

namespace GC.Seifert

theorem isotopic_iff_torusMatrix_eq_unconditional
    {φ ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus} :
    IsotopicDiffeomorph φ ψ ↔ torusMatrix φ = torusMatrix ψ :=
  isotopic_iff_torusMatrix_eq torusMappingClassLinear_holds

theorem moveMerge_unconditional : MoveMerge.{u} :=
  moveMerge' torusMappingClassLinear_holds

theorem progress_of_split_of_terminal (hS : MoveSplit.{u}) (hT : MoveTerminal.{u}) :
    Progress.{u} :=
  progress_of_moves moveMerge_unconditional hS moveAbsorb hT

theorem seifertRefinement_of_elementarizeClosed_of_split_of_terminal
    (hE : ElementarizeClosed.{u}) (hS : MoveSplit.{u}) (hT : MoveTerminal.{u}) :
    SeifertRefinement.{u} :=
  seifertRefinement_of_elementarizeClosed_of_progress hE (progress_of_split_of_terminal hS hT)

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}}

theorem exists_hasLinearSeams_unconditional (E : ElementaryPresentation W) :
    ∃ (E' : ElementaryPresentation W)
      (hc : E'.toTorus.pairing.count = E.toTorus.pairing.count)
      (hp : E'.toTorus.components.count = E.toTorus.components.count),
      E'.HasLinearSeams ∧ E'.toTorus.cutCarrier = E.toTorus.cutCarrier ∧
      E'.complexity = E.complexity ∧
      (∀ i, E'.kind i = E.kind (Fin.cast hp i)) ∧
      (∀ j, Fin.cast hp (E'.toTorus.leftPiece j) = E.toTorus.leftPiece (Fin.cast hc j)) ∧
      (∀ j, Fin.cast hp (E'.toTorus.rightPiece j) = E.toTorus.rightPiece (Fin.cast hc j)) ∧
      (∀ j, torusUnit (E'.toTorus.pairing.matching j) =
        torusUnit (E.toTorus.pairing.matching (Fin.cast hc j))) ∧
      (∀ j b, E'.fillingDistance j b = E.fillingDistance (Fin.cast hc j) b) ∧
      ∀ j, (E'.toTorus.seam j).target = (E.toTorus.seam (Fin.cast hc j)).target :=
  E.exists_hasLinearSeams torusMappingClassLinear_holds

variable {Q : ConnectedClosedOrientedManifold.{u} 3}

theorem exists_solidExtension_of_meridianStabilizer_unconditional
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hf : torusUnit f • meridianSlope = meridianSlope) :
    ∃ D : (UnitDisc.{0} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), (𝓡∂ 2).prod (𝓡 1)⟯
        UnitDisc.{0} × Circle,
      ∀ t v : Circle, D (fillingDiscBoundary t, v) =
        (fillingDiscBoundary (f (t, v)).1, (f (t, v)).2) :=
  exists_solidExtension_of_meridianStabilizer torusMappingClassLinear_holds f hf

theorem exists_fillingSelectedCharts_unconditional
    (E : ElementaryPresentation (NoCuts.carrier Q)) (j : Fin E.toTorus.pairing.count)
    (b : Bool) (h : E.IsMergeSeam j b) (hk3 : E.kind (E.hostPiece j b) = 3) :
    ∃ q : ℤ, E.mergeSlope j b = Merge.sectionSlope q ∧
      Nonempty (SeifertBlockCharts (fillingProductCarrier E j) (selectedNormalData q)) :=
  exists_fillingSelectedCharts torusMappingClassLinear_holds E j b h hk3

theorem fillingProductCarrier_linearize_unconditional
    (E : ElementaryPresentation (NoCuts.carrier Q)) (j : Fin E.toTorus.pairing.count) :
    fillingProductCarrier (E.linearize torusMappingClassLinear_holds) j =
      fillingProductCarrier E j :=
  E.fillingProductCarrier_linearize torusMappingClassLinear_holds j

theorem exists_fillingProductDiffeomorph_unconditional
    (E : ElementaryPresentation (NoCuts.carrier Q)) (j : Fin E.toTorus.pairing.count)
    (b : Bool) (h : E.IsMergeSeam j b) (hk3 : E.kind (E.hostPiece j b) = 3) :
    Nonempty ((planarSet.{u} 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      (fillingProductCarrier E j).model⟯ (fillingProductCarrier E j).Carrier) :=
  exists_fillingProductDiffeomorph torusMappingClassLinear_holds E j b h hk3

theorem exists_fillingProduct_of_hostKind_eq_three_unconditional
    (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hk3 : E.kind (E.hostPiece j b) = 3) :
    ∃ B : PlanarBase.{u} 2, Nonempty
      ((B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
        (fillingProductCarrier E j).model⟯ (fillingProductCarrier E j).Carrier) :=
  E.exists_fillingProduct_of_hostKind_eq_three_of_torusMappingClassLinear
    torusMappingClassLinear_holds j b h hk3

theorem exists_planarBase_diffeomorph_merge_unconditional
    (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hf : E.HostSelfSeamFree j b) :
    ∃ B : PlanarBase.{u} (E.kind (E.hostPiece j b) - 1), Nonempty
      ((B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
        (E.mergeContraction j b h hf
          (TorusPresentation.externalPiece_not_mem_of_closed _ _)).cutCarrier.model⟯
        (E.mergeContraction j b h hf
          (TorusPresentation.externalPiece_not_mem_of_closed _ _)).components.piece
        (E.mergeLast j b h hf (TorusPresentation.externalPiece_not_mem_of_closed _ _))) :=
  E.exists_planarBase_diffeomorph_merge_of_torusMappingClassLinear
    torusMappingClassLinear_holds j b h hf

theorem exists_merge_of_selfSeamFree_unconditional
    (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hf : E.HostSelfSeamFree j b) :
    ∃ E' : ElementaryPresentation (NoCuts.carrier Q),
      E'.complexity + 1 = E.complexity :=
  E.exists_merge_of_selfSeamFree_of_torusMappingClassLinear torusMappingClassLinear_holds j b h hf

theorem exists_complexity_one_of_selfSeam_core_unconditional
    (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (k : Fin E.toTorus.pairing.count)
    (hl : E.toTorus.leftPiece k = E.hostPiece j b)
    (hr : E.toTorus.rightPiece k = E.hostPiece j b) :
    ∃ E' : ElementaryPresentation (NoCuts.carrier Q), E'.complexity = 1 :=
  E.exists_complexity_one_of_selfSeam_core j b h k hl hr torusMappingClassLinear_holds

theorem exists_complexity_one_of_selfSeam_redundant_unconditional
    (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (k : Fin E.toTorus.pairing.count)
    (hl : E.toTorus.leftPiece k = E.hostPiece j b)
    (hr : E.toTorus.rightPiece k = E.hostPiece j b)
    (hH : E.kind (E.hostPiece j b) = 3) (hc : E.toTorus.components.count = 2)
    (hn : E.complexity = 2) :
    ∃ E' : ElementaryPresentation (NoCuts.carrier Q), E'.complexity = 1 :=
  E.exists_complexity_one_of_selfSeam_redundant j b h k hl hr hH hc hn
    torusMappingClassLinear_holds

end ElementaryPresentation

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData}

theorem exists_charts_unconditional (B : SeifertBlock W d) :
    Nonempty (SeifertBlockCharts W d) :=
  B.exists_charts torusMappingClassLinear_holds

theorem exists_closed_charts_unconditional (B : SeifertBlock W d) (h : d.ports = 0) :
    Nonempty (SeifertBlockCharts W d) :=
  B.exists_closed_charts torusMappingClassLinear_holds h

def twistedIBundleInteriorGeometry_unconditional (B : SeifertBlock W d) (q₁ q₂ : ℤ)
    (hports : d.ports = 1) (hcones : d.cones = [(2, q₁), (2, q₂)]) :
    W.InteriorGeometry ⊤ :=
  B.twistedIBundleInteriorGeometry torusMappingClassLinear_holds q₁ q₂ hports hcones

theorem twistedIBundleInteriorGeometry_model_unconditional (B : SeifertBlock W d) (q₁ q₂ : ℤ)
    (hports : d.ports = 1) (hcones : d.cones = [(2, q₁), (2, q₂)]) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (B.twistedIBundleInteriorGeometry_unconditional q₁ q₂ hports hcones).model =
      ThurstonModel.euclidean :=
  B.twistedIBundleInteriorGeometry_model torusMappingClassLinear_holds q₁ q₂ hports hcones

theorem exists_openInteriorGeometry_model_unconditional (B : SeifertBlock W d)
    (hB : B.IsGoodBlock) (hopen : 0 < d.ports) (hA : FilledPantsBlockGeometry.{u}) :
    ∃ G : W.InteriorGeometry ⊤,
      let := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
      let := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
      G.model = d.openGeometryModel :=
  B.exists_openInteriorGeometry_model hB hopen torusMappingClassLinear_holds hA

theorem exists_openInteriorGeometry_unconditional (B : SeifertBlock W d) (hB : B.IsGoodBlock)
    (hopen : 0 < d.ports) (hA : FilledPantsBlockGeometry.{u}) :
    Nonempty (W.InteriorGeometry ⊤) :=
  B.exists_openInteriorGeometry hB hopen torusMappingClassLinear_holds hA

def openInteriorGeometry_unconditional (B : SeifertBlock W d) (hB : B.IsGoodBlock)
    (hopen : 0 < d.ports) (hA : FilledPantsBlockGeometry.{u}) : W.InteriorGeometry ⊤ :=
  B.openInteriorGeometry hB hopen torusMappingClassLinear_holds hA

end SeifertBlock

namespace BlockedPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3}

def geometricDecomposition_of_positivePorts_unconditional
    (B : BlockedPresentation (NoCuts.carrier Q)) (hB : B.IsGood)
    (hp : ∀ i, 0 < (B.data i).ports) (hA : FilledPantsBlockGeometry.{u}) :
    GeometricDecomposition Q :=
  B.geometricDecomposition_of_positivePorts hB hp torusMappingClassLinear_holds hA

end BlockedPresentation

theorem goodBlockUnionGeometry_or_closedSmallBlock_unconditional
    (hA : FilledPantsBlockGeometry.{u}) (hC : ClosedTriangleBlockGeometry.{u})
    (Q : ConnectedClosedOrientedManifold.{u} 3) (hQ : GoodBlockUnion Q) :
    Nonempty (GeometricDecomposition Q) ∨
      ∃ d : SeifertData, d.ports = 0 ∧ d.cones.length ≤ 2 ∧
        Nonempty (SeifertBlock (NoCuts.carrier Q) d) :=
  goodBlockUnionGeometry_or_closedSmallBlock torusMappingClassLinear_holds hA hC Q hQ

theorem goodBlockUnionGeometry_unconditional (hA : FilledPantsBlockGeometry.{u})
    (hC : ClosedTriangleBlockGeometry.{u}) : GoodBlockUnionGeometry.{u} :=
  goodBlockUnionGeometry torusMappingClassLinear_holds hA hC

theorem exists_meridianPreserving_solidTorusDiffeomorph_unconditional
    (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hμ : torusUnit φ • meridianSlope = meridianSlope) :
    ∃ (F : solidTorusSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidTorusSet.{u}) (δ : ℝ),
      0 < δ ∧ δ ≤ 1 ∧ ∀ p ∈ halfCollarSource, p.2.val 0 < δ →
        F (solidTorusCollar p) = solidTorusCollar (φ p.1, p.2) :=
  exists_meridianPreserving_solidTorusDiffeomorph_of_mappingClassLinear
    torusMappingClassLinear_holds φ hμ

theorem SolidTorusPiece.exists_comparison_germ_unconditional
    {W : CompactCarrier.{u}} {T : TorusPresentation W} {i : Fin T.components.count}
    {V : CompactCarrier.{v}} {E : TorusPresentation V} {l : Fin E.components.count}
    (P : SolidTorusPiece T i) (Q : SolidTorusPiece E l)
    (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hμ : torusUnit φ • meridianSlope = meridianSlope) :
    ∃ δ > (0 : ℝ), ∃ H : T.components.piece i ≃ₘ⟮T.cutCarrier.model, E.cutCarrier.model⟯
      E.components.piece l,
      ∀ p ∈ halfCollarSource, p.2.val 0 < δ →
        H (T.pieceCollar i (P.port 0) p) = E.pieceCollar l (Q.port 0) (φ p.1, p.2) :=
  P.exists_comparison_germ_of_mappingClassLinear torusMappingClassLinear_holds Q φ hμ

theorem exists_primitiveFillingComparison_unconditional
    {W W' : CompactCarrier.{u}} {n r : ℕ}
    (B : PrimitiveFillingPresentation W n r) (B' : PrimitiveFillingPresentation W' n r)
    (ψ : Fin r ⊕ Fin n → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (h : B.presentation.components.piece (B.piece none) ≃ₘ⟮B.presentation.cutCarrier.model,
      B'.presentation.cutCarrier.model⟯
        B'.presentation.components.piece (B'.piece none))
    (ho : h.preservesOrientation
      (B.presentation.cutCarrier.orientation.restrictOpen
        (B.presentation.components.piece (B.piece none)))
      (B'.presentation.cutCarrier.orientation.restrictOpen
        (B'.presentation.components.piece (B'.piece none))))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1)
    (hgerm : ∀ a p, p ∈ halfCollarSource → p.2.val 0 < δ₀ →
      h (B.presentation.pieceCollar (B.piece none) (B.product.port (B.port a)) p) =
        B'.presentation.pieceCollar (B'.piece none) (B'.product.port (B'.port a))
          (ψ a p.1, p.2))
    (hslope : ∀ m, torusUnit (ψ (.inr m)) • B.slope m = B'.slope m) :
    ∃ (δ : ℝ), 0 < δ ∧ δ ≤ 1 ∧
      ∃ (H : B.presentation.cutCarrier.Carrier ≃ₘ⟮B.presentation.cutCarrier.model,
          B'.presentation.cutCarrier.model⟯
            B'.presentation.cutCarrier.Carrier)
        (F : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
        (q : B.presentation.pairing.QuotientSpace ≃ₜ B'.presentation.pairing.QuotientSpace),
      F.preservesOrientation W.orientation W'.orientation ∧
      (∀ x : B.presentation.components.piece (B.piece none), H x.val = (h x).val) ∧
      (∀ i : Option (Fin n), H '' (B.presentation.components.piece (B.piece i) : Set _) =
        (B'.presentation.components.piece (B'.piece i) : Set _)) ∧
      (∀ m p, p ∈ halfCollarSource → p.2.val 0 < δ →
        H (B.presentation.pairing.leftCollar (B.seam m) p) =
          B'.presentation.pairing.leftCollar (B'.seam m)
            (primitiveFillingCorrection (B.presentation.pairing.matching (B.seam m))
              (B'.presentation.pairing.matching (B'.seam m)) (ψ (.inr m)) p.1, p.2)) ∧
      (∀ x, q (B.presentation.pairing.quotientMap x) =
        B'.presentation.pairing.quotientMap (H x)) ∧
      (∀ z, F (B.presentation.reconstruction z) = B'.presentation.reconstruction (q z)) ∧
      (∀ a p, p ∈ halfCollarSource → p.2.val 0 < δ →
        F (B.presentation.external.collar (B.free a) p) =
          B'.presentation.external.collar (B'.free a) (ψ (.inl a) p.1, p.2)) :=
  exists_primitiveFillingComparison_of_mappingClassLinear torusMappingClassLinear_holds
    B B' ψ h ho δ₀ hδ₀ hδ₀1 hgerm hslope

theorem exists_collarFillingDiffeomorph_unconditional
    {W W' : CompactCarrier.{u}} {d : SeifertData}
    (B : SeifertBlock W d) (B' : SeifertBlock W' d) (hport : B.port = B'.port)
    (ho : (B.product.pieceDiffeomorph B'.product).preservesOrientation
      (B.presentation.cutCarrier.orientation.restrictOpen
        (B.presentation.components.piece (B.piece none)))
      (B'.presentation.cutCarrier.orientation.restrictOpen
        (B'.presentation.components.piece (B'.piece none)))) :
    ∃ F : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier,
      F.preservesOrientation W.orientation W'.orientation ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
        ∀ r p, p ∈ halfCollarSource → p.2.val 0 < δ →
          F (B.presentation.external.collar (B.free r) p) =
            B'.presentation.external.collar (B'.free r) p :=
  exists_collarFillingDiffeomorph_of_mappingClassLinear torusMappingClassLinear_holds
    B B' hport ho

end GC.Seifert

import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Carrier
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.RegularSublevelAtlas

/-!
# Chapter-14 assembly: the piece types `PieceFold` and `PieceEmbedding`

The per-piece fields of `EmbeddedCutSystem` (`Seifert/EmbeddedPieces.lean:263–273`), as frozen in the
chapter-14 assembly design (`docs/geometrization/chapter14/design-fc39-fc42-assembly-20261004.md`, §0
decision 2, §4 row §1). The two structures are copied verbatim from the frozen interface file; the
bridge statements B1 (`AssemblySublevelPieces.lean`, `AssemblyInteriorSublevel.lean`) produce
`PieceEmbedding`s, and the later certificate and producer modules import this file.

Besides the two structures: continuity and compactness of the image, the pulled-back orientation
`PieceFold.pullbackOrientation` (the per-piece form of `EmbeddedCutSystem.cutOrientation`), and for
an injective piece the closed embedding `PieceEmbedding.isClosedEmbedding_map` and the
homeomorphism onto the image.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry GC.Endpoint Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- An actual compact piece mapped into `W` (the `EmbeddedCutSystem` piece fields,
`Seifert/EmbeddedPieces.lean:263–273`). Not necessarily injective: a piece cut open along a
self-seam folds two boundary copies onto one torus. Its orientation is the pullback
(`EmbeddedCutSystem.cutOrientation`, `:327`), so none is stored. -/
structure PieceFold (W : CompactCarrier.{u}) where
  Piece : Type u
  [topology : TopologicalSpace Piece]
  [charts : ChartedSpace (EuclideanHalfSpace 3) Piece]
  [manifold : IsManifold (𝓡∂ 3) ∞ Piece]
  [compact : CompactSpace Piece]
  [hausdorff : T2Space Piece]
  [secondCountable : SecondCountableTopology Piece]
  [connected : ConnectedSpace Piece]
  map : Piece → W.Carrier
  smooth : ContMDiff (𝓡∂ 3) W.model ∞ map
  mfderiv_bijective : ∀ q, Bijective (mfderiv (𝓡∂ 3) W.model map q)

attribute [instance] PieceFold.topology PieceFold.charts PieceFold.manifold PieceFold.compact
  PieceFold.hausdorff PieceFold.secondCountable PieceFold.connected

/-- An injective piece: the B1 output for one connected component of a regular domain. -/
structure PieceEmbedding (W : CompactCarrier.{u}) extends PieceFold W where
  injective : Injective map

namespace PieceFold

variable {W : CompactCarrier.{u}} (P : PieceFold W)

theorem continuous_map : Continuous P.map :=
  P.smooth.continuous

theorem mdifferentiable_map : MDifferentiable (𝓡∂ 3) W.model P.map :=
  P.smooth.mdifferentiable (by simp)

theorem isCompact_range : IsCompact (range P.map) :=
  _root_.isCompact_range P.continuous_map

theorem isClosed_range : IsClosed (range P.map) :=
  P.isCompact_range.isClosed

theorem isConnected_range : IsConnected (range P.map) :=
  _root_.isConnected_range P.continuous_map

theorem range_nonempty : (range P.map).Nonempty :=
  Set.range_nonempty P.map

/-- The orientation of `W` pulled back along the piece map (the per-piece form of
`EmbeddedCutSystem.cutOrientation`, `Seifert/EmbeddedPieces.lean:327`). -/
def pullbackOrientation : ManifoldOrientation (𝓡∂ 3) P.Piece 3 :=
  DifferentialGeometry.Topology.Manifold.manifoldOrientationPullback (𝓡∂ 3) W.model
    finrank_euclideanSpace_fin P.map P.smooth P.mfderiv_bijective W.orientation

/-- The differential of the piece map carries the pulled-back orientation to that of `W`. -/
theorem orientation_map_pullbackOrientation (q : P.Piece) :
    Orientation.map (Fin 3)
      (DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective (𝓡∂ 3) W.model P.map
        P.mfderiv_bijective q).toLinearEquiv (P.pullbackOrientation.orientation q) =
      W.orientation.orientation (P.map q) :=
  DifferentialGeometry.Topology.Manifold.orientation_map_manifoldOrientationPullback (𝓡∂ 3)
    W.model finrank_euclideanSpace_fin P.map P.smooth P.mfderiv_bijective W.orientation q

end PieceFold

namespace PieceEmbedding

variable {W : CompactCarrier.{u}} (P : PieceEmbedding W)

theorem isClosedEmbedding_map : Topology.IsClosedEmbedding P.map :=
  P.continuous_map.isClosedEmbedding P.injective

/-- An injective piece is homeomorphic to its image. -/
def homeomorphRange : P.Piece ≃ₜ range P.map :=
  P.isClosedEmbedding_map.isEmbedding.toHomeomorph

theorem homeomorphRange_apply (q : P.Piece) : (P.homeomorphRange q : W.Carrier) = P.map q :=
  rfl

end PieceEmbedding

end GC.GraphManifold.Assembly

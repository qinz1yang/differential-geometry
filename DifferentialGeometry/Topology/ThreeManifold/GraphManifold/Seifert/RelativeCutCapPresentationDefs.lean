import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.EmbeddedPieces
import DifferentialGeometry.Topology.ThreeManifold.CutCap

/-!
# The actual output ledger of a controlled cut and cap

All presentations live on components of the actual capped carrier. Original seam maps are
recorded only on their source. Piece origins need not be injective and are constrained only
where the new piece meets the retained core. Uncut compact maps record orientation separately.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert

structure CappedMixedRefinement {M : ConnectedClosedOrientedManifold.{u} 3}
    {Q : ClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier M))
    (X : SphericalCutCapTransition M.toClosedOrientedManifold Q)
    (graphPieces : Finset (Fin T.components.count)) where
  presentation : ∀ c : ConnectedComponents X.capped.Carrier,
    TorusPresentation (NoCuts.carrier (X.capped.component c))
  pieces : ∀ c (i : Fin (presentation c).components.count),
    (∃ g : ((presentation c).cutCarrier).InteriorGeometry ((presentation c).components.piece i),
      letI := Manifold.interiorChartedSpace ((presentation c).cutCarrier).model ∞
        (M := ((presentation c).cutCarrier).pieceInterior ((presentation c).components.piece i))
      letI := Manifold.interiorIsManifold ((presentation c).cutCarrier).model ∞
        (M := ((presentation c).cutCarrier).pieceInterior ((presentation c).components.piece i))
      g.model = .hyperbolic) ∨
      Nonempty (RawGraphPresentation
        (componentCarrier (presentation c).cutCarrier (presentation c).components i))
  marked : Fin T.pairing.count → Σ c, Fin (presentation c).pairing.count
  marked_injective : Function.Injective marked
  marked_matching : ∀ j,
    (presentation (marked j).1).pairing.matching (marked j).2 = T.pairing.matching j
  marked_collar : ∀ j p, p ∈ signedCollarSource → ∃ x : X.tubes.core,
    x.val = T.seam j p ∧ X.capping.coreInclusion x =
      ((presentation (marked j).1).seam (marked j).2 p).val

  origin : ∀ c, Fin (presentation c).components.count → Fin T.components.count
  retained_origin : ∀ c k (z : (presentation c).components.piece k) (x : X.tubes.core),
    ((presentation c).cutMap z).val = X.capping.coreInclusion x →
      x.val ∈ T.cutMap '' (T.components.piece (origin c k) : Set T.cutCarrier.Carrier)
  uncut : {i : Fin T.components.count // i ∉ graphPieces} →
    Σ c, Fin (presentation c).components.count
  uncut_injective : Function.Injective uncut
  uncut_origin : ∀ i, origin (uncut i).1 (uncut i).2 = i.val
  uncutDiffeomorph : ∀ i,
    (componentCarrier T.cutCarrier T.components i.val).Carrier ≃ₘ⟮
      (componentCarrier T.cutCarrier T.components i.val).model,
      (componentCarrier (presentation (uncut i).1).cutCarrier
        (presentation (uncut i).1).components (uncut i).2).model⟯
      (componentCarrier (presentation (uncut i).1).cutCarrier
        (presentation (uncut i).1).components (uncut i).2).Carrier
  uncut_oriented : ∀ i, (uncutDiffeomorph i).preservesOrientation
    (componentCarrier T.cutCarrier T.components i.val).orientation
    (componentCarrier (presentation (uncut i).1).cutCarrier
      (presentation (uncut i).1).components (uncut i).2).orientation
  uncut_map : ∀ i (x : (componentCarrier T.cutCarrier T.components i.val).Carrier),
    ∃ y : X.tubes.core, y.val = T.cutMap x.val ∧ X.capping.coreInclusion y =
      ((presentation (uncut i).1).cutMap (uncutDiffeomorph i x).val).val


end GC.Seifert

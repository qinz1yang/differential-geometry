import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyEdgeCircleSolidTorus

/-!
# Consumer of D2S1: the piece-to-solid-torus direction

The inverse of the D2S1 diffeomorphism: the piece of a circle-fibred edge piece maps
diffeomorphically onto the standard solid torus.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The piece of a circle-fibred edge piece is diffeomorphic to the standard solid torus. -/
theorem nonempty_edgeCirclePiece_diffeomorph_solidTorus {W : CompactCarrier.{u}}
    (P : EdgeCirclePiece W) :
    Nonempty (P.piece.Piece ≃ₘ⟮𝓡∂ 3, solidTorusCarrier.{u}.model⟯
      solidTorusCarrier.{u}.Carrier) :=
  (exists_solidTorus_of_edgeCirclePiece P).map Diffeomorph.symm

end GC.GraphManifold.Assembly

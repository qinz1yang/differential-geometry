import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.EmbeddedPieces

/-!
# Consumer of `PieceFold`: the pieces of a tree cut system

Every piece of an `EmbeddedCutSystem W .withBoundary` (`Seifert/EmbeddedPieces.lean:260`) is a
`PieceFold W` with the same map; the images of the pieces cover `W`, and the union of the images
of any finite family of pieces is closed.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry GC.Endpoint GC.Seifert Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

variable {W : CompactCarrier.{u}}

/-- The `j`-th piece of a tree cut system (kind `withBoundary`) as a `PieceFold`. -/
def pieceFoldOfCutSystem (S : EmbeddedCutSystem W .withBoundary) (j : Fin S.count) :
    PieceFold W where
  Piece := S.Piece j
  charts := S.charts j
  manifold := S.manifold j
  compact := S.compact j
  hausdorff := S.hausdorff j
  secondCountable := S.secondCountable j
  connected := S.connected j
  map := S.map j
  smooth := S.smooth j
  mfderiv_bijective := S.mfderiv_bijective j

theorem pieceFoldOfCutSystem_map (S : EmbeddedCutSystem W .withBoundary) (j : Fin S.count) :
    (pieceFoldOfCutSystem S j).map = S.map j :=
  rfl

theorem iUnion_range_pieceFoldOfCutSystem (S : EmbeddedCutSystem W .withBoundary) :
    ⋃ j, range (pieceFoldOfCutSystem S j).map = univ :=
  S.covers

/-- The union of the images of finitely many pieces is closed. -/
theorem isClosed_iUnion_range_pieceFold {m : ℕ} (P : Fin m → PieceFold W) :
    IsClosed (⋃ k, range (P k).map) :=
  isClosed_iUnion_of_finite fun k => (P k).isClosed_range

end GC.GraphManifold.Assembly

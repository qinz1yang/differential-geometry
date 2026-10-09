import DifferentialGeometry.Geometry.Collapse.CutPieceBallsCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutGeometry

/-!
# Consumer: ball tests on the pieces of a late cut family (A7 CPI)

The consumer of A7 is adapter 3 of the merged WBD design
(`docs/geometrization/chapter13/design-wbd-merged-20261004.md` §6): the ball tests in
`LateCutFamily.hasEventualDerivativeBounds` (`Geometry/Flow/RicciFlow/LongTime/LateCutGeometry.lean`)
are stated for the piece metric `L.metric j C i` of a piece of the actual torus decomposition
`L.decomposition j C` of a component of the late slice, and that metric is induced by the
normalized slice metric (`L.induced j C i`). For an arbitrary `L` (no extra buffers chosen during
a construction), the results below read the test on a ball whose radius is below the boundary
distance in the ambient slice metric:

* `cutPiece_ball_tests`: the intrinsic ball is the ambient ball about the image point, the strict
  test `r < R_p` is the same test for the ambient curvature scale, the ball volumes agree, and the
  curvature derivative norms agree pointwise on the ball;
* `cutPiece_curvatureDerivativeNorm_le_of_ambient`: ambient derivative bounds on the ambient ball
  give the same bounds on the intrinsic ball;
* `cutPiece_curvatureRadius_eq_of_lt`: a piece curvature scale below the boundary distance is the
  ambient curvature scale of the slice component at the image point.

Collar estimates near the boundary (adapter 2) are not part of this lane.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open GC.Endpoint GC.Topology Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.LateCutFamily

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
  {F : GC.Interface.RawSurgery P g} {K : ℕ} {slices : ℕ → RegularSlice F.observation}

/-- Adapter 3, ball part, for an arbitrary late cut family: below the boundary distance of the
piece, the intrinsic ball is the ambient ball of the normalized slice component, the strict
curvature-scale test, the ball volume and the curvature derivative norms are those of the slice
component at the image points. -/
theorem cutPiece_ball_tests (L : LateCutFamily F K slices) (j : ℕ)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (i : Fin (L.decomposition j C).components.count)
    (p : ((L.decomposition j C).component i).Carrier) {r : ℝ}
    (hd : ENNReal.ofReal r <
      distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p) :
    cutPieceMap (L.decomposition j C) i '' riemannianBallOf (L.metric j C i) p r =
        riemannianBallOf ((slices j).componentMetric C) (cutPieceMap (L.decomposition j C) i p) r ∧
      (ENNReal.ofReal r < curvatureRadius (L.metric j C i) p ↔
        ENNReal.ofReal r <
          curvatureRadius ((slices j).componentMetric C) (cutPieceMap (L.decomposition j C) i p)) ∧
      ballVolume (L.metric j C i) p r =
        ballVolume ((slices j).componentMetric C) (cutPieceMap (L.decomposition j C) i p) r ∧
      ∀ k : ℕ, ∀ q ∈ riemannianBallOf (L.metric j C i) p r,
        curvatureDerivativeNorm (L.metric j C i) k q =
          curvatureDerivativeNorm ((slices j).componentMetric C) k
            (cutPieceMap (L.decomposition j C) i q) :=
  ⟨image_cutPieceMap_riemannianBallOf _ _ i _ (L.induced j C i) hd.le,
    ofReal_lt_curvatureRadius_cutPieceMap_iff _ _ (L.induced j C i) hd,
    ballVolume_cutPieceMap_of_le _ _ i _ (L.induced j C i) hd.le,
    fun k _ hq => curvatureDerivativeNorm_cutPieceMap_of_mem_ball _ _ i _ (L.induced j C i) k hd.le hq⟩

/-- Ambient derivative bounds on the ambient ball give the same bounds on the intrinsic ball of a
late piece, below the boundary distance. -/
theorem cutPiece_curvatureDerivativeNorm_le_of_ambient (L : LateCutFamily F K slices) (j : ℕ)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (i : Fin (L.decomposition j C).components.count)
    (p : ((L.decomposition j C).component i).Carrier) {r : ℝ}
    (hd : ENNReal.ofReal r ≤
      distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p)
    (k : ℕ) {B : ℝ}
    (hamb : ∀ y ∈ riemannianBallOf ((slices j).componentMetric C)
        (cutPieceMap (L.decomposition j C) i p) r,
      curvatureDerivativeNorm ((slices j).componentMetric C) k y ≤ B) :
    ∀ q ∈ riemannianBallOf (L.metric j C i) p r, curvatureDerivativeNorm (L.metric j C i) k q ≤ B := by
  intro q hq
  rw [curvatureDerivativeNorm_cutPieceMap_of_mem_ball _ _ i _ (L.induced j C i) k hd hq]
  apply hamb
  rw [← image_cutPieceMap_riemannianBallOf _ _ i _ (L.induced j C i) hd]
  exact mem_image_of_mem _ hq

/-- A curvature scale of a late piece below the boundary distance is the curvature scale of the
normalized slice component at the image point. -/
theorem cutPiece_curvatureRadius_eq_of_lt (L : LateCutFamily F K slices) (j : ℕ)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (i : Fin (L.decomposition j C).components.count)
    (p : ((L.decomposition j C).component i).Carrier)
    (hlt : curvatureRadius (L.metric j C i) p <
      distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p) :
    curvatureRadius ((slices j).componentMetric C) (cutPieceMap (L.decomposition j C) i p) =
      curvatureRadius (L.metric j C i) p :=
  curvatureRadius_cutPieceMap_eq_of_lt _ _ i _ (L.induced j C i) hlt

end GC.LongTime.LateCutFamily

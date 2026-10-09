import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCapBall
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierDiffeomorphTransport
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Sphere

/-!
# Consumers of packet S3a, ball case (lane ASM-SPH)

* `DecompositionCertificate.nonempty_rawGraphPresentation_component_of_ball`: B4's first branch for
  a ball side — the component of the capped carrier containing the cap of a ball side of the cut
  seam has a raw graph presentation (it is `S³`: the two-solid-torus presentation
  `standardThreeSphereLiftRawGraphPresentation` carried along the diffeomorphism).
* `SphereCutCapped.exists_capUnion_sphere`: the X-level form, for any piece on one side of the seam
  that is a closed ball with the seam sphere as boundary and contains the half collar of its side.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballChartsCapBallApp_ASMSPH : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothCapBallApp_ASMSPH : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance sphereDimFourCapBallApp_ASMSPH :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by simp⟩

/-- **X-level: a ball side and its cap are `S³`.** -/
theorem SphereCutCapped.exists_capUnion_sphere {W : CompactCarrier.{u}} {S : SphereSeam W}
    {n : ℕ} {E : BoundaryTori W n} (X : SphereCutCapped W S E) (P : PieceEmbedding W) (j : Fin 2)
    (hside : ∀ q p, p ∈ S.collar.source → P.map q = S.collar p → 0 ≤ cutSideSign j * p.2)
    (e : P.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (hbd : P.map '' (𝓡∂ 3).boundary P.Piece = S.zeroSphere)
    (hhalf : ∀ z s, 0 ≤ s → s < 1 → S.collar (z, cutSideSign j * s) ∈ range P.map) :
    ∃ U : TopologicalSpace.Opens X.Q.Carrier,
      (U : Set X.Q.Carrier) = range (X.liftPiece P j hside).map ∪
        range (X.capping.cap (Fin.cast X.h2.symm j)) ∧
      IsCompact (U : Set X.Q.Carrier) ∧
      Nonempty (U ≃ₘ⟮X.Q.model, 𝓡 3⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  ⟨_, rfl, X.isCompact_capUnion P j hside,
    X.nonempty_capUnion_sphereDiffeomorph P j hside e hbd hhalf⟩

/-- **B4, first branch, ball side**: the capped component of a ball side is Raw. -/
theorem DecompositionCertificate.nonempty_rawGraphPresentation_component_of_ball
    {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
    (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E) (b : Bool)
    (hk : (D.vertex (D.sphereSide c b)).IsBall) (DQ : X.Q.Components) :
    Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ
      (X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b))))) := by
  obtain ⟨φ⟩ := D.componentCarrier_sphere_of_ball c X b hk DQ
  have := standardThreeSphereLift.{u}.connected
  exact nonempty_rawGraphPresentation_of_carrierDiffeomorph
    standardThreeSphereLiftRawGraphPresentation
    (standardThreeSphereLiftDiffeomorph.{u}.symm.trans φ.symm)

end GC.GraphManifold.Assembly

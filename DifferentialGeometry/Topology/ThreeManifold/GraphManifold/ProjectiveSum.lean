import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.ProjectiveLens

/-!
Raw connected sums with projective three-space accept arbitrary oriented ball charts on either
side through the actual chart diffeomorphism of the fixed oriented connected sum.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff

universe u

namespace GC.GraphManifold

theorem nonempty_rawGraphPresentation_smoothConnectedSum_projectiveThreeSpaceLift
    (M : ConnectedClosedOrientedManifold.{u} 3) (G : RawGraphPresentation (NoCuts.carrier M))
    (c₀ : OrientedBallChart M.toClosedOrientedManifold)
    (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold) :
    Nonempty (RawGraphPresentation (NoCuts.carrier
      (smoothConnectedSum M projectiveThreeSpaceLift.{u} c₀ c
        boundaryAttachment).toConnectedClosedOrientedManifold)) := by
  obtain ⟨R⟩ := rawGraphPresentation_connectedSum M projectiveThreeSpaceLift.{u} G
    projectiveThreeSpaceLensRawGraphPresentation.{u}
  exact rawGraphPresentation_of_diffeomorph R
    (fixedConnectedSumChartDiffeomorph M projectiveThreeSpaceLift.{u} c₀ c).symm


theorem nonempty_rawGraphPresentation_smoothConnectedSum_projectiveThreeSpaceLift_left
    (M : ConnectedClosedOrientedManifold.{u} 3) (G : RawGraphPresentation (NoCuts.carrier M))
    (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
    (c₀ : OrientedBallChart M.toClosedOrientedManifold) :
    Nonempty (RawGraphPresentation (NoCuts.carrier
      (smoothConnectedSum projectiveThreeSpaceLift.{u} M c c₀
        boundaryAttachment).toConnectedClosedOrientedManifold)) := by
  obtain ⟨R⟩ := rawGraphPresentation_connectedSum projectiveThreeSpaceLift.{u} M
    projectiveThreeSpaceLensRawGraphPresentation.{u} G
  exact rawGraphPresentation_of_diffeomorph R
    (fixedConnectedSumChartDiffeomorph projectiveThreeSpaceLift.{u} M c c₀).symm

end GC.GraphManifold

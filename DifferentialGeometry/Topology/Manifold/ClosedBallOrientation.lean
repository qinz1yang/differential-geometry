import DifferentialGeometry.Topology.Manifold.ScaledClosedBall
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Ball (L : ℝ) := {x : E3 // ‖x‖ ≤ L}

theorem closedBall_inclusion_mfderiv_bijective {L : ℝ} (hL : 0 < L) (x : Ball L) :
    letI := closedBallChartedSpace hL
    Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Ball L → E3) x) := by
  let := closedBallChartedSpace hL
  exact bijective_mfderiv_of_isImmersionAt (𝓡∂ 3) (𝓡 3) _ x
    ((isSmoothEmbedding_closedBall_inclusion hL).isImmersion.isImmersionAt x) rfl

def closedBallSmoothOrientation {L : ℝ} (hL : 0 < L)
    (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    SmoothOrientation (𝓡∂ 3) (Ball L) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact pullbackSmoothOrientation (𝓡∂ 3) (𝓡 3) (Subtype.val : Ball L → E3)
    (isSmoothEmbedding_closedBall_inclusion hL).contMDiff
    (closedBall_inclusion_mfderiv_bijective hL) (euclideanSmoothOrientation E3 o)

theorem closedBallSmoothOrientation_pushforward {L : ℝ} (hL : 0 < L)
    (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) (x : Ball L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    tangentOrientationEquiv (differentialEquivOfBijective (𝓡∂ 3) (𝓡 3)
      (Subtype.val : Ball L → E3) (closedBall_inclusion_mfderiv_bijective hL) x).toLinearEquiv
        ((closedBallSmoothOrientation hL o).val x) = o := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact pullbackSmoothOrientation_pushforward (𝓡∂ 3) (𝓡 3) (Subtype.val : Ball L → E3)
    (isSmoothEmbedding_closedBall_inclusion hL).contMDiff
    (closedBall_inclusion_mfderiv_bijective hL) (euclideanSmoothOrientation E3 o) x
end DifferentialGeometry.Topology.Manifold

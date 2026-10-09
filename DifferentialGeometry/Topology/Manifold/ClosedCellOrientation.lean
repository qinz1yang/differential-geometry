import DifferentialGeometry.Topology.Manifold.ClosedBall
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem closedCell_inclusion_mfderiv_bijective (m : ℕ) (x : ClosedCell (m + 1)) :
    Function.Bijective (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1))
      (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) x) :=
  bijective_mfderiv_of_isImmersionAt (𝓡∂ (m + 1)) (𝓡 (m + 1)) _ x
    ((isSmoothEmbedding_closedCell_inclusion m).isImmersion.isImmersionAt x) rfl

def closedCellSmoothOrientation (m : ℕ)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin (m + 1)))
      (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1)))))) :
    SmoothOrientation (𝓡∂ (m + 1)) (ClosedCell (m + 1)) :=
  pullbackSmoothOrientation (𝓡∂ (m + 1)) (𝓡 (m + 1)) Subtype.val
    (isSmoothEmbedding_closedCell_inclusion m).contMDiff
    (closedCell_inclusion_mfderiv_bijective m)
    (euclideanSmoothOrientation (EuclideanSpace ℝ (Fin (m + 1))) o)

theorem closedCellSmoothOrientation_pushforward (m : ℕ)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin (m + 1)))
      (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))))))
    (x : ClosedCell (m + 1)) :
    tangentOrientationEquiv (differentialEquivOfBijective (𝓡∂ (m + 1)) (𝓡 (m + 1))
      Subtype.val (closedCell_inclusion_mfderiv_bijective m) x).toLinearEquiv
        ((closedCellSmoothOrientation m o).val x) = o :=
  pullbackSmoothOrientation_pushforward (𝓡∂ (m + 1)) (𝓡 (m + 1)) Subtype.val
    (isSmoothEmbedding_closedCell_inclusion m).contMDiff
    (closedCell_inclusion_mfderiv_bijective m)
    (euclideanSmoothOrientation (EuclideanSpace ℝ (Fin (m + 1))) o) x

end DifferentialGeometry.Topology.Manifold

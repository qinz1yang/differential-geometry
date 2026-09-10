import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere

open Set Metric Manifold
open scoped ContDiff

namespace Poincare.Topology.SphereSeparation

def smoothSchoenfliesThree : Prop :=
  ∀ e : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3),
    IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e →
    ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3)
        (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) ∞,
      closedBall 0 1 ⊆ Φ.source ∧ Φ '' sphere 0 1 = range e

end Poincare.Topology.SphereSeparation

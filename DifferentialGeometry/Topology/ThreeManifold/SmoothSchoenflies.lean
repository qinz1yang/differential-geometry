import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.SmoothEmbedding

open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.ThreeManifold

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => Metric.sphere (0 : ℝ³) 1

theorem smooth_schoenflies_three
    (e : S² → ℝ³) (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' Metric.sphere (0 : ℝ³) 1 = Set.range e := by
  sorry

end DifferentialGeometry.Topology.ThreeManifold

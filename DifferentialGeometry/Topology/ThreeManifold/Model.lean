import Mathlib.Geometry.Manifold.Instances.Sphere

noncomputable section

open scoped Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

abbrev Sphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)

abbrev ThreeModel := 𝓘(ℝ, ThreeSpace)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

import DifferentialGeometry.Geometry.MinimalSurface.Plateau.OpenTargetDifferential
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence

section

noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

theorem riemannianDiskEnergy_restrictOpen
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (N : TopologicalSpace.Opens M) [T2Space N] (q : closedDisk → N) :
    riemannianDiskEnergy (g.restrictOpen N) q =
      riemannianDiskEnergy g (Subtype.val ∘ q) := by
  unfold riemannianDiskEnergy
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => diskMapEnergyDensity_restrictOpen g N _ z

end DifferentialGeometry.Geometry

end

end

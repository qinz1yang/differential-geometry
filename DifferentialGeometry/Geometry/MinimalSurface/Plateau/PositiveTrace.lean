import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalDisk
import DifferentialGeometry.Geometry.Measure.Area.Reparametrization








noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap Filter
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]




theorem IsMorreyDisk.exists_conformal_minimizing_disk
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hd : Module.finrank ℝ E = 3) {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) (hboundary : ∃ U : ℂ → M, SmoothDiskExtension (E := E) u U) :
    ∃ (v : C(closedDisk, M)) (σ : C(loopCircle, loopCircle)) (U : ℂ → M),
      (v = u ∨ v = u.comp ⟨diskReflection, diskReflection.continuous⟩) ∧
      riemannianDiskArea g v = riemannianDiskArea g u ∧
      IsConformalMinimizingDisk g γ v σ U := by
  sorry

end DifferentialGeometry.Geometry

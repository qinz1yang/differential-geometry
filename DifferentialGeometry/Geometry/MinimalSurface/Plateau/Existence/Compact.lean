import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.CompactMinimizer
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.AreaMinimality

noncomputable section

open Manifold Set
open DifferentialGeometry.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_morrey_disk_of_compact
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hfinite : (weaklyMonotoneDiskCompetitors g γ).Nonempty) :
    ∃ q : C(closedDisk, M), IsMorreyDisk g γ q := by
  obtain ⟨q, τ, hτ, _, _, _, htrace, hsmooth, hharm, hconf, henergy, heq⟩ :=
    exists_disk_energy_minimizer_of_compact g γ hγ hfinite
  exact ⟨q, isMorreyDisk_of_energy_attainment g hγ.smooth hγ.immersed
    hsmooth hconf hharm henergy ⟨τ, hτ, htrace⟩ heq⟩

end DifferentialGeometry.Geometry

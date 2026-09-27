import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.NoncompactMinimizer
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.AreaMinimality













noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]






theorem exists_morrey_disk (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hcomplete : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    ∃ u : C(closedDisk, M), IsMorreyDisk g γ u := by
  obtain ⟨u, σ, hσ, _, _, _, htrace, hsmooth, hharm, hconf, henergy, heq⟩ :=
    exists_disk_energy_minimizer_of_homogeneously_regular g hcomplete hregular γ hγ hfinite
  exact ⟨u, isMorreyDisk_of_energy_attainment g hγ.smooth hγ.immersed
    hsmooth hconf hharm henergy ⟨σ, hσ, htrace⟩ heq⟩




def selectedMorreyDisk (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hcomplete : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) : C(closedDisk, M) :=
  Classical.choose (exists_morrey_disk g hcomplete hregular γ hγ hfinite)



theorem selectedMorreyDisk_isMorrey (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hcomplete : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    IsMorreyDisk g γ (selectedMorreyDisk g hcomplete hregular γ hγ hfinite) :=
  Classical.choose_spec (exists_morrey_disk g hcomplete hregular γ hγ hfinite)

end DifferentialGeometry.Geometry

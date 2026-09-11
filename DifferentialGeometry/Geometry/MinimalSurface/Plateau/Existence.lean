import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.HomogeneousRegularity













noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]






theorem exists_morrey_disk (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hd : Module.finrank ℝ E = 3) (hcomplete : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ) (hnull : γ.Nullhomotopic)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    ∃ u : C(closedDisk, M), IsMorreyDisk g γ u := by
  sorry




def selectedMorreyDisk (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hd : Module.finrank ℝ E = 3) (hcomplete : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ) (hnull : γ.Nullhomotopic)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) : C(closedDisk, M) :=
  Classical.choose (exists_morrey_disk g hd hcomplete hregular γ hγ hnull hfinite)



theorem selectedMorreyDisk_isMorrey (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hd : Module.finrank ℝ E = 3) (hcomplete : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ) (hnull : γ.Nullhomotopic)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    IsMorreyDisk g γ (selectedMorreyDisk g hd hcomplete hregular γ hγ hnull hfinite) :=
  Classical.choose_spec (exists_morrey_disk g hd hcomplete hregular γ hγ hnull hfinite)

end DifferentialGeometry.Geometry

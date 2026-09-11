import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Existence
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension







noncomputable section

open Bundle Manifold DifferentialGeometry ContinuousMap
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]



theorem IsMorreyDisk.exists_smooth_extension (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hd : Module.finrank ℝ E = 3) {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) : ∃ U : ℂ → M, SmoothDiskExtension (E := E) u U := by
  sorry



theorem selectedMorreyDisk_smoothUpToBoundary (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hd : Module.finrank ℝ E = 3) (hcomplete : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ) (hnull : γ.Nullhomotopic)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    DiskSmoothUpToBoundary (E := E)
      (selectedMorreyDisk g hd hcomplete hregular γ hγ hnull hfinite) := by
  obtain ⟨U, hU⟩ := IsMorreyDisk.exists_smooth_extension g hd hγ
    (selectedMorreyDisk_isMorrey g hd hcomplete hregular γ hγ hnull hfinite)
  exact hU.smoothUpToBoundary

end DifferentialGeometry.Geometry

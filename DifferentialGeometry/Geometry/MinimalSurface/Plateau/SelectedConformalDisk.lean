import DifferentialGeometry.Geometry.MinimalSurface.Plateau.BoundaryRegularity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PositiveTrace
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ExactAttainment







noncomputable section

open Bundle Manifold DifferentialGeometry ContinuousMap
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]




theorem selectedMorreyDisk_conformal_output (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hd : Module.finrank ℝ E = 3) (hcomplete : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ) (hnull : γ.Nullhomotopic)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    ∃ (v : C(closedDisk, M)) (σ : C(loopCircle, loopCircle)) (U : ℂ → M),
      (v = selectedMorreyDisk g hd hcomplete hregular γ hγ hnull hfinite ∨
        v = (selectedMorreyDisk g hd hcomplete hregular γ hγ hnull hfinite).comp
          ⟨diskReflection, diskReflection.continuous⟩) ∧
      riemannianDiskArea g v =
        riemannianDiskArea g (selectedMorreyDisk g hd hcomplete hregular γ hγ hnull hfinite) ∧
      IsConformalMinimizingDisk g γ v σ U := by
  have hu := selectedMorreyDisk_isMorrey g hd hcomplete hregular γ hγ hnull hfinite
  exact hu.exists_conformal_minimizing_disk g hd hγ
    (hu.exists_smooth_extension g hd hγ)



theorem selectedMorreyDisk_area_eq_leastSpanningArea [CompactSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hd : Module.finrank ℝ E = 3) (hcomplete : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : lipschitzContractibleLoop g) (hγ : IsSmoothEmbeddedLoop (E := E) γ.val.val)
    (hfinite : (spanningDiskCompetitors g γ.val.val).Nonempty) :
    riemannianDiskArea g
      (selectedMorreyDisk g hd hcomplete hregular γ.val.val hγ γ.val.property hfinite) =
      leastSpanningArea g γ := by
  obtain ⟨v, σ, U, _, heq, hv⟩ := selectedMorreyDisk_conformal_output g hd hcomplete hregular
    γ.val.val hγ γ.val.property hfinite
  exact heq.symm.trans (hv.area_eq_leastSpanningArea hγ.smooth)

end DifferentialGeometry.Geometry

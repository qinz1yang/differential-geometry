import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ConformalDiskFromMorrey
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauDensityBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauDiskDensityEquivalence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauFrontierMinimality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauMorreyInteriorBridge

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal
open DifferentialGeometry.Geometry

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

theorem hasConformalMinimizingSmoothInteriorDisk_of_exists_isMorreyDisk
    [T2Space Q] [CompactSpace Q]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (γ : RegularLoop 𝓘(ℝ, E) Q)
    (h : ∃ u : C(Disk, Q), IsMorreyDisk g γ.toContinuousLoop u) :
    HasConformalMinimizingSmoothInteriorDisk (I := 𝓘(ℝ, E)) (Q := Q) g γ :=
  hasConformalMinimizingSmoothInteriorDisk_of_minimizingConformalInteriorDisk g γ
    (hasMinimizingConformalInteriorDisk_of_hasConformalMinimizingInteriorDisk g γ
      (hasConformalMinimizingInteriorDisk_of_exists_isMorreyDisk g γ h))

theorem conformal_disk_producer_of_exists_isMorreyDisk
    [T2Space Q] [CompactSpace Q]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (hdim : Module.finrank ℝ E = 3)
    (γ : RegularLoop 𝓘(ℝ, E) Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (loopLift γ.toContinuousLoop))
    (hemb : Topology.IsEmbedding (γ : Surgery.Topology.Circle → Q))
    (himm : ∀ t : ℝ, loopVelocity (I := 𝓘(ℝ, E)) γ.toContinuousLoop t ≠ 0)
    (h : ∃ u : C(Disk, Q), IsMorreyDisk g γ.toContinuousLoop u) :
    ∃ u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q), ∃ σ : SmoothWeaklyMonotoneCircleMap,
      (∀ θ, u.map (diskBoundary θ) = γ (σ.map θ)) ∧ u.IsConformal g ∧ u.IsHarmonic g ∧
      ∀ v : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q),
        (∀ θ, v.map (diskBoundary θ) = γ θ) →
          diskArea g u.map ≤ diskArea g v.map :=
  conformal_disk_producer_of_hasConformalMinimizingInteriorDisk g hdim γ hγ hemb himm
    (hasConformalMinimizingInteriorDisk_of_exists_isMorreyDisk g γ h)

theorem conformal_disk_attains_exact_area_of_smoothDiskAreaDensity
    [T2Space Q] [CompactSpace Q]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (γ : RegularLoop 𝓘(ℝ, E) Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (loopLift γ.toContinuousLoop))
    (hdensity : SmoothDiskAreaDensity (E := E) g γ.toContinuousLoop)
    (hctr : Surgery.Topology.IsContractibleLoop γ.toContinuousLoop)
    (u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q)) (σ : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ θ, u.map (diskBoundary θ) = γ (σ.map θ))
    (hmin : ∀ v : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q),
      (∀ θ, v.map (diskBoundary θ) = γ θ) → diskArea g u.map ≤ diskArea g v.map) :
    diskArea g u.map = leastArea g γ.toContinuousLoop hctr (γ.isLipschitz g) := by
  have hplateau : PlateauDiskDensity (I := 𝓘(ℝ, E)) (Q := Q) g γ.toContinuousLoop :=
    plateauDiskDensity_of_smoothDiskAreaDensity g γ.toContinuousLoop hdensity
  apply le_antisymm
  · apply le_csInf (competitorAreas_nonempty g γ.toContinuousLoop hctr (γ.isLipschitz g))
    rintro _ ⟨v, rfl⟩
    obtain ⟨w, htracew, hlim⟩ :=
      smooth_exact_disk_density_of_plateauDiskDensity g γ hplateau v
    exact ge_of_tendsto' hlim (fun j => hmin (w j) (htracew j))
  · obtain ⟨ulip, hulip⟩ := u.exists_lipschitz g
    have htracelip : ∀ θ, ulip.map (diskBoundary θ) = γ (σ.map θ) := by
      simpa only [hulip] using htrace
    obtain ⟨v, hv⟩ := zero_area_trace_annulus g γ hγ σ ulip htracelip
    have hle := leastArea_le_competitor g γ.toContinuousLoop hctr (γ.isLipschitz g) v
    simpa only [hv, hulip] using hle

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

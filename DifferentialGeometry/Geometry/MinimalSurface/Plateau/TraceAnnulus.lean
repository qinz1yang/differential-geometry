import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TracePhaseAnnulus
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalDisk
import DifferentialGeometry.Geometry.Measure.Area.LeastArea
import DifferentialGeometry.Topology.LoopSpace.RegularDerivativeBounds

noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]

theorem exists_spanning_disk_competitor_area_eq_of_smooth_positive_trace
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {σ : C(loopCircle, loopCircle)} (hσ : IsSmoothPositiveCircleMap σ)
    {u : C(closedDisk, M)} (htrace : diskTrace u = γ.comp σ)
    (hLip : ∃ L : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w) :
    ∃ v ∈ spanningDiskCompetitors g γ, riemannianDiskArea g v = riemannianDiskArea g u := by
  obtain ⟨ψ, hψ, _, _, hl, δ, hδ, Lδ, hδlip⟩ := hσ.exists_lipschitz_displacement
  let : Nonempty M := ⟨γ 0⟩
  obtain ⟨Lγ, hLγ⟩ := regularLoop_riemannian_lipschitz g
    (⟨γ, hγ.of_le (by simp)⟩ : regularLoop E M)
  obtain ⟨K, hK⟩ := tracePhaseAnnulus_lipschitzOn_strip g hLγ hδlip
  exact exists_spanningDiskCompetitor_of_tracePhase_lipschitz g hψ hl hδ hγ htrace hLip ⟨K, hK⟩

end DifferentialGeometry.Geometry

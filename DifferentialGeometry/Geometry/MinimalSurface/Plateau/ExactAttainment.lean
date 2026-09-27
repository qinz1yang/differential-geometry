import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TraceAnnulus
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothDensity







noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap Filter
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [CompactSpace M]



theorem IsConformalMinimizingDisk.area_eq_leastSpanningArea
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : lipschitzContractibleLoop g}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ.val.val (t : loopCircle)))
    {u : C(closedDisk, M)} {σ : C(loopCircle, loopCircle)} {U : ℂ → M}
    (h : IsConformalMinimizingDisk g γ.val.val u σ U) :
    riemannianDiskArea g u = leastSpanningArea g γ := by
  obtain ⟨v, hv, harea⟩ :=
    exists_spanning_disk_competitor_area_eq_of_smooth_positive_trace
      g hγ h.positiveTrace h.trace
    (h.extension.lipschitz g)
  apply le_antisymm
  · apply le_csInf (show (spanningDiskAreas g γ).Nonempty from ⟨_, v, hv, rfl⟩)
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨wj, hwj, ht⟩ := exists_smooth_spanning_disks_tendsto_area g hγ hw
    exact ge_of_tendsto ht (Eventually.of_forall fun j =>
      h.minimizesSmooth (wj j) (hwj j).1 (hwj j).2)
  · exact harea ▸ leastSpanningArea_le_competitor g γ hv

end DifferentialGeometry.Geometry

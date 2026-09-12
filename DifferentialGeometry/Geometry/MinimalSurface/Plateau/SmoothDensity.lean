import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalDisk
import DifferentialGeometry.Geometry.Measure.Area.LeastArea

noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap Filter
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_smooth_spanning_disks_smooth_extension_tendsto_area [CompactSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {v : C(closedDisk, M)} (hv : v ∈ spanningDiskCompetitors g γ) :
    ∃ (vj : ℕ → C(closedDisk, M)) (Uj : ℕ → ℂ → M),
      (∀ j, SmoothDiskExtension (E := E) (vj j) (Uj j) ∧ diskTrace (vj j) = γ) ∧
      Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v)) := by
  sorry

theorem exists_smooth_spanning_disks_tendsto_area [CompactSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    {v : C(closedDisk, M)} (hv : v ∈ spanningDiskCompetitors g γ) :
    ∃ vj : ℕ → C(closedDisk, M),
      (∀ j, DiskSmoothUpToBoundary (E := E) (vj j) ∧ diskTrace (vj j) = γ) ∧
      Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v)) := by
  obtain ⟨vj, Uj, h, ht⟩ := exists_smooth_spanning_disks_smooth_extension_tendsto_area g hγ hv
  exact ⟨vj, fun j => ⟨(h j).1.smoothUpToBoundary, (h j).2⟩, ht⟩

end DifferentialGeometry.Geometry

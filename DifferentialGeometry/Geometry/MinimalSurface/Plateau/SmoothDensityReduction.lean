import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MinimalDiskAreaDensityFrontier
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothDiskAreaDensity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothDiskTrace
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SpanningDiskAreaDensity

noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap Filter
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

omit [FiniteDimensional ℝ E] [T3Space M] in
theorem exists_smooth_spanning_disks_smooth_extension_tendsto_area_of_diskAreaDensityAt
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {v : C(closedDisk, M)}
    (hdensity : DiskAreaDensityAt (E := E) g γ v) :
    ∃ (vj : ℕ → C(closedDisk, M)) (Uj : ℕ → ℂ → M),
      (∀ j, SmoothDiskExtension (E := E) (vj j) (Uj j) ∧ diskTrace (vj j) = γ) ∧
      Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v)) :=
  exists_smooth_spanning_disks_smooth_extension_tendsto_area_of_area_approximation g hdensity

omit [FiniteDimensional ℝ E] [T3Space M] in
theorem diskAreaDensityAt_of_exists_smooth_spanning_disks_smooth_extension_tendsto_area
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {v : C(closedDisk, M)}
    (h : ∃ (vj : ℕ → C(closedDisk, M)) (Uj : ℕ → ℂ → M),
      (∀ j, SmoothDiskExtension (E := E) (vj j) (Uj j) ∧ diskTrace (vj j) = γ) ∧
      Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v))) :
    DiskAreaDensityAt (E := E) g γ v := by
  obtain ⟨vj, Uj, hdata, ht⟩ := h
  exact diskAreaDensityAt_of_tendsto g (fun j => (hdata j).1) (fun j => (hdata j).2) ht

omit [FiniteDimensional ℝ E] [T3Space M] in
theorem exists_smooth_spanning_disks_smooth_extension_tendsto_area_iff_diskAreaDensityAt
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {v : C(closedDisk, M)} :
    (∃ (vj : ℕ → C(closedDisk, M)) (Uj : ℕ → ℂ → M),
      (∀ j, SmoothDiskExtension (E := E) (vj j) (Uj j) ∧ diskTrace (vj j) = γ) ∧
      Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v))) ↔
      DiskAreaDensityAt (E := E) g γ v :=
  ⟨diskAreaDensityAt_of_exists_smooth_spanning_disks_smooth_extension_tendsto_area g,
    exists_smooth_spanning_disks_smooth_extension_tendsto_area_of_diskAreaDensityAt g⟩

omit [T3Space M] in
theorem smoothDiskAreaDensity_of_areaDenseAt
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (h : SmoothDisksAreAreaDenseAt g γ) :
    SmoothDiskAreaDensity (E := E) g γ := by
  intro v hv
  exact diskAreaDensityAt_of_exists_smooth_spanning_disks_smooth_extension_tendsto_area g
    (exists_smooth_spanning_disks_smooth_extension_tendsto_area_of_areaDenseAt g h v hv)

omit [T3Space M] in
theorem smoothDiskAreaDensity_of_weakTracesDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (h : SmoothDisksAreAreaDenseForWeakTracesAt g γ) :
    SmoothDiskAreaDensity (E := E) g γ :=
  smoothDiskAreaDensity_of_areaDenseAt g (smoothDisksAreAreaDenseAt_of_weakTraces g h)

omit [T3Space M] in
theorem exists_smooth_spanning_disks_smooth_extension_tendsto_area_of_weakTracesDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {v : C(closedDisk, M)}
    (h : SmoothDisksAreAreaDenseForWeakTracesAt g γ) (hv : v ∈ spanningDiskCompetitors g γ) :
    ∃ (vj : ℕ → C(closedDisk, M)) (Uj : ℕ → ℂ → M),
      (∀ j, SmoothDiskExtension (E := E) (vj j) (Uj j) ∧ diskTrace (vj j) = γ) ∧
      Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v)) :=
  exists_smooth_spanning_disks_smooth_extension_tendsto_area_of_diskAreaDensityAt g
    (smoothDiskAreaDensity_of_weakTracesDensity g h v hv)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] in
theorem contMDiff_of_exists_smoothDiskExtension_diskTrace
    {γ : freeLoop M} {u : C(closedDisk, M)} {U : ℂ → M}
    (h : SmoothDiskExtension (E := E) u U) (htr : diskTrace u = γ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)) := by
  rw [← htr]
  exact h.smoothUpToBoundary.trace

omit [FiniteDimensional ℝ E] [T3Space M] in
theorem contMDiff_of_exists_smooth_spanning_disks_smooth_extension_tendsto_area
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {v : C(closedDisk, M)}
    (h : ∃ (vj : ℕ → C(closedDisk, M)) (Uj : ℕ → ℂ → M),
      (∀ j, SmoothDiskExtension (E := E) (vj j) (Uj j) ∧ diskTrace (vj j) = γ) ∧
      Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v))) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)) := by
  obtain ⟨vj, Uj, hdata, _⟩ := h
  exact contMDiff_of_exists_smoothDiskExtension_diskTrace (hdata 0).1 (hdata 0).2

omit [T3Space M] in
theorem contMDiff_of_weakTracesDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (h : SmoothDisksAreAreaDenseForWeakTracesAt g γ)
    (hv : (spanningDiskCompetitors g γ).Nonempty) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)) := by
  obtain ⟨v, hv⟩ := hv
  obtain ⟨vj, hvj, _⟩ := h (ContinuousMap.id loopCircle)
    ⟨fun t : ℝ => t, continuous_id, fun _ => rfl, Or.inl ⟨monotone_id, fun _ => rfl⟩⟩ v
    (by simpa only [ContinuousMap.comp_id] using hv)
  obtain ⟨U, hU⟩ := exists_smoothDiskExtension_of_diskSmoothUpToBoundary (E := E) (hvj 0).1
  exact contMDiff_of_exists_smoothDiskExtension_diskTrace hU (hvj 0).2

omit [T3Space M] in
theorem exists_smooth_spanning_disks_smooth_extension_tendsto_area_of_subsingleton
    [Subsingleton M] (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    {v : C(closedDisk, M)} (hv : v ∈ spanningDiskCompetitors g γ) :
    ∃ (vj : ℕ → C(closedDisk, M)) (Uj : ℕ → ℂ → M),
      (∀ j, SmoothDiskExtension (E := E) (vj j) (Uj j) ∧ diskTrace (vj j) = γ) ∧
      Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v)) :=
  exists_smooth_spanning_disks_smooth_extension_tendsto_area_of_areaDenseAt g
    (smoothDisksAreAreaDenseAt_of_subsingleton g γ) v hv

end DifferentialGeometry.Geometry

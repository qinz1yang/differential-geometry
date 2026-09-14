import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SpanningDiskAreaDensity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothDensityFrontier

noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap Filter
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
def DiskAreaDensityAt (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (v : C(closedDisk, M)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (w : C(closedDisk, M)) (W : ℂ → M),
    SmoothDiskExtension (E := E) w W ∧ diskTrace w = γ ∧
      |riemannianDiskArea g w - riemannianDiskArea g v| ≤ ε

omit [FiniteDimensional ℝ E] in
def SmoothDiskAreaDensity (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M) : Prop :=
  ∀ v : C(closedDisk, M), v ∈ spanningDiskCompetitors g γ → DiskAreaDensityAt (E := E) g γ v

omit [FiniteDimensional ℝ E] in
theorem exists_smooth_spanning_disks_smooth_extension_tendsto_area_of_density
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (h : SmoothDiskAreaDensity (E := E) g γ) {v : C(closedDisk, M)}
    (hv : v ∈ spanningDiskCompetitors g γ) :
    ∃ (vj : ℕ → C(closedDisk, M)) (Uj : ℕ → ℂ → M),
      (∀ j, SmoothDiskExtension (E := E) (vj j) (Uj j) ∧ diskTrace (vj j) = γ) ∧
      Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v)) :=
  exists_smooth_spanning_disks_smooth_extension_tendsto_area_of_area_approximation g (h v hv)

omit [FiniteDimensional ℝ E] in
theorem exists_smooth_spanning_disks_tendsto_area_of_density
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (h : SmoothDiskAreaDensity (E := E) g γ) {v : C(closedDisk, M)}
    (hv : v ∈ spanningDiskCompetitors g γ) :
    ∃ vj : ℕ → C(closedDisk, M),
      (∀ j, DiskSmoothUpToBoundary (E := E) (vj j) ∧ diskTrace (vj j) = γ) ∧
      Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v)) := by
  refine exists_smooth_spanning_disks_tendsto_area_of_area_approximation g ?_
  intro ε hε
  obtain ⟨w, W, hW, htr, hle⟩ := h v hv ε hε
  exact ⟨w, hW.smoothUpToBoundary, htr, hle⟩

omit [FiniteDimensional ℝ E] in
theorem diskAreaDensityAt_of_tendsto
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {v : C(closedDisk, M)}
    {vj : ℕ → C(closedDisk, M)} {Uj : ℕ → ℂ → M}
    (hsm : ∀ j, SmoothDiskExtension (E := E) (vj j) (Uj j))
    (htr : ∀ j, diskTrace (vj j) = γ)
    (ht : Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v))) :
    DiskAreaDensityAt (E := E) g γ v := by
  intro ε hε
  have hball : ∀ᶠ j in atTop,
      dist (riemannianDiskArea g (vj j)) (riemannianDiskArea g v) < ε :=
    ht.eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨j, hj⟩ := hball.exists
  rw [Real.dist_eq] at hj
  exact ⟨vj j, Uj j, hsm j, htr j, hj.le⟩

omit [FiniteDimensional ℝ E] in
theorem density_of_exists_smooth_spanning_disks_smooth_extension_tendsto_area
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (h : ∀ v : C(closedDisk, M), v ∈ spanningDiskCompetitors g γ →
      ∃ (vj : ℕ → C(closedDisk, M)) (Uj : ℕ → ℂ → M),
        (∀ j, SmoothDiskExtension (E := E) (vj j) (Uj j) ∧ diskTrace (vj j) = γ) ∧
        Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v))) :
    SmoothDiskAreaDensity (E := E) g γ := by
  intro v hv
  obtain ⟨vj, Uj, hdata, ht⟩ := h v hv
  exact diskAreaDensityAt_of_tendsto g (fun j => (hdata j).1) (fun j => (hdata j).2) ht

omit [FiniteDimensional ℝ E] in
theorem diskAreaDensityAt_of_smoothDiskExtension
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {v : C(closedDisk, M)}
    {V : ℂ → M}
    (hV : SmoothDiskExtension (E := E) v V) (htr : diskTrace v = γ) :
    DiskAreaDensityAt (E := E) g γ v :=
  diskAreaDensityAt_of_tendsto g (fun _ => hV) (fun _ => htr) tendsto_const_nhds

end DifferentialGeometry.Geometry

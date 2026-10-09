import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiskVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonDensity

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

def DiskSmoothExtension (I : ModelWithCorners ℝ E H) (u : C(Disk, Q)) (U : ℂ → Q) : Prop :=
  (∀ z : Disk, U z = u z) ∧ ∃ N : Set ℂ, IsOpen N ∧
    Metric.closedBall (0 : ℂ) 1 ⊆ N ∧ ContMDiffOn 𝓘(ℝ, ℂ) I ∞ U N

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
theorem DiskSmoothExtension.smoothUpToBoundary {u : C(Disk, Q)} {U : ℂ → Q}
    (h : DiskSmoothExtension I u U) :
    ContMDiffOn 𝓘(ℝ, ℂ) I ∞ (diskExtension u) (Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨heq, N, _hN, hDN, hU⟩ := h
  refine (hU.mono hDN).congr fun z hz => ?_
  exact (diskExtension_coe u ⟨z, hz⟩).trans (heq ⟨z, hz⟩).symm

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
def smoothDiskOfDiskSmoothExtension {u : C(Disk, Q)} {U : ℂ → Q}
    (h : DiskSmoothExtension I u U) : SmoothDisk (I := I) (Q := Q) where
  map := u
  smooth z := by
    obtain ⟨heq, N, hN, hDN, hUN⟩ := h
    refine ⟨{
      map := U
      domain := N
      isOpen_domain := hN
      mem_domain := hDN z.property
      smooth := hUN
      agrees := ?_ }⟩
    intro w hw
    rw [heq ⟨w, hw.2⟩]
    exact (diskExtension_coe u ⟨w, hw.2⟩).symm

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
@[simp] theorem smoothDisk_of_diskSmoothExtension_map {u : C(Disk, Q)} {U : ℂ → Q}
    (h : DiskSmoothExtension I u U) : (smoothDiskOfDiskSmoothExtension h).map = u := rfl

def HasDiskSmoothExtensionDensity (g : SmoothRiemannianMetric I Q)
    (γ : Surgery.Topology.ContinuousFreeLoop Q) : Prop :=
  ∀ v : DiskCompetitor g γ,
    ∃ (vj : ℕ → C(Disk, Q)) (Uj : ℕ → ℂ → Q),
      (∀ j, DiskSmoothExtension I (vj j) (Uj j) ∧
        ∀ θ, vj j (diskBoundary θ) = γ θ) ∧
      Tendsto (fun j => diskArea g (vj j)) atTop (𝓝 (diskArea g v.1.map))

omit [FiniteDimensional ℝ E] in
theorem plateauDiskDensity_of_hasDiskSmoothExtensionDensity (g : SmoothRiemannianMetric I Q)
    (γ : Surgery.Topology.ContinuousFreeLoop Q)
    (h : HasDiskSmoothExtensionDensity (I := I) (Q := Q) g γ) :
    PlateauDiskDensity (I := I) (Q := Q) g γ := by
  intro v
  obtain ⟨vj, Uj, hdata, htend⟩ := h v
  exact ⟨fun j => smoothDiskOfDiskSmoothExtension (hdata j).1,
    fun j θ => (hdata j).2 θ, htend⟩

omit [FiniteDimensional ℝ E] in
theorem smooth_exact_disk_density_of_plateauDiskDensity
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (hd : PlateauDiskDensity (I := I) (Q := Q) g γ.toContinuousLoop)
    (v : DiskCompetitor g γ.toContinuousLoop) :
    ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
      (∀ j θ, (w j).map (diskBoundary θ) = γ θ) ∧
      Tendsto (fun j => diskArea g (w j).map) atTop (𝓝 (diskArea g v.1.map)) :=
  hd v

omit [FiniteDimensional ℝ E] in
theorem exists_smoothDisk_sequence_of_smoothDisk (g : SmoothRiemannianMetric I Q)
    (γ : Surgery.Topology.ContinuousFreeLoop Q) (w : SmoothDisk (I := I) (Q := Q))
    (htrace : ∀ θ, w.map (diskBoundary θ) = γ θ) :
    ∃ w' : ℕ → SmoothDisk (I := I) (Q := Q),
      (∀ j θ, (w' j).map (diskBoundary θ) = γ θ) ∧
      Tendsto (fun j => diskArea g (w' j).map) atTop (𝓝 (diskArea g w.map)) :=
  ⟨fun _ => w, fun _ _ => htrace _, tendsto_const_nhds⟩

theorem hasDiskSmoothExtensionDensity_of_smoothDisk_competitors [I.Boundaryless] [T2Space Q]
    [CompactSpace Q] [Nonempty Q] (g : SmoothRiemannianMetric I Q)
    (γ : Surgery.Topology.ContinuousFreeLoop Q) (w : SmoothDisk (I := I) (Q := Q))
    (htrace : ∀ θ, w.map (diskBoundary θ) = γ θ) :
    ∃ vj : ℕ → C(Disk, Q), ∃ Uj : ℕ → ℂ → Q,
      (∀ j, DiskSmoothExtension I (vj j) (Uj j) ∧
        ∀ θ, vj j (diskBoundary θ) = γ θ) ∧
      Tendsto (fun j => diskArea g (vj j)) atTop (𝓝 (diskArea g w.map)) := by
  obtain ⟨U, hU⟩ := w.exists_smoothExtension
  exact ⟨fun _ => w.map, fun _ => U, fun _ => ⟨hU, htrace⟩, tendsto_const_nhds⟩

section StandardModel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]

theorem smooth_exact_disk_density_stdModel_of_smoothDiskDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : RegularLoop 𝓘(ℝ, E) M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (loopLift γ.toContinuousLoop))
    (v : DiskCompetitor g γ.toContinuousLoop) :
    ∃ w : ℕ → SmoothDisk (I := 𝓘(ℝ, E)) (Q := M),
      (∀ j θ, (w j).map (diskBoundary θ) = γ θ) ∧
      Tendsto (fun j => diskArea g (w j).map) atTop (𝓝 (diskArea g v.1.map)) :=
  smooth_exact_disk_density_stdModel g γ hγ v

end StandardModel

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

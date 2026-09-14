import DifferentialGeometry.Geometry.Measure.Area.SpanningCompetitors
import DifferentialGeometry.Geometry.Measure.Area.ManifoldDensity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalDisk
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalEnergy
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskLocality
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension

noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem diskMapPartial_const (q : M) (z v : ℂ) :
    diskMapPartial (E := E) (fun _ : ℂ => q) z v = 0 := by
  have h : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun _ : ℂ => q) z =
      (0 : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, E) q) := mfderiv_const
  rw [diskMapPartial, h]
  exact zero_apply v

omit [FiniteDimensional ℝ E] in
theorem diskMapConformalAt_const (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : M) (z : ℂ) :
    DiskMapConformalAt g (fun _ : ℂ => q) z := by
  have h := diskMapPartial_const (E := E) q z
  unfold DiskMapConformalAt
  rw [h (1 : ℂ), h Complex.I]
  exact ⟨by simp, by simp⟩

theorem diskMapCovariantPartial_const (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : M)
    (z v w : ℂ) : diskMapCovariantPartial g (fun _ : ℂ => q) z v w = 0 := by
  rw [diskMapCovariantPartial]
  have h : (fun t : ℝ => diskMapPartial (E := E) (fun _ : ℂ => q) (z + t • v) w) =
      fun _ => 0 := by
    funext t
    exact diskMapPartial_const q (z + t • v) w
  rw [h]
  exact DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong_zero
    (I := 𝓘(ℝ, E)) g (fun _ : ℝ => q) 0

theorem diskMapTension_const (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : M) (z : ℂ) :
    diskMapTension g (fun _ : ℂ => q) z = 0 := by
  rw [diskMapTension, diskMapCovariantPartial_const, diskMapCovariantPartial_const, add_zero]

omit [FiniteDimensional ℝ E] in
theorem diskMapEnergyDensity_const (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : M) :
    diskMapEnergyDensity g (fun _ : ℂ => q) = fun _ => 0 := by
  funext z
  rw [diskMapEnergyDensity, diskMapPartial_const, diskMapPartial_const]
  simp

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem diskExtension_const (q : M) :
    diskExtension (ContinuousMap.const closedDisk q) = fun _ : ℂ => q := by
  funext z
  simp [diskExtension]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem smoothDiskExtension_const (q : M) :
    SmoothDiskExtension (E := E) (ContinuousMap.const closedDisk q) (fun _ => q) :=
  ⟨fun _ => rfl, univ, isOpen_univ, subset_univ _, contMDiffOn_const⟩

omit [FiniteDimensional ℝ E] in
theorem diskWeakJordanTrace_const (q : M) :
    DiskWeakJordanTrace (ContinuousMap.const loopCircle q)
      (ContinuousMap.const closedDisk q) := by
  refine ⟨ContinuousMap.id loopCircle,
    ⟨fun t : ℝ => t, continuous_id, fun _ => rfl,
      Or.inl ⟨monotone_id, fun _ => rfl⟩⟩, ?_⟩
  ext θ
  simp [diskTrace]

theorem isMorreyDisk_const (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : M) :
    IsMorreyDisk g (ContinuousMap.const loopCircle q) (ContinuousMap.const closedDisk q) := by
  have hde := diskExtension_const q
  have hzero : riemannianDiskArea g (ContinuousMap.const closedDisk q) = 0 :=
    riemannianDiskArea_const g q
  refine ⟨?_, ?_, ?_, ?_, diskWeakJordanTrace_const q, ?_, ?_⟩
  · change ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞
      (diskExtension (ContinuousMap.const closedDisk q)) (Metric.ball (0 : ℂ) 1)
    rw [hde]
    exact contMDiffOn_const
  · rw [hde]
    exact fun z _ => diskMapConformalAt_const g q z
  · rw [hde]
    exact fun z _ => diskMapTension_const g q z
  · rw [hde, diskMapEnergyDensity_const]
    simp
  · intro v _ _
    rw [hzero]
    exact riemannianDiskArea_nonneg g v
  · intro v _ _
    rw [hzero]
    exact riemannianDiskArea_nonneg g v

def SmoothDisksAreAreaDenseAt (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) : Prop :=
  ∀ v : C(closedDisk, M), v ∈ spanningDiskCompetitors g γ →
    ∃ vj : ℕ → C(closedDisk, M),
      (∀ j, DiskSmoothUpToBoundary (E := E) (vj j) ∧ diskTrace (vj j) = γ) ∧
      Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v))

def SmoothDisksAreAreaDenseForWeakTracesAt (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) : Prop :=
  ∀ (σ : C(loopCircle, loopCircle)), IsWeaklyMonotoneOnce σ →
    ∀ v ∈ spanningDiskCompetitors g (γ.comp σ),
      ∃ vj : ℕ → C(closedDisk, M),
        (∀ j, DiskSmoothUpToBoundary (E := E) (vj j) ∧ diskTrace (vj j) = γ) ∧
        Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v))

omit [FiniteDimensional ℝ E] in
theorem smoothDisksAreAreaDenseAt_of_weakTraces
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (h : SmoothDisksAreAreaDenseForWeakTracesAt g γ) : SmoothDisksAreAreaDenseAt g γ := by
  intro v hv
  exact h (ContinuousMap.id loopCircle)
    ⟨fun t : ℝ => t, continuous_id, fun _ => rfl, Or.inl ⟨monotone_id, fun _ => rfl⟩⟩ v
    (by simpa only [ContinuousMap.comp_id] using hv)

omit [FiniteDimensional ℝ E] in
theorem smoothDisksAreAreaDenseAt_of_exists_smooth_spanning_disks_smooth_extension
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (h : ∀ v : C(closedDisk, M), v ∈ spanningDiskCompetitors g γ →
      ∃ (vj : ℕ → C(closedDisk, M)) (Uj : ℕ → ℂ → M),
        (∀ j, SmoothDiskExtension (E := E) (vj j) (Uj j) ∧ diskTrace (vj j) = γ) ∧
        Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v))) :
    SmoothDisksAreAreaDenseAt g γ := by
  intro v hv
  obtain ⟨vj, _, hvj, ht⟩ := h v hv
  exact ⟨vj, fun j => ⟨(hvj j).1.smoothUpToBoundary, (hvj j).2⟩, ht⟩

theorem exists_smooth_spanning_disks_smooth_extension_tendsto_area_of_areaDenseAt
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (h : SmoothDisksAreAreaDenseAt g γ) :
    ∀ v : C(closedDisk, M), v ∈ spanningDiskCompetitors g γ →
      ∃ (vj : ℕ → C(closedDisk, M)) (Uj : ℕ → ℂ → M),
        (∀ j, SmoothDiskExtension (E := E) (vj j) (Uj j) ∧ diskTrace (vj j) = γ) ∧
        Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v)) := by
  intro v hv
  obtain ⟨vj, hvj, ht⟩ := h v hv
  choose Uj hUj using fun j =>
    exists_smoothDiskExtension_of_diskSmoothUpToBoundary (E := E) (hvj j).1
  exact ⟨vj, Uj, fun j => ⟨hUj j, (hvj j).2⟩, ht⟩

theorem exists_smooth_spanning_disks_smooth_extension_tendsto_area_of_diskSmoothUpToBoundary
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {v : C(closedDisk, M)}
    (hv : v ∈ spanningDiskCompetitors g γ) (h : DiskSmoothUpToBoundary (E := E) v) :
    ∃ (vj : ℕ → C(closedDisk, M)) (Uj : ℕ → ℂ → M),
      (∀ j, SmoothDiskExtension (E := E) (vj j) (Uj j) ∧ diskTrace (vj j) = γ) ∧
      Tendsto (fun j => riemannianDiskArea g (vj j)) atTop (𝓝 (riemannianDiskArea g v)) := by
  obtain ⟨U, hU⟩ := exists_smoothDiskExtension_of_diskSmoothUpToBoundary (E := E) h
  exact ⟨fun _ => v, fun _ => U, fun _ => ⟨hU, hv.1⟩, tendsto_const_nhds⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem diskSmoothUpToBoundary_of_subsingleton [Subsingleton M] (v : C(closedDisk, M)) :
    DiskSmoothUpToBoundary (E := E) v := by
  change ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension v)
    (Metric.closedBall (0 : ℂ) 1)
  have h : diskExtension v = fun _ : ℂ => v ⟨0, by simp⟩ := by
    funext z
    exact Subsingleton.elim _ _
  rw [h]
  exact contMDiffOn_const

omit [FiniteDimensional ℝ E] in
theorem smoothDisksAreAreaDenseAt_of_subsingleton (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) [Subsingleton M] : SmoothDisksAreAreaDenseAt g γ := by
  intro v hv
  exact ⟨fun _ => v,
    fun _ => ⟨diskSmoothUpToBoundary_of_subsingleton v, Subsingleton.elim _ _⟩,
    tendsto_const_nhds⟩

omit [FiniteDimensional ℝ E] in
theorem smoothDisksAreAreaDenseForWeakTracesAt_of_subsingleton
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M) [Subsingleton M] :
    SmoothDisksAreAreaDenseForWeakTracesAt g γ := by
  intro σ _ v _
  exact ⟨fun _ => v,
    fun _ => ⟨diskSmoothUpToBoundary_of_subsingleton v, Subsingleton.elim _ _⟩,
    tendsto_const_nhds⟩

theorem isMorreyDisk_of_conformalMinimizingDisk_of_areaDenseForWeakTraces
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {u : C(closedDisk, M)}
    {σ : C(loopCircle, loopCircle)} {U : ℂ → M}
    (hdensity : SmoothDisksAreAreaDenseForWeakTracesAt g γ)
    (h : IsConformalMinimizingDisk g γ u σ U) : IsMorreyDisk g γ u := by
  have hconformal : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z :=
    fun z hz => (diskMapConformalAt_congr_of_eventuallyEq g
      (SmoothDiskExtension.eventuallyEq_diskExtension h.extension hz)).mp
      (h.conformal z (Metric.ball_subset_closedBall hz))
  have hharmonic : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension u) z = 0 := by
    intro z hz
    have hval : (diskMapTension g (diskExtension u) z : E) = 0 := by
      rw [← diskMapTension_congr_of_eventuallyEq g
          (SmoothDiskExtension.eventuallyEq_diskExtension h.extension hz),
        h.harmonic z (Metric.ball_subset_closedBall hz)]
      rfl
    exact hval
  have hfinite : IntegrableOn (diskMapEnergyDensity g (diskExtension u))
      (Metric.closedBall (0 : ℂ) 1) := by
    obtain ⟨_, N, hN, hDN, hU⟩ := h.extension
    have hUint : IntegrableOn (riemannianAreaDensity g U) (Metric.closedBall (0 : ℂ) 1) :=
      integrableOn_riemannianAreaDensity_of_contMDiffOn g hN (hU.of_le (by norm_num))
        (isCompact_closedBall (0 : ℂ) 1) hDN
    have hcongr : (fun z => riemannianAreaDensity g U z) =ᵐ[volume.restrict
        (Metric.closedBall (0 : ℂ) 1)] fun z => riemannianAreaDensity g (diskExtension u) z := by
      filter_upwards [ae_disk_interior] with z hz
      exact riemannianAreaDensity_congr g (SmoothDiskExtension.eventuallyEq_diskExtension
        h.extension hz)
    exact (diskArea_integrable_iff_energy_of_conformal g u hconformal).1 (hUint.congr_fun_ae hcongr)
  refine ⟨h.extension.smoothUpToBoundary.interior, hconformal, hharmonic, hfinite,
    h.weakJordanTrace, ?_, h.minimizesSmooth⟩
  intro v hv hLip
  obtain ⟨σv, hσv, htrv⟩ := hv
  obtain ⟨vj, hvj, ht⟩ := hdensity σv hσv v ⟨htrv, hLip⟩
  exact ge_of_tendsto ht
    (Eventually.of_forall fun j => h.minimizesSmooth (vj j) (hvj j).1 (hvj j).2)

theorem exists_isMorreyDisk_of_exists_conformalMinimizingDisk_of_areaDenseForWeakTraces
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hdensity : SmoothDisksAreAreaDenseForWeakTracesAt g γ)
    (h : ∃ (u : C(closedDisk, M)) (σ : C(loopCircle, loopCircle)) (U : ℂ → M),
      IsConformalMinimizingDisk g γ u σ U) :
    ∃ u : C(closedDisk, M), IsMorreyDisk g γ u := by
  obtain ⟨u, σ, U, hconf⟩ := h
  exact ⟨u, isMorreyDisk_of_conformalMinimizingDisk_of_areaDenseForWeakTraces g hdensity hconf⟩

end DifferentialGeometry.Geometry

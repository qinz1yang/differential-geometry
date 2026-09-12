import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalDisk
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskLocality
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskReflectionCovariant
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskTensionSmoothness
import DifferentialGeometry.Geometry.Measure.Area.Reparametrization

noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap Filter MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Bundle Manifold ContDiff Topology ComplexConjugate NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

omit [T3Space M] in
theorem IsMorreyDisk.conformal_of_extension {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u) {U : ℂ → M}
    (hext : SmoothDiskExtension (E := E) u U) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U z :=
  fun z hz =>
    (diskMapConformalAt_congr_of_eventuallyEq g (hext.eventuallyEq_diskExtension hz)).mpr
      (hu.conformal z hz)

omit [T3Space M] in
theorem IsMorreyDisk.tension_eq_zero_of_extension {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u) {U : ℂ → M}
    (hext : SmoothDiskExtension (E := E) u U) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g U z = 0 := by
  intro z hz
  have hval : (diskMapTension g U z : E) = 0 := by
    rw [diskMapTension_congr_of_eventuallyEq g (hext.eventuallyEq_diskExtension hz),
      hu.harmonic z hz]
    rfl
  exact hval

omit [T3Space M] in
theorem IsMorreyDisk.conformal_of_extension_closedBall {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u) {U : ℂ → M}
    (hext : SmoothDiskExtension (E := E) u U) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt g U z := by
  obtain ⟨heq, N, hN, hDN, hU⟩ := hext
  exact diskMapConformalAt_of_ball g hN hU hDN
    (hu.conformal_of_extension ⟨heq, N, hN, hDN, hU⟩)

omit [T3Space M] in
theorem IsMorreyDisk.tension_eq_zero_of_extension_closedBall {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u) {U : ℂ → M}
    (hext : SmoothDiskExtension (E := E) u U) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, diskMapTension g U z = 0 := by
  obtain ⟨heq, N, hN, hDN, hU⟩ := hext
  exact diskMapTension_eq_zero_of_ball g hN hU hDN
    (hu.tension_eq_zero_of_extension ⟨heq, N, hN, hDN, hU⟩)

omit [T3Space M] in
theorem IsMorreyDisk.conformal_comp_diskReflection {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u) {U : ℂ → M}
    (hext : SmoothDiskExtension (E := E) u U) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt g (U ∘ conj) z :=
  fun z hz => (hu.conformal_of_extension_closedBall hext (conj z) (by
    simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using hz)).comp_conj g

omit [T3Space M] in
theorem IsMorreyDisk.tension_eq_zero_comp_diskReflection {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u) {U : ℂ → M}
    (hext : SmoothDiskExtension (E := E) u U) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, diskMapTension g (U ∘ conj) z = 0 :=
  fun z hz => by
    rw [diskMapTension_comp_conj g U z]
    exact hu.tension_eq_zero_of_extension_closedBall hext (conj z) (by
      simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_conj] using hz)

omit [FiniteDimensional ℝ E] [T3Space M] in
theorem riemannianDiskArea_diskReflection_of_extension (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : C(closedDisk, M)} {U : ℂ → M} (hext : SmoothDiskExtension (E := E) u U) :
    riemannianDiskArea g (u.comp ⟨diskReflection, diskReflection.continuous⟩) =
      riemannianDiskArea g u := by
  obtain ⟨heq, N, hN, hDN, hU⟩ := hext
  have hconj := riemannianArea_comp_conj_of_contMDiffOn g hN hDN hU
  obtain ⟨heq', _⟩ :=
    SmoothDiskExtension.comp_diskReflection (⟨heq, N, hN, hDN, hU⟩ : SmoothDiskExtension (E := E) u U)
  rw [riemannianDiskArea_eq_of_extension g _ (U ∘ conj) heq',
    riemannianDiskArea_eq_of_extension g u U heq, hconj]

omit [T3Space M] in
theorem exists_conformal_minimizing_disk_of_smooth_positive_trace
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) (hext : ∃ U : ℂ → M, SmoothDiskExtension (E := E) u U)
    (σ : C(loopCircle, loopCircle)) (hσ : IsSmoothPositiveCircleMap σ)
    (htr : diskTrace u = γ.comp σ ∨
      diskTrace (u.comp ⟨diskReflection, diskReflection.continuous⟩) = γ.comp σ) :
    ∃ (v : C(closedDisk, M)) (σ' : C(loopCircle, loopCircle)) (U : ℂ → M),
      (v = u ∨ v = u.comp ⟨diskReflection, diskReflection.continuous⟩) ∧
      riemannianDiskArea g v = riemannianDiskArea g u ∧
      IsConformalMinimizingDisk g γ v σ' U := by
  obtain ⟨U, hextU⟩ := hext
  rcases htr with htr | htr
  · refine ⟨u, σ, U, Or.inl rfl, rfl, ?_⟩
    exact ⟨hextU, hσ, htr, hu.conformal_of_extension_closedBall hextU,
      hu.tension_eq_zero_of_extension_closedBall hextU, hu.minimizesSmooth⟩
  · refine ⟨u.comp ⟨diskReflection, diskReflection.continuous⟩, σ, U ∘ conj, Or.inr rfl, ?_, ?_⟩
    · exact riemannianDiskArea_diskReflection_of_extension g hextU
    · exact ⟨SmoothDiskExtension.comp_diskReflection hextU, hσ, htr,
        hu.conformal_comp_diskReflection hextU, hu.tension_eq_zero_comp_diskReflection hextU,
        fun w hw hwtr => (riemannianDiskArea_diskReflection_of_extension g hextU).trans_le
          (hu.minimizesSmooth w hw hwtr)⟩

end DifferentialGeometry.Geometry

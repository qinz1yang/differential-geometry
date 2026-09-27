import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Reparametrization.AreaEnergy
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.WeakJordanDensity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalEnergy

section

noncomputable section
open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Topology
open scoped ContDiff Topology Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem disk_energy_inf_le_area_of_weakJordanTrace
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    (him : ∀ t : ℝ,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) t 1 ≠ 0)
    {u : C(closedDisk, M)} (hu : DiskWeakJordanTrace γ u) {L : ℝ≥0}
    (hL : ∀ z w : closedDisk,
      riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w) :
    sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
      weaklyMonotoneDiskCompetitors g γ) ≤ riemannianDiskArea g u := by
  obtain ⟨vj, Vj, hj, ht⟩ :=
    exists_smooth_spanning_disks_tendsto_area_of_weakJordanTrace g hγ him hu hL
  exact ge_of_tendsto' ht (fun j =>
    (hj j).1.disk_energy_inf_le_area g (DiskWeakJordanTrace.of_diskTrace_eq (hj j).2))

theorem riemannianDiskArea_le_of_energy_attainment_of_conformal
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    (him : ∀ t : ℝ,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) t 1 ≠ 0)
    {u : C(closedDisk, M)}
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z)
    (heq : riemannianDiskEnergy g u = sInf
      ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ))
    {v : C(closedDisk, M)} (hv : DiskWeakJordanTrace γ v) {L : ℝ≥0}
    (hL : ∀ z w : closedDisk,
      riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) :
    riemannianDiskArea g u ≤ riemannianDiskArea g v := by
  have harea : riemannianDiskArea g u = riemannianDiskEnergy g u :=
    riemannianDiskArea_eq_energy_of_conformal g u hconf
  rw [harea, heq]
  exact disk_energy_inf_le_area_of_weakJordanTrace g hγ him hv hL

theorem isMorreyDisk_of_energy_attainment
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle)))
    (him : ∀ t : ℝ,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) t 1 ≠ 0)
    {u : C(closedDisk, M)} (hsmooth : DiskSmoothInterior (E := E) u)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z)
    (hharm : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension u) z = 0)
    (hfinite : IntegrableOn (diskMapEnergyDensity g (diskExtension u)) (Metric.closedBall 0 1))
    (htrace : DiskWeakJordanTrace γ u)
    (heq : riemannianDiskEnergy g u = sInf
      ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ)) :
    IsMorreyDisk g γ u := by
  have hmin : ∀ v : C(closedDisk, M), DiskWeakJordanTrace γ v →
      (∃ L : ℝ≥0, ∀ z w : closedDisk,
        riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) →
      riemannianDiskArea g u ≤ riemannianDiskArea g v := by
    rintro v hv ⟨L, hL⟩
    exact riemannianDiskArea_le_of_energy_attainment_of_conformal g hγ him hconf heq hv hL
  refine ⟨hsmooth, hconf, hharm, hfinite, htrace, hmin, ?_⟩
  intro v hv hboundary
  obtain ⟨V, hV⟩ := exists_smoothDiskExtension_of_diskSmoothUpToBoundary hv
  exact hmin v (DiskWeakJordanTrace.of_diskTrace_eq hboundary) (hV.lipschitz g)

end DifferentialGeometry.Geometry

end

end

import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Lipschitz
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskCriterion
import Mathlib.Topology.Order.IsLUB

noncomputable section

open Bundle Manifold DifferentialGeometry Filter Set MeasureTheory ContinuousMap
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def riemannianDiskEnergy (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : closedDisk → M) : ℝ :=
  ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z

theorem riemannianDiskEnergy_nonneg (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (u : closedDisk → M) : 0 ≤ riemannianDiskEnergy g u :=
  integral_nonneg fun z =>
    div_nonneg (add_nonneg (metric_inner_self_nonneg g (diskExtension u z) _)
      (metric_inner_self_nonneg g (diskExtension u z) _)) (by norm_num)

def weaklyMonotoneDiskCompetitors (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M) :
    Set C(closedDisk, M) :=
  {u | DiskWeakJordanTrace γ u ∧ ∃ L : ℝ≥0, ∀ z w : closedDisk,
    riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w}

theorem spanningDiskCompetitors_subset_weaklyMonotoneDiskCompetitors
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M) :
    spanningDiskCompetitors g γ ⊆ weaklyMonotoneDiskCompetitors g γ := by
  rintro u ⟨htrace, hLip⟩
  exact ⟨DiskWeakJordanTrace.of_diskTrace_eq htrace, hLip⟩

theorem exists_weakly_monotone_disk_energy_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    ∃ u : ℕ → C(closedDisk, M),
      (∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ) ∧
      Antitone (fun n => riemannianDiskEnergy g (u n)) ∧
      Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
        (𝓝 (sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) '' weaklyMonotoneDiskCompetitors g γ))) := by
  classical
  have hnonempty : (weaklyMonotoneDiskCompetitors g γ).Nonempty :=
    hfinite.mono (spanningDiskCompetitors_subset_weaklyMonotoneDiskCompetitors g γ)
  have hbound : BddBelow ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) '' weaklyMonotoneDiskCompetitors g γ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨u, _, rfl⟩
    exact riemannianDiskEnergy_nonneg g u
  obtain ⟨e, heanti, heconv, he⟩ :=
    exists_seq_tendsto_sInf (hnonempty.image (fun v : C(closedDisk, M) => riemannianDiskEnergy g v)) hbound
  choose u hu hue using he
  refine ⟨u, hu, ?_, ?_⟩
  · simpa only [hue] using heanti
  · simpa only [hue] using heconv

variable [FiniteDimensional ℝ E] [T3Space M]

theorem weaklyMonotoneDiskCompetitor_integrable_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : u ∈ weaklyMonotoneDiskCompetitors g γ) :
    IntegrableOn (diskMapEnergyDensity g (diskExtension u)) (Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨_, L, hL⟩ := hu
  exact integrable_diskMapEnergyDensity g hL

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold DifferentialGeometry Filter Set MeasureTheory
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

theorem exists_bounded_weakly_monotone_disk_energy_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    ∃ (u : ℕ → C(closedDisk, M)) (B : ℝ), 0 ≤ B ∧
      (∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ) ∧
      (∀ n, IntegrableOn (diskMapEnergyDensity g (diskExtension (u n)))
        (Metric.closedBall (0 : ℂ) 1)) ∧
      (∀ n, riemannianDiskEnergy g (u n) ≤ B) ∧
      Antitone (fun n => riemannianDiskEnergy g (u n)) ∧
      Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
        (𝓝 (sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
          weaklyMonotoneDiskCompetitors g γ))) := by
  obtain ⟨u, hu, hanti, hlim⟩ :=
    exists_weakly_monotone_disk_energy_minimizing_sequence g γ hfinite
  exact ⟨u, riemannianDiskEnergy g (u 0), riemannianDiskEnergy_nonneg g (u 0), hu,
    fun n => weaklyMonotoneDiskCompetitor_integrable_energy g (hu n),
    fun n => hanti (Nat.zero_le n), hanti, hlim⟩

end DifferentialGeometry.Geometry

end

import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalEnergy
import DifferentialGeometry.Geometry.Measure.Area.SpanningCompetitors
import DifferentialGeometry.Analysis.Integration.Measure.UniformIntegrability








noncomputable section

open Bundle Manifold DifferentialGeometry MeasureTheory Set ContinuousMap
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




structure IsSmoothEmbeddedLoop (γ : freeLoop M) : Prop where
  smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle))
  embedding : Topology.IsEmbedding γ
  immersed : ∀ t : ℝ,
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => γ (s : loopCircle)) t 1 ≠ 0



def IsWeaklyMonotoneOnce (σ : C(loopCircle, loopCircle)) : Prop :=
  ∃ ψ : ℝ → ℝ, Continuous ψ ∧ (∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle)) ∧
    ((Monotone ψ ∧ ∀ t, ψ (t + 1) = ψ t + 1) ∨
      (Antitone ψ ∧ ∀ t, ψ (t + 1) = ψ t - 1))



def DiskWeakJordanTrace (γ : freeLoop M) (u : C(closedDisk, M)) : Prop :=
  ∃ σ : C(loopCircle, loopCircle), IsWeaklyMonotoneOnce σ ∧ diskTrace u = γ.comp σ






structure IsMorreyDisk (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) (u : C(closedDisk, M)) : Prop where
  smoothInterior : DiskSmoothInterior (E := E) u
  conformal : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z
  harmonic : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension u) z = 0
  finiteEnergy : IntegrableOn (diskMapEnergyDensity g (diskExtension u)) (Metric.closedBall 0 1)
  trace : DiskWeakJordanTrace γ u
  minimizesLipschitz : ∀ v : C(closedDisk, M), DiskWeakJordanTrace γ v →
    (∃ L : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) →
        riemannianDiskArea g u ≤ riemannianDiskArea g v
  minimizesSmooth : ∀ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v → diskTrace v = γ →
    riemannianDiskArea g u ≤ riemannianDiskArea g v



theorem IsMorreyDisk.integrableArea {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)} (h : IsMorreyDisk g γ u) :
    IntegrableOn (riemannianAreaDensity g (diskExtension u)) (Metric.closedBall 0 1) :=
  diskArea_integrable_of_conformal_energy g u h.conformal h.finiteEnergy

theorem IsMorreyDisk.exists_pos_integral_energy_lt
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (h : IsMorreyDisk g γ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ a : ℂ,
      (∫ z in Metric.closedBall a r ∩ Metric.closedBall (0 : ℂ) 1,
        diskMapEnergyDensity g (diskExtension u) z) < ε := by
  obtain ⟨r, hr, hbound⟩ := h.finiteEnergy.exists_pos_integral_norm_closedBall_lt hε
  refine ⟨r, hr, fun a => ?_⟩
  have hle := norm_integral_le_integral_norm
    (μ := volume.restrict (Metric.closedBall a r ∩ Metric.closedBall (0 : ℂ) 1))
    (diskMapEnergyDensity g (diskExtension u))
  rw [Real.norm_eq_abs] at hle
  exact ((le_abs_self _).trans hle).trans_lt (hbound a)

end DifferentialGeometry.Geometry

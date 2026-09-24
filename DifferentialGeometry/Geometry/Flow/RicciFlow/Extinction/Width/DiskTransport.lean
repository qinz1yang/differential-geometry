import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Comparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiffeomorphismTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauBridge

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width
open Surgery.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A]
  [T2Space Q] [T2Space A]

theorem exists_spanning_disk_of_postcomposeDiffeomorph
    (g : SmoothRiemannianMetric I Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A)
    (gamma : ContinuousFreeLoop Q) (v : LipschitzDisk g)
    (htrace : ∀ theta, v.map (diskBoundary theta) = gamma theta) :
    ∃ w : DiskCompetitor (Diffeomorph.pullbackMetricCross g Φ.symm)
        ((⟨Φ, Φ.continuous⟩ : C(Q, A)).comp gamma),
      (∀ z, w.1.map z = Φ (v.map z)) ∧
      w.1.map ∈ Geometry.spanningDiskCompetitors (Diffeomorph.pullbackMetricCross g Φ.symm)
        ((⟨Φ, Φ.continuous⟩ : C(Q, A)).comp gamma) ∧
      diskArea (Diffeomorph.pullbackMetricCross g Φ.symm) w.1.map = diskArea g v.map := by
  have hf : ∀ x y : Q, riemannianEDistOf (Diffeomorph.pullbackMetricCross g Φ.symm)
      (Φ x) (Φ y) ≤ (1 : ℝ≥0∞) * riemannianEDistOf g x y := by
    intro x y
    rw [DifferentialGeometry.Geometry.Metric.edistOf_pullbackMetricCross]
    simp only [Diffeomorph.symm_apply_apply, one_mul, le_refl]
  let w : DiskCompetitor (Diffeomorph.pullbackMetricCross g Φ.symm)
      ((⟨Φ, Φ.continuous⟩ : C(Q, A)).comp gamma) :=
    DiskCompetitor.postcompose g _ ⟨Φ, Φ.continuous⟩ 1 hf gamma ⟨v, htrace⟩
  refine ⟨w, fun z => rfl, mem_spanningDiskCompetitors_of_diskCompetitor _ _ w, ?_⟩
  rw [diskArea_pullbackMetricCross]
  congr 1
  funext z
  exact Φ.symm_apply_apply (v.map z)

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

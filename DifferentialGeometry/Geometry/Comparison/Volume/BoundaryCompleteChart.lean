import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryMetricChart
import DifferentialGeometry.Geometry.Metric.Construction.LocalExtension
import DifferentialGeometry.Geometry.Metric.CompleteMetricExists

/-!
The original boundary-chart tensor is realized locally by an actual complete ambient
metric. Completeness is on the model vector space and does not change the original metric.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundary : HasSmoothBoundary E H I]
  {M : Type*} [manifoldTopology : TopologicalSpace M]
  [manifoldCharts : ChartedSpace H M] [manifoldSmooth : IsManifold I ∞ M]

theorem exists_boundary_complete_chart (g : SmoothRiemannianMetric I M) (p : M)
    (hp : I.IsBoundaryPoint p) :
    ∃ G : SmoothRiemannianMetric 𝓘(ℝ, E) E,
      RiemannianMetricComplete G ∧ ∃ U : Opens E,
        extChartAt I p p ∈ U ∧ (U : Set E) ⊆ I.symm ⁻¹' (chartAt H p).target ∧
          ∀ y ∈ (U : Set E) ∩ range I, ∀ v w : E,
            G.inner y v w = metricFlatModelInChart g p y v w := by
  obtain ⟨O, hpO, hOtarget, k, hk⟩ := exists_boundaryChart_metric_extension g p hp
  obtain ⟨G, V, hVO, hpV, hGV⟩ :=
    Geometry.Riemannian.exists_model_metric_extension O k ⟨extChartAt I p p, hpO⟩
  obtain ⟨G', S, hcomplete, hS, hpS, hG', hle⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact G
      (isCompact_singleton (x := extChartAt I p p))
  let U : Opens E := ⟨(V : Set E) ∩ S, V.isOpen.inter hS⟩
  refine ⟨G', hcomplete, U, ⟨hpV, hpS (mem_singleton _)⟩,
    fun y hy => hOtarget (hVO hy.1), ?_⟩
  intro y hy v w
  have hfirst : G'.inner y v w = G.inner y v w :=
    congrArg (fun B : TangentSpace 𝓘(ℝ, E) y →L[ℝ]
      TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ => B v w) (hG' y hy.1.2)
  exact hfirst.trans ((hGV ⟨y, hy.1.1⟩ v w).trans
    (hk (Opens.inclusion hVO ⟨y, hy.1.1⟩) hy.2 v w))

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

import DifferentialGeometry.Geometry.Metric.CurveVariation.LocalDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckCylindricalChartBridge

set_option autoImplicit false

noncomputable section

open Bundle Set Manifold Filter
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}
  {neck : NormalizedNeck h δ k} {fixed : StaticCapScaffold}
  {D : ℝ} {m : ℕ} {ε : ℝ}

theorem StaticCapWitness.exists_mem_nhds_collapse_riemannianEDistOf_le
    (w : StaticCapWitness neck fixed D m ε) (p : neckCentralDomain δ) :
    ∃ U ∈ 𝓝 p, ∀ y ∈ U, ∀ z ∈ U,
      riemannianEDistOf w.metric (w.collapse y) (w.collapse z) ≤
        riemannianEDistOf h (neck.chart y.1) (neck.chart z.1) := by
  let : RegularSpace M := regularSpace_of_chartedSpace ThreeModel
  have hchart : _root_.Topology.IsOpenEmbedding (neck.chart : neckBuffer δ → M) :=
    DifferentialGeometry.Topology.Manifold.isOpenEmbedding_of_injective_immersion
      neck.chart neck.chart_smooth.contMDiff neck.chart_smooth.isEmbedding.injective
      (fun z => DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt
        NeckCylinderModel ThreeModel neck.chart z (neck.chart_smooth.isImmersion.isImmersionAt z))
      (by simp [Module.finrank_prod, ThreeSpace])
  have hparam : _root_.Topology.IsOpenEmbedding
      (fun x : neckCentralDomain δ => neck.chart x.1) :=
    hchart.comp (isOpen_neckCentralDomain δ).isOpenEmbedding_subtypeVal
  exact DifferentialGeometry.Geometry.local_riemannianEDistOf_le_of_riemannianCurveVariation_le h w.metric
    (fun x : neckCentralDomain δ => neck.chart x.1) hparam w.collapse
    w.collapse_length p

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

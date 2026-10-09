import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.TerminalRegion

section

set_option autoImplicit false
noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem terminalRegularOpen_eq :
    G.terminalRegularOpen =
      DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion G.flow.base.metric a s := by
  apply TopologicalSpace.Opens.ext
  ext x
  constructor
  · rintro ⟨U, hU, hx, t, ht, C, hC, hbound⟩
    refine ⟨⟨U, hU⟩, hx, t, ht, C, hC, ?_⟩
    intro y hy τ hτ
    simpa only [riemannNorm, SolutionFamily.rm04, Geometry.Curvature.metricRm04_apply] using
      hbound y hy τ hτ
  · rintro ⟨U, hx, t, ht, C, hC, hbound⟩
    refine ⟨U, U.isOpen, hx, t, ht, C, hC, ?_⟩
    intro y hy τ hτ
    simpa only [riemannNorm, SolutionFamily.rm04, Geometry.Curvature.metricRm04_apply] using
      hbound y hy τ hτ

theorem terminalMetricConverges_of_tendsto
    (g : SmoothRiemannianMetric ThreeModel G.terminalRegularOpen)
    (h : ∀ K : Set G.terminalRegularOpen, IsCompact K → ∀ j : ℕ,
      Tendsto (fun t => metricDerivENormSupOn K j
        ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) g g) (𝓝[<] s) (𝓝 0)) :
    G.TerminalMetricConverges g := by
  intro K hK j ε hε
  have hsmall : ∀ᶠ t in 𝓝[<] s,
      metricDerivENormSupOn K j ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) g g <
        ENNReal.ofReal ε := (h K hK j).eventually (gt_mem_nhds (by simpa using hε))
  obtain ⟨d, hd, hbound⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).mp hsmall
  refine ⟨max a d, ⟨le_max_left _ _, max_lt G.lt hd⟩, ?_⟩
  intro t ht x hx
  exact metricDerivNorm_lt_of_sup_lt K j _ g g
    (hbound ⟨lt_of_le_of_lt (le_max_right a d) ht.1, ht.2⟩) le_rfl hx

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

end

section

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

private def terminalLimitMetricOfOpenEq {U : TopologicalSpace.Opens P.Carrier}
    (hU : G.terminalRegularOpen = U) (g : SmoothRiemannianMetric ThreeModel U)
    (h : ∀ K : Set U, IsCompact K → ∀ j : ℕ,
      Tendsto (fun t => metricDerivENormSupOn K j
        ((G.flow.base.metric t).restrictOpen U) g g) (𝓝[<] s) (𝓝 0)) :
    G.TerminalLimitMetric := by
  subst U
  exact ⟨g, G.terminalMetricConverges_of_tendsto g h⟩

private theorem terminalLimitMetricOfOpenEq_metric_heq {U : TopologicalSpace.Opens P.Carrier}
    (hU : G.terminalRegularOpen = U) (g : SmoothRiemannianMetric ThreeModel U)
    (h : ∀ K : Set U, IsCompact K → ∀ j : ℕ,
      Tendsto (fun t => metricDerivENormSupOn K j
        ((G.flow.base.metric t).restrictOpen U) g g) (𝓝[<] s) (𝓝 0)) :
    HEq (terminalLimitMetricOfOpenEq G hU g h).metric g := by
  subst U
  rfl

def terminalLimitMetricOfIsTerminalLimitMetric
    (gBar : SmoothRiemannianMetric ThreeModel
      (DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion G.flow.base.metric a s))
    (hBar : DifferentialGeometry.PDE.RicciFlow.IsTerminalLimitMetric G.flow.base.metric a s gBar) :
    G.TerminalLimitMetric :=
  terminalLimitMetricOfOpenEq G G.terminalRegularOpen_eq gBar hBar

theorem terminalLimitMetricOfIsTerminalLimitMetric_metric_heq
    (gBar : SmoothRiemannianMetric ThreeModel
      (DifferentialGeometry.PDE.RicciFlow.terminalRegularRegion G.flow.base.metric a s))
    (hBar : DifferentialGeometry.PDE.RicciFlow.IsTerminalLimitMetric G.flow.base.metric a s gBar) :
    HEq (G.terminalLimitMetricOfIsTerminalLimitMetric gBar hBar).metric gBar :=
  terminalLimitMetricOfOpenEq_metric_heq G G.terminalRegularOpen_eq gBar hBar

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

end

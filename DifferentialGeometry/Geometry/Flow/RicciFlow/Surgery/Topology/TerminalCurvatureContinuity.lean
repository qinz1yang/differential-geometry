import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalClosedSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private local instance : IsManifold ThreeModel 1 G.terminalRegularOpen :=
  IsManifold.of_le (n := ∞) (by decide)

private theorem TerminalLimitMetric.closedSolution_riemannNorm
    (L : G.TerminalLimitMetric) {c : ℝ} (hcs : c ≤ s) (t : ℝ)
    (x : G.terminalRegularOpen) :
    Real.sqrt (normSq0S ((L.closedSolution ⊤ hcs).base.metric t)
      (⟨x, mem_univ x⟩ : (⊤ : TopologicalSpace.Opens G.terminalRegularOpen)) 4
      ((L.closedSolution ⊤ hcs).base.rm04 t ⟨x, mem_univ x⟩)) =
      Real.sqrt (normSq0S (L.extendedMetric t) x 4 (metricRm04At (L.extendedMetric t) x)) := by
  simp only [SolutionFamily.rm04, metricRm04_apply, L.closedSolution_metric]
  rw [rmNormSq_restrictOpen]

private theorem TerminalLimitMetric.extendedMetric_riemannNorm_before
    (L : G.TerminalLimitMetric) {t : ℝ} (ht : t < s) (x : G.terminalRegularOpen) :
    Real.sqrt (normSq0S (L.extendedMetric t) x 4 (metricRm04At (L.extendedMetric t) x)) =
      G.riemannNorm t x.val := by
  rw [L.extendedMetric_before ht, rmNormSq_restrictOpen]
  rfl

theorem TerminalLimitMetric.tendsto_riemannNorm
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen) :
    Tendsto (fun t => G.riemannNorm t x.val) (𝓝[<] s)
      (𝓝 (Real.sqrt (normSq0S L.metric x 4 (metricRm04At L.metric x)))) := by
  let W : TopologicalSpace.Opens G.terminalRegularOpen := ⊤
  let xW : W := ⟨x, mem_univ x⟩
  have hc := (L.closedSolution_isSolutionOn W le_rfl G.lt).continuousOn_riemannNorm_time xW
  have hci := hc s (show s ∈ (RealTimeInterval.closed a s G.lt.le).carrier from ⟨G.lt.le, le_rfl⟩)
  have hlim := hci.mono_left (nhdsWithin_mono s Ioo_subset_Icc_self)
  rw [nhdsWithin_Ioo_eq_nhdsLT G.lt] at hlim
  change Tendsto (fun t => Real.sqrt (normSq0S ((L.closedSolution ⊤ G.lt.le).base.metric t)
      xW 4 ((L.closedSolution ⊤ G.lt.le).base.rm04 t xW))) (𝓝[<] s)
      (𝓝 (Real.sqrt (normSq0S ((L.closedSolution ⊤ G.lt.le).base.metric s)
        xW 4 ((L.closedSolution ⊤ G.lt.le).base.rm04 s xW)))) at hlim
  simp only [xW, W, L.closedSolution_riemannNorm, L.extendedMetric_terminal] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact L.extendedMetric_riemannNorm_before ht x

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

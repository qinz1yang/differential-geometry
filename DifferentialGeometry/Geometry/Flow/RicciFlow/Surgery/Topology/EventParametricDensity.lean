import DifferentialGeometry.Geometry.Measure.ParametricIsometry
import DifferentialGeometry.Analysis.Integration.Measure.ParamDensityCongruence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric

noncomputable section

open Set Filter Manifold
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem paramGramMatrix_eq_of_regularCrossing
    {φ : ThreeSpace → E.incoming.terminalRegularOpen} {ψ : ThreeSpace → Q.Carrier}
    {x : ThreeSpace} (hφ : MDifferentiableAt 𝓘(ℝ, ThreeSpace) ThreeModel φ x)
    (hcross : ∀ᶠ y in 𝓝 x, E.RegularCrossing (φ y).val (ψ y)) :
    paramGramMatrix E.outputMetric ψ x = paramGramMatrix E.terminal.metric φ x := by
  obtain ⟨F, _, hx, _, _, hFcross, hmetric⟩ :=
    (hcross.self_of_nhds).exists_survivor_partialDiffeomorph E
  have hstay : ∀ᶠ y in 𝓝 x, φ y ∈ F.source :=
    hφ.continuousAt.preimage_mem_nhds (F.open_source.mem_nhds hx)
  have heq : ψ =ᶠ[𝓝 x] (F : E.incoming.terminalRegularOpen → Q.Carrier) ∘ φ := by
    filter_upwards [hcross, hstay] with y hy hys
    exact E.regularCrossing_right_unique hy (hFcross (φ y) hys)
  rw [paramGramMatrix_eq_of_eventuallyEq E.outputMetric heq]
  exact paramGramMatrix_comp_of_metric_inner_eq E.terminal.metric E.outputMetric
    (F.mdifferentiableAt (by simp) hx) hφ (hmetric (φ x) hx)

theorem paramDensity_eq_of_regularCrossing
    {φ : ThreeSpace → E.incoming.terminalRegularOpen} {ψ : ThreeSpace → Q.Carrier}
    {x : ThreeSpace} (hφ : MDifferentiableAt 𝓘(ℝ, ThreeSpace) ThreeModel φ x)
    (hcross : ∀ᶠ y in 𝓝 x, E.RegularCrossing (φ y).val (ψ y)) :
    paramDensity E.outputMetric ψ x = paramDensity E.terminal.metric φ x := by
  rw [paramDensity_apply, paramDensity_apply, E.paramGramMatrix_eq_of_regularCrossing hφ hcross]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

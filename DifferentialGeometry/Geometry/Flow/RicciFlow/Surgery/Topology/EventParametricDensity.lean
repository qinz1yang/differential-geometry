import DifferentialGeometry.Geometry.Measure.ParametricIsometry
import DifferentialGeometry.Analysis.Integration.Measure.ParamDensityCongruence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetricInner

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
  ext i j
  exact E.metric_inner_eq_of_eventually_regularCrossing φ ψ hφ hcross _ _

theorem paramDensity_eq_of_regularCrossing
    {φ : ThreeSpace → E.incoming.terminalRegularOpen} {ψ : ThreeSpace → Q.Carrier}
    {x : ThreeSpace} (hφ : MDifferentiableAt 𝓘(ℝ, ThreeSpace) ThreeModel φ x)
    (hcross : ∀ᶠ y in 𝓝 x, E.RegularCrossing (φ y).val (ψ y)) :
    paramDensity E.outputMetric ψ x = paramDensity E.terminal.metric φ x := by
  rw [paramDensity_apply, paramDensity_apply, E.paramGramMatrix_eq_of_regularCrossing hφ hcross]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

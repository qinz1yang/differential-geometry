import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric
set_option autoImplicit false
noncomputable section

open Set Manifold TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u v
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem metric_inner_eq_of_eventually_regularCrossing
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {XH : Type*} [TopologicalSpace XH] {I : ModelWithCorners ℝ V XH}
    {X : Type*} [TopologicalSpace X] [ChartedSpace XH X]
    (φ : X → E.incoming.terminalRegularOpen) (ψ : X → Q.Carrier)
    {x : X} (hφ : MDifferentiableAt I ThreeModel φ x)
    (hcross : ∀ᶠ y in 𝓝 x, E.RegularCrossing (φ y).val (ψ y)) :
    ∀ v w : TangentSpace I x,
      E.outputMetric.inner (ψ x)
        (mfderiv I ThreeModel ψ x v) (mfderiv I ThreeModel ψ x w) =
      E.terminal.metric.inner (φ x)
        (mfderiv I ThreeModel φ x v) (mfderiv I ThreeModel φ x w) := by
  obtain ⟨F, _, hx, _, _, hFcross, hmetric⟩ :=
    (hcross.self_of_nhds).exists_survivor_partialDiffeomorph E
  have hstay : ∀ᶠ y in 𝓝 x, φ y ∈ F.source :=
    hφ.continuousAt.preimage_mem_nhds (F.open_source.mem_nhds hx)
  have heq : ψ =ᶠ[𝓝 x] (F : E.incoming.terminalRegularOpen → Q.Carrier) ∘ φ := by
    filter_upwards [hcross, hstay] with y hy hys
    exact E.regularCrossing_right_unique hy (hFcross (φ y) hys)
  intro v w
  rw [heq.mfderiv_eq (I := I) (I' := ThreeModel), heq.self_of_nhds, mfderiv_comp x
    (F.mdifferentiableAt (by simp) hx) hφ]
  exact hmetric (φ x) hx _ _

variable {V XH : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace XH] {I : ModelWithCorners ℝ V XH} [I.Boundaryless]
  {X : Type v} [TopologicalSpace X] [ChartedSpace XH X]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

set_option autoImplicit false
noncomputable section

open Set Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

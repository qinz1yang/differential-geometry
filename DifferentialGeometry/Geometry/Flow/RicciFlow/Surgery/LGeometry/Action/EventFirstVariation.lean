import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs

noncomputable section
open Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
universe u
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem lVelocity_pair_eq_of_eventually_regularCrossing
    (φ : ℝ → ℝ → E.incoming.terminalRegularOpen) (ψ : ℝ → ℝ → Q.Carrier)
    (t r : ℝ)
    (hφ : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ThreeModel
      (fun z : ℝ × ℝ => φ z.1 z.2) (t, r))
    (hcross : ∀ᶠ z : ℝ × ℝ in 𝓝 (t, r), E.RegularCrossing (φ z.1 z.2).val (ψ z.1 z.2)) :
    E.outputMetric.inner (ψ t r)
      (lVelocity (I := ThreeModel) (fun y => ψ y r) t)
      (lVelocity (I := ThreeModel) (ψ t) r) =
    E.terminal.metric.inner (φ t r)
      (lVelocity (I := ThreeModel) (fun y => φ y r) t)
      (lVelocity (I := ThreeModel) (φ t) r) := by
  obtain ⟨F, _, hx, _, _, hFcross, _⟩ :=
    (hcross.self_of_nhds).exists_survivor_partialDiffeomorph E
  have hstay : ∀ᶠ y : ℝ × ℝ in 𝓝 (t, r), φ y.1 y.2 ∈ F.source :=
    hφ.continuousAt.preimage_mem_nhds (F.open_source.mem_nhds hx)
  have heq : (fun z : ℝ × ℝ => ψ z.1 z.2) =ᶠ[𝓝 (t, r)]
      (F : E.incoming.terminalRegularOpen → Q.Carrier) ∘ (fun z => φ z.1 z.2) := by
    filter_upwards [hcross, hstay] with y hy hys
    exact E.regularCrossing_right_unique hy (hFcross _ hys)
  have hψ : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ThreeModel
      (fun z : ℝ × ℝ => ψ z.1 z.2) (t, r) :=
    ((F.mdifferentiableAt (by simp) hx).comp (t, r) hφ).congr_of_eventuallyEq heq
  have hh := E.metric_inner_eq_of_eventually_regularCrossing
    (fun z : ℝ × ℝ => φ z.1 z.2) (fun z => ψ z.1 z.2) hφ hcross (1, 0) (0, 1)
  have hψ₁ := mfderiv_prod_eq_add_apply (v := (1, 0)) hψ
  have hψ₂ := mfderiv_prod_eq_add_apply (v := (0, 1)) hψ
  have hφ₁ := mfderiv_prod_eq_add_apply (v := (1, 0)) hφ
  have hφ₂ := mfderiv_prod_eq_add_apply (v := (0, 1)) hφ
  rw [hψ₁, hψ₂, hφ₁, hφ₂] at hh
  change E.outputMetric.inner (ψ t r)
      ((mfderiv 𝓘(ℝ, ℝ) ThreeModel (fun z => ψ z r) t) 1 +
        (mfderiv 𝓘(ℝ, ℝ) ThreeModel (ψ t) r) 0)
      ((mfderiv 𝓘(ℝ, ℝ) ThreeModel (fun z => ψ z r) t) 0 +
        (mfderiv 𝓘(ℝ, ℝ) ThreeModel (ψ t) r) 1) =
    E.terminal.metric.inner (φ t r)
      ((mfderiv 𝓘(ℝ, ℝ) ThreeModel (fun z => φ z r) t) 1 +
        (mfderiv 𝓘(ℝ, ℝ) ThreeModel (φ t) r) 0)
      ((mfderiv 𝓘(ℝ, ℝ) ThreeModel (fun z => φ z r) t) 0 +
        (mfderiv 𝓘(ℝ, ℝ) ThreeModel (φ t) r) 1) at hh
  simp only [map_zero, add_zero, zero_add] at hh
  convert hh using 1 <;> rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyCurvatureBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingCurvatureLifespan
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctionBound

set_option autoImplicit false

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem OrientedThreeStage.IncomingSlab.one_div_le_endpoint_sub_of_scalar_bound
    {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
    (hsing : G.SingularEndpoint) {a₀ h B : ℝ} (ha₀ : 0 < a₀) (hh : a₀ ≤ h)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (G.flow.base.metric a) h x)
    (hscalar : ∀ x, G.flow.scalar a x ≤ B) :
    1 / (2592 * (2 * Real.sqrt 3 * (max B 0 / 2 + max B (Real.exp 4 / a₀)))) ≤ s - a := by
  apply G.one_div_le_endpoint_sub_of_initial_curvature_bound hsing
  · have hmax : 0 < max B (Real.exp 4 / a₀) :=
      (div_pos (Real.exp_pos 4) ha₀).trans_le (le_max_right _ _)
    have hn : 0 ≤ max B 0 := le_max_right _ _
    positivity
  · intro x
    exact sqrt_normSq0S_le_of_fixedHamiltonIveyRegion (G.flow.base.metric a) x
      ha₀ hh (hfixed x) (hscalar x)

namespace ObservedHistory

variable (H : ObservedHistory.{u}) {parameters : CutoffParameters}
  (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
  {a₀ : ℝ} (ha₀ : 0 < a₀)
  (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
  (hlower : ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)

include records ha₀ hfixed hlower

theorem riemannNorm_initial_le_of_scalar_upper_bound
    (i : Fin H.eventCount) {B : ℝ}
    (hreset : ∀ x : (H.stage i.castSucc).Carrier,
      metricScalarAt (H.initialMetric i.castSucc) x ≤ B) :
    ∀ x : (H.stage i.castSucc).Carrier,
      (H.event i).incoming.riemannNorm (H.time i.castSucc) x ≤
        2 * Real.sqrt 3 * (max B 0 / 2 + max B (Real.exp 4 / a₀)) := by
  have hpin := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hlower
  have htime : H.time i.castSucc ∈ H.stageDomain i.castSucc := by
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, mem_Ico]
    exact ⟨le_rfl, H.time_strictMono i.castSucc_lt_succ⟩
  have hmetric : H.stageMetric i.castSucc (H.time i.castSucc) = H.initialMetric i.castSucc := by
    simpa only [ObservedHistory.stageMetric, Fin.lastCases_castSucc] using H.event_initial i
  intro x
  change Real.sqrt (normSq0S ((H.event i).incoming.flow.base.metric (H.time i.castSucc)) x 4
    (metricRm04At ((H.event i).incoming.flow.base.metric (H.time i.castSucc)) x)) ≤ _
  rw [H.event_initial]
  apply sqrt_normSq0S_le_of_fixedHamiltonIveyRegion (H.initialMetric i.castSucc) x
    (a := a₀ + H.time i.castSucc) ha₀ (by linarith [H.time_nonneg i.castSucc]) ?_ (hreset x)
  simpa only [hmetric] using (hpin.1 i.castSucc (H.time i.castSucc) htime x).1

theorem event_time_gap_of_scalar_upper_bound
    (i : Fin H.eventCount) {B : ℝ}
    (hreset : ∀ x : (H.stage i.castSucc).Carrier,
      metricScalarAt (H.initialMetric i.castSucc) x ≤ B) :
    1 / (2592 * (2 * Real.sqrt 3 * (max B 0 / 2 + max B (Real.exp 4 / a₀)))) ≤
      H.time i.succ - H.time i.castSucc := by
  apply (H.event i).incoming.one_div_le_endpoint_sub_of_initial_curvature_bound (records i).singular
  · have hmax : 0 < max B (Real.exp 4 / a₀) :=
      (div_pos (Real.exp_pos 4) ha₀).trans_le (le_max_right _ _)
    have hn : 0 ≤ max B 0 := le_max_right _ _
    positivity
  · exact H.riemannNorm_initial_le_of_scalar_upper_bound records ha₀ hfixed hlower i hreset

theorem eventCount_le_of_scalar_upper_bound
    {B T : ℝ} (hT : H.horizon ≤ T)
    (hreset : ∀ i : Fin H.eventCount, ∀ x : (H.stage i.castSucc).Carrier,
      metricScalarAt (H.initialMetric i.castSucc) x ≤ B) :
    (H.eventCount : ℝ) ≤
      T * (2592 * (2 * Real.sqrt 3 * (max B 0 / 2 + max B (Real.exp 4 / a₀)))) := by
  let Q := 2 * Real.sqrt 3 * (max B 0 / 2 + max B (Real.exp 4 / a₀))
  have hQ : 0 < Q := by
    have hmax : 0 < max B (Real.exp 4 / a₀) :=
      (div_pos (Real.exp_pos 4) ha₀).trans_le (le_max_right _ _)
    have hn : 0 ≤ max B 0 := le_max_right _ _
    dsimp only [Q]
    positivity
  have hgap : ∀ i : Fin H.eventCount,
      H.time i.castSucc + 1 / (2592 * Q) ≤ H.time i.succ := by
    intro i
    have h := H.event_time_gap_of_scalar_upper_bound records ha₀ hfixed hlower i (hreset i)
    change 1 / (2592 * Q) ≤ _ at h
    linarith
  have h := H.eventCount_le_div_of_gap (by positivity) hgap (H.time_le_horizon.trans hT)
  simpa only [one_div, div_inv_eq_mul, Q] using h

theorem eventCount_le_of_output_scalar_upper_bound
    {B T : ℝ} (hT : H.horizon ≤ T)
    (hinitial : ∀ x : (H.stage 0).Carrier, metricScalarAt (H.initialMetric 0) x ≤ B)
    (houtput : ∀ i : Fin H.eventCount, ∀ x : (H.stage i.succ).Carrier,
      metricScalarAt (H.event i).outputMetric x ≤ B) :
    (H.eventCount : ℝ) ≤
      T * (2592 * (2 * Real.sqrt 3 * (max B 0 / 2 + max B (Real.exp 4 / a₀)))) := by
  have hreset : ∀ j : Fin (H.eventCount + 1), ∀ x : (H.stage j).Carrier,
      metricScalarAt (H.initialMetric j) x ≤ B := by
    refine Fin.cases hinitial ?_
    intro i x
    rw [← H.event_output i]
    exact houtput i x
  exact H.eventCount_le_of_scalar_upper_bound records ha₀ hfixed hlower hT
    (fun i => hreset i.castSucc)

end ObservedHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

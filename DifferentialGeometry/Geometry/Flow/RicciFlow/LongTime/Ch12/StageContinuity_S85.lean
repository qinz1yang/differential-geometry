import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeStages_S70
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabEndpoints
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility

set_option autoImplicit false

/-!
# CH12-S85 / G1a: continuity in time of `inner` and `ricciTensor` of the stage metrics at fixed `(z, V)`

On the time domain `stageDomain j` of a stage `j` of an observed history, `r ↦ g_r(V,V)` and
`r ↦ Ric_{g_r}(V,V)` are continuous (`stage_inner_ricci_continuousOn_S85`); `actS_mem_stageDomain_S85`
puts every `r ∈ [0, horizon]` in the domain of its active stage.
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

theorem incoming_inner_ricci_continuousOn_S85 {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) (z : P.Carrier) (V : TangentSpace ThreeModel z) :
    ContinuousOn (fun r => ricciTensor (G.flow.base.metric r) z V V) (Ico a s) ∧
      ContinuousOn (fun r => (G.flow.base.metric r).inner z V V) (Ico a s) := by
  refine ⟨?_, G.equation.smoothMetric.coeff_cont z V V⟩
  have heval := tensor0SFamilyContinuousOnSet.eval_continuous
    (I := ThreeModel) (M := P.Carrier) (s := 2) G.equation.ricciCont
    (P := Ico a s) (τ := fun t => t.1) (b := fun _ => z)
    continuous_subtype_val (fun t => t.2) continuous_const
    (v := fun i _ => vec2 V V i) (fun _ => continuous_const)
  have h : ContinuousOn (fun t => G.flow.ricciAt t z (vec2 V V)) (Ico a s) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact heval
  refine h.congr (fun t _ => ?_)
  exact (metricRicciAt_apply_eq_ricciTensor (G.flow.base.metric t) z V V).symm

theorem closed_inner_ricci_continuousOn_S85 {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.ClosedSlab a s) (z : P.Carrier) (V : TangentSpace ThreeModel z) :
    ContinuousOn (fun r => ricciTensor (G.flow.base.metric r) z V V) (Icc a s) ∧
      ContinuousOn (fun r => (G.flow.base.metric r).inner z V V) (Icc a s) := by
  refine ⟨(G.ricciAt_continuousOn z V V).congr (fun t _ => ?_),
    G.equation.smoothMetric.coeff_cont z V V⟩
  exact (metricRicciAt_apply_eq_ricciTensor (G.flow.base.metric t) z V V).symm

theorem stage_inner_ricci_continuousOn_S85 (K : ObservedHistory.{u}) (j : Fin (K.eventCount + 1))
    (z : (K.stage j).Carrier) (V : TangentSpace ThreeModel z) :
    ContinuousOn (fun r => ricciTensor (K.stageMetric j r) z V V) (K.stageDomain j) ∧
      ContinuousOn (fun r => (K.stageMetric j r).inner z V V) (K.stageDomain j) := by
  revert z V
  cases j using Fin.lastCases with
  | last =>
    intro z V
    have hdom : K.stageDomain (Fin.last K.eventCount) =
        Icc (K.time (Fin.last K.eventCount)) K.horizon := by
      ext τ
      exact ObservedHistory.mem_stageDomain_last K τ
    rw [hdom]
    by_cases h : K.time (Fin.last K.eventCount) < K.horizon
    · have hm : ∀ τ, K.stageMetric (Fin.last K.eventCount) τ = (K.finalSlab h).flow.base.metric τ :=
        fun τ => ObservedHistory.stageMetric_last_of_lt (H := K) (h := h) τ
      simp only [hm]
      exact closed_inner_ricci_continuousOn_S85 (K.finalSlab h) z V
    · have hm : ∀ τ, K.stageMetric (Fin.last K.eventCount) τ = K.initialMetric (Fin.last K.eventCount) :=
        fun τ => ObservedHistory.stageMetric_last_of_le (H := K) (not_lt.mp h) τ
      simp only [hm]
      exact ⟨continuousOn_const, continuousOn_const⟩
  | cast i =>
    intro z V
    have hdom : K.stageDomain i.castSucc = Ico (K.time i.castSucc) (K.time i.succ) := by
      rw [ObservedHistory.stageDomain, Fin.lastCases_castSucc]
    rw [hdom]
    simp only [ObservedHistory.stageMetric_castSucc_apply]
    exact incoming_inner_ricci_continuousOn_S85 (K.event i).incoming z V

theorem actS_mem_stageDomain_S85 (K : ObservedHistory.{u}) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) K.horizon) :
    r ∈ K.stageDomain (actS_S70 K r) := by
  have h1 := actS_time_le_S70 K hr
  generalize hj : actS_S70 K r = j at h1 ⊢
  cases j using Fin.lastCases with
  | last =>
    rw [ObservedHistory.mem_stageDomain_last]
    exact ⟨h1, hr.2⟩
  | cast i =>
    rw [ObservedHistory.stageDomain, Fin.lastCases_castSucc]
    refine ⟨h1, ?_⟩
    by_contra hnot
    have h2 := le_actS_S70 K hr (j := i.succ) (not_lt.mp hnot)
    rw [hj] at h2
    exact absurd h2 (not_le.mpr (Fin.castSucc_lt_succ (i := i)))

/-- The LTF03 vector defect `|2 r Ric(V,V) + g(V,V)| ≤ η g(V,V)` of the stage metric `g = stageMetric j r`
at one point and one vector. -/
def DefectAt_S85 (K : ObservedHistory.{u}) (j : Fin (K.eventCount + 1)) (z : (K.stage j).Carrier)
    (V : TangentSpace ThreeModel z) (η r : ℝ) : Prop :=
  |2 * r * ricciTensor (K.stageMetric j r) z V V + (K.stageMetric j r).inner z V V| ≤
    η * (K.stageMetric j r).inner z V V

/-- Closedness of the vector defect in time on a stage: left-closedness at the right end. -/
theorem defectAt_closed_S85 (K : ObservedHistory.{u}) (j : Fin (K.eventCount + 1))
    (z : (K.stage j).Carrier) (V : TangentSpace ThreeModel z) (η : ℝ) {a s : ℝ} (has : a < s)
    (hdom : Icc a s ⊆ K.stageDomain j) (h : ∀ r ∈ Ico a s, DefectAt_S85 K j z V η r) :
    DefectAt_S85 K j z V η s := by
  obtain ⟨hR, hG⟩ := stage_inner_ricci_continuousOn_S85 K j z V
  have hF : ContinuousOn (fun r => |2 * r * ricciTensor (K.stageMetric j r) z V V +
      (K.stageMetric j r).inner z V V|) (Icc a s) :=
    (((continuousOn_const.mul continuousOn_id).mul (hR.mono hdom)).add (hG.mono hdom)).abs
  have hG' : ContinuousOn (fun r => η * (K.stageMetric j r).inner z V V) (Icc a s) :=
    continuousOn_const.mul (hG.mono hdom)
  have hcl : s ∈ closure (Ico a s) := by
    rw [closure_Ico has.ne]
    exact ⟨has.le, le_rfl⟩
  exact ContinuousWithinAt.closure_le hcl
    ((hF s ⟨has.le, le_rfl⟩).mono Ico_subset_Icc_self)
    ((hG' s ⟨has.le, le_rfl⟩).mono Ico_subset_Icc_self) h

end GC.LongTime.Ch12

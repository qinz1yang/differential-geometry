import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.HistoryWidthJump
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ObservedComparisonRecord

noncomputable section

universe u

open Bundle Manifold Set Filter MeasureTheory CategoryTheory
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology

abbrev ChildComparisonData {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {parameters : CutoffParameters} (G : GeometricCutoffRecord H i parameters) : Prop :=
  ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
      C((G.Parent c).Carrier, (G.Child c).Carrier),
    (∀ c, ∃ K : G.ComparisonSupport c, f c = K.canonicalWholeParentMap) ∧
      (∀ c, integralHomologyMap 3 (f c) (fundamentalClass (G.Parent c).orientation) =
        fundamentalClass (G.Child c).orientation) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
              riemannianEDistOf ((H.stage i.castSucc).componentMetric
                ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y

theorem rfs_child_comparison_data
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
    (G : GeometricCutoffRecord H i parameters)
    (hSC : ∀ p : ConnectedComponents (H.stage i.castSucc).Carrier,
      SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier) :
    ChildComparisonData G :=
  G.rfs_child_comparison hSC

theorem historyWidth_event_jump_of_childComparison (H : ObservedHistory.{u})
    (parameters : CutoffParameters)
    (cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    (i : Fin H.eventCount)
    (hchild : ChildComparisonData (cutoff i)) :
    ENNReal.ofReal (historyWidth H h0 terminal (historyStageTime H i.succ)) ≤
      liminf (fun t => ENNReal.ofReal (historyWidth H h0 terminal t))
        (𝓝[<] (historyStageTime H i.succ)) := by
  let chain := finiteAncestorChain H terminal
  let SC := rfs_simply_connected_history H h0
  let G := cutoff i
  let c := chain.component i.succ
  let p := G.transition.childParent c
  let w : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal
    (componentWidth (H.stage i.castSucc) ((H.event i).incoming.flow.base.metric s) p
      (SC i.castSucc p))
  have hleft : ENNReal.ofReal (historyWidth H h0 terminal (historyStageTime H i.succ)) =
      ENNReal.ofReal (componentWidth (H.stage i.succ) (H.event i).outputMetric c
        (SC i.succ c)) := by
    rw [historyWidth_stageTime, ← H.event_output i]
  rw [hleft]
  have h₁ : ENNReal.ofReal (componentWidth (H.stage i.succ) (H.event i).outputMetric c
      (SC i.succ c)) ≤ liminf w (𝓝[<] (H.time i.succ)) :=
    rfs_actual_width_jump_of_child_comparison G (SC i.castSucc) c hchild
  have hcoe : Tendsto (fun t : Icc (0 : ℝ) H.horizon => t.1)
      (𝓝[<] (historyStageTime H i.succ)) (𝓝[<] (H.time i.succ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨(continuous_subtype_val.tendsto (historyStageTime H i.succ)).mono_left inf_le_left,
      self_mem_nhdsWithin⟩
  have h₂ := hcoe.liminf_le_liminf_comp (u := w)
  have heq : (w ∘ fun t : Icc (0 : ℝ) H.horizon => t.1) =ᶠ[𝓝[<]
      (historyStageTime H i.succ)]
      (fun t => ENNReal.ofReal (historyWidth H h0 terminal t)) := by
    filter_upwards [hcoe.eventually (Ioo_mem_nhdsLT (H.event i).incoming.lt)] with t ht
    rw [historyWidth_incoming H h0 terminal i t ⟨ht.1.le, ht.2⟩]
    change w t.1 = ENNReal.ofReal (componentWidth (H.stage i.castSucc)
      ((H.event i).incoming.flow.base.metric t.1) (chain.component i.castSucc)
      (SC i.castSucc _))
    rw [chain.parent_eq i]
  exact h₁.trans (h₂.trans_eq (liminf_congr heq))

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

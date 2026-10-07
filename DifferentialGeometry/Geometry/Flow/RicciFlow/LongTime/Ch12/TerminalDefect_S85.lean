import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RicciJetConv_S85
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WeakEvent_S85

set_option autoImplicit false

/-!
# CH12-S85 / G2b: the vector defect passes to the terminal metric of an incoming slab

If the flow metrics `g_t` (restricted to the terminal regular open set) satisfy the vector defect
`|2 t Ric(V,V) + g_t(V,V)| ≤ η g_t(V,V)` for `t ∈ [a', s)` at a point `z`, then the terminal limit metric
`gbar` satisfies it at `z` with `t = s` (`TerminalMetricConverges` gives `C²` convergence at `z`).
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

theorem terminal_defect_of_flow_defect_S85 {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) (gbar : SmoothRiemannianMetric ThreeModel G.terminalRegularOpen)
    (hconv : G.TerminalMetricConverges gbar) (z : G.terminalRegularOpen)
    (V : TangentSpace ThreeModel z) {η a' : ℝ} (ha' : a' < s)
    (hdef : ∀ t ∈ Ico a' s,
      |2 * t * ricciTensor ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) z V V +
          ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen).inner z V V| ≤
        η * ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen).inner z V V) :
    |2 * s * ricciTensor gbar z V V + gbar.inner z V V| ≤ η * gbar.inner z V V := by
  classical
  let _ : SecondCountableTopology P.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
  let _ : LocallyCompactSpace G.terminalRegularOpen :=
    ChartedSpace.locallyCompactSpace ThreeSpace G.terminalRegularOpen
  have hK : IsCompact ({z} : Set G.terminalRegularOpen) := isCompact_singleton
  set gt : ℝ → SmoothRiemannianMetric ThreeModel G.terminalRegularOpen :=
    fun t => (G.flow.base.metric t).restrictOpen G.terminalRegularOpen with hgt
  have hev : ∀ δ : ℝ, 0 < δ → ∀ᶠ t in 𝓝[<] s, ∀ j : ℕ, j ≤ 2 →
      metricDerivNorm j (gt t) gbar gbar z < δ := by
    intro δ hδ
    obtain ⟨d0, hd0, h0⟩ := hconv _ hK 0 δ hδ
    obtain ⟨d1, hd1, h1⟩ := hconv _ hK 1 δ hδ
    obtain ⟨d2, hd2, h2⟩ := hconv _ hK 2 δ hδ
    have hmax : max d0 (max d1 d2) < s := max_lt hd0.2 (max_lt hd1.2 hd2.2)
    filter_upwards [Ioo_mem_nhdsLT hmax] with t ht j hj
    have ht0 : t ∈ Ioo d0 s := ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩
    have ht1 : t ∈ Ioo d1 s :=
      ⟨((le_max_left _ _).trans (le_max_right _ _)).trans_lt ht.1, ht.2⟩
    have ht2 : t ∈ Ioo d2 s :=
      ⟨((le_max_right _ _).trans (le_max_right _ _)).trans_lt ht.1, ht.2⟩
    interval_cases j
    · exact h0 t ht0 z rfl
    · exact h1 t ht1 z rfl
    · exact h2 t ht2 z rfl
  have hRic : Tendsto (fun t => ricciTensor (gt t) z V V) (𝓝[<] s)
      (𝓝 (ricciTensor gbar z V V)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hu⟩ := ricci_inner_close_of_jet_S85 gbar z V hε
    filter_upwards [hev δ hδ] with t ht
    rw [Real.dist_eq]
    exact (hu (gt t) ht).1
  have hInn : Tendsto (fun t => (gt t).inner z V V) (𝓝[<] s) (𝓝 (gbar.inner z V V)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hu⟩ := ricci_inner_close_of_jet_S85 gbar z V hε
    filter_upwards [hev δ hδ] with t ht
    rw [Real.dist_eq]
    exact (hu (gt t) ht).2
  have htime : Tendsto (fun t : ℝ => 2 * t) (𝓝[<] s) (𝓝 (2 * s)) :=
    ((tendsto_id.const_mul 2).mono_left nhdsWithin_le_nhds)
  have hF : Tendsto (fun t => η * (gt t).inner z V V -
      |2 * t * ricciTensor (gt t) z V V + (gt t).inner z V V|) (𝓝[<] s)
      (𝓝 (η * gbar.inner z V V - |2 * s * ricciTensor gbar z V V + gbar.inner z V V|)) :=
    (hInn.const_mul η).sub (((htime.mul hRic).add hInn).abs)
  have hnn : ∀ᶠ t in 𝓝[<] s, 0 ≤ η * (gt t).inner z V V -
      |2 * t * ricciTensor (gt t) z V V + (gt t).inner z V V| := by
    filter_upwards [Ico_mem_nhdsLT ha'] with t ht
    exact sub_nonneg.mpr (hdef t ht)
  exact sub_nonneg.mp (ge_of_tendsto hF hnn)

end GC.LongTime.Ch12

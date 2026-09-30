import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBackwardScalar

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem TerminalLimitMetric.inv_max_scalar_sub_terminal_le_on_time_window
    (L : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (x : G.terminalRegularOpen) {c : ℝ} (hac : a ≤ c) (hcs : c < s)
    (hbound : ∀ t ∈ Ioo c s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤
        C * G.flow.scalar t x.val ^ 2) {t : ℝ} (ht : t ∈ Ico c s) :
    |(max q (G.flow.scalar t x.val))⁻¹ - (max q (metricScalarAt L.metric x))⁻¹| ≤
      C * (s - t) := by
  have hlip : LipschitzOnWith C (fun t => (max q (G.flow.scalar t x.val))⁻¹) (Ioo c s) := by
    apply DifferentialGeometry.Analysis.lipschitzOnWith_inv_max_of_quadratic_deriv_bound
      (r' := fun t => derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t)
      hq ordConnected_Ioo
    · intro t ht
      exact (G.equation.scalarTime (K := Ioo c s) ht (fun _ ht => ⟨hac.trans ht.1.le, ht.2⟩) x.val).continuousWithinAt
    · intro t ht _
      exact DifferentialGeometry.Analysis.hasDerivWithinAt_left_of_mem_nhdsLE
        (G.equation.scalarTime (K := Ioo c s) ht (fun _ ht => ⟨hac.trans ht.1.le, ht.2⟩) x.val)
        (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds ht.1 ht.2))
    · exact hbound
  have hlimTerminal : Tendsto (fun t => (max q (G.flow.scalar t x.val))⁻¹)
      (𝓝[<] s) (𝓝 ((max q (metricScalarAt L.metric x))⁻¹)) := by
    exact ((tendsto_const_nhds.max (L.tendsto_metricScalarAt x)).inv₀
      (ne_of_gt (hq.trans_le (le_max_left _ _))))
  have hpoint (t : ℝ) (ht : t ∈ Ioo c s) :
      |(max q (G.flow.scalar t x.val))⁻¹ - (max q (metricScalarAt L.metric x))⁻¹| ≤
        C * (s - t) := by
    apply le_of_tendsto_of_tendsto
      ((tendsto_const_nhds.sub hlimTerminal).abs)
      (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds |>.sub_const t))
    filter_upwards [Ioo_mem_nhdsLT ht.2] with u hu
    have h := hlip.dist_le_mul t ht u ⟨ht.1.trans hu.1,hu.2⟩
    simpa only [id_eq, Real.dist_eq, abs_sub_comm t u,
      abs_of_nonneg (sub_nonneg.mpr hu.1.le)] using h
  rcases eq_or_lt_of_le ht.1 with hta | hta
  · have he : t = c := hta.symm
    subst t
    have hlimInitial : Tendsto (fun t => (max q (G.flow.scalar t x.val))⁻¹)
        (𝓝[>] c) (𝓝 ((max q (G.flow.scalar c x.val))⁻¹)) := by
      have hc := G.equation.scalarTime (K := Ico c s) ⟨le_rfl,hcs⟩ (fun _ ht => ⟨hac.trans ht.1,ht.2⟩) x.val
      have hcont := hc.continuousWithinAt
      have hm : Tendsto (fun t => G.flow.scalar t x.val) (𝓝[>] c)
          (𝓝 (G.flow.scalar c x.val)) := by
        have hIco : Ico c s ∈ 𝓝[>] c :=
          mem_of_superset (Ioo_mem_nhdsGT hcs) (fun _ ht => ⟨ht.1.le, ht.2⟩)
        exact hcont.mono_left (nhdsWithin_le_of_mem hIco)
      exact ((tendsto_const_nhds.max hm).inv₀
        (ne_of_gt (hq.trans_le (le_max_left _ _))))
    apply le_of_tendsto_of_tendsto ((hlimInitial.sub tendsto_const_nhds).abs)
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub
        (tendsto_id.mono_left nhdsWithin_le_nhds)))
    filter_upwards [Ioo_mem_nhdsGT hcs] with t ht
    exact hpoint t ht
  · exact hpoint t ⟨hta, ht.2⟩

theorem TerminalLimitMetric.inv_max_scalar_sub_terminal_le
    (L : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (x : G.terminalRegularOpen)
    (hbound : ∀ t ∈ Ioo a s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤
        C * G.flow.scalar t x.val ^ 2) {t : ℝ} (ht : t ∈ Ico a s) :
    |(max q (G.flow.scalar t x.val))⁻¹ - (max q (metricScalarAt L.metric x))⁻¹| ≤
      C * (s - t) := by
  exact L.inv_max_scalar_sub_terminal_le_on_time_window G hq x le_rfl G.lt hbound ht

theorem TerminalLimitMetric.inv_max_scalar_initial_sub_terminal_le
    (L : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (x : G.terminalRegularOpen)
    (hbound : ∀ t ∈ Ioo a s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤
        C * G.flow.scalar t x.val ^ 2) :
    |(max q (G.flow.scalar a x.val))⁻¹ - (max q (metricScalarAt L.metric x))⁻¹| ≤
      C * (s - a) :=
  L.inv_max_scalar_sub_terminal_le G hq x hbound ⟨le_rfl, G.lt⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

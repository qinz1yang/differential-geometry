import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalMetricCompactComparison
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.Scalar
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self
import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff

open Set Filter Bundle Manifold
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Topology Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.eventually_scalar_close_on_compact (L : G.TerminalLimitMetric)
    {K : Set G.terminalRegularOpen} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝[<] s, ∀ x ∈ K,
      |metricScalarAt (G.flow.base.metric t) x.val - metricScalarAt L.metric x| < ε := by
  let : SecondCountableTopology P.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
  let : LocallyCompactSpace G.terminalRegularOpen :=
    ChartedSpace.locallyCompactSpace ThreeSpace G.terminalRegularOpen
  let : SigmaCompactSpace G.terminalRegularOpen := inferInstance
  let B := Real.sqrt 3 + 1
  obtain ⟨C, hC, hbound⟩ := exists_abs_metricScalarAt_sub_le L.metric
    (K := K) hK (1 / 2) B (by norm_num)
  let δ := min (1 / 2) (ε / (6 * C))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  obtain ⟨d0, hd0, hb0⟩ := L.converges K hK 0 δ hδ
  obtain ⟨d1, hd1, hb1⟩ := L.converges K hK 1 δ hδ
  obtain ⟨d2, hd2, hb2⟩ := L.converges K hK 2 δ hδ
  have hlimit := Ioo_mem_nhdsLT (max_lt hd0.2 (max_lt hd1.2 hd2.2))
  filter_upwards [hlimit] with t ht
  intro x hx
  let gt := (G.flow.base.metric t).restrictOpen G.terminalRegularOpen
  have hd0t : d0 < t := (le_max_left _ _).trans_lt ht.1
  have hd1t : d1 < t := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt ht.1
  have hd2t : d2 < t := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt ht.1
  have hdn : ∀ k ≤ 2, metricDerivNorm k gt L.metric L.metric x ≤ δ := by
    intro k hk
    interval_cases k
    · exact (hb0 t ⟨hd0t, ht.2⟩ x hx).le
    · exact (hb1 t ⟨hd1t, ht.2⟩ x hx).le
    · exact (hb2 t ⟨hd2t, ht.2⟩ x hx).le
  have hbound' := hbound gt L.metric
    (by
      intro y hy v
      have hdiff := metricDifference_abs_le gt L.metric L.metric y v v
      rw [mul_assoc,Real.mul_self_sqrt (DifferentialGeometry.metric_inner_self_nonneg L.metric y v)] at hdiff
      have hn := DifferentialGeometry.metric_inner_self_nonneg L.metric y v
      have hb := hdiff.trans (mul_le_mul_of_nonneg_right ((hb0 t ⟨hd0t,ht.2⟩ y hy).le.trans hδhalf) hn)
      linarith [(abs_le.mp hb).1])
    (by intro y hy v; have hn := DifferentialGeometry.metric_inner_self_nonneg L.metric y v; linarith)
    (by
      intro y hy k hk
      have htri := covNorm_le_add k gt L.metric L.metric y
      have hdn : metricDerivNorm k gt L.metric L.metric y ≤ δ := by
        interval_cases k
        · exact (hb0 t ⟨hd0t,ht.2⟩ y hy).le
        · exact (hb1 t ⟨hd1t,ht.2⟩ y hy).le
        · exact (hb2 t ⟨hd2t,ht.2⟩ y hy).le
      cases k with
      | zero => rw [DifferentialGeometry.Geometry.Metric.metricCovDerivNorm_self_zero] at htri; norm_num only [ThreeSpace,finrank_euclideanSpace,Fintype.card_fin,Nat.cast_ofNat] at htri; dsimp [B]; linarith [hdn.trans hδhalf]
      | succ k => rw [covNorm_self_succ] at htri; dsimp [B]; have hs := Real.sqrt_nonneg 3; linarith [hdn.trans hδhalf])
    (by
      intro y hy k hk
      cases k with
      | zero => rw [DifferentialGeometry.Geometry.Metric.metricCovDerivNorm_self_zero]; norm_num only [ThreeSpace,finrank_euclideanSpace,Fintype.card_fin,Nat.cast_ofNat]; dsimp [B]; linarith
      | succ k => rw [covNorm_self_succ]; dsimp [B]; have hs := Real.sqrt_nonneg 3; linarith)
    x hx
  have hsum : (∑ k ∈ Finset.range 3, metricDerivNorm k gt L.metric L.metric x) ≤ 3 * δ := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    linarith [hdn 0 (by norm_num), hdn 1 (by norm_num), hdn 2 (by norm_num)]
  have hδle : δ ≤ ε / (6 * C) := min_le_right _ _
  have hmul : δ * (6 * C) ≤ ε := (le_div_iff₀ (by positivity)).mp hδle
  have hfinal : C * (3 * δ) < ε := by nlinarith
  rw [← metricScalarAt_restrictOpen (G.flow.base.metric t) G.terminalRegularOpen x]
  exact hbound'.trans_lt ((mul_le_mul_of_nonneg_left hsum hC.le).trans_lt hfinal)


theorem TerminalLimitMetric.tendsto_metricScalarAt (L : G.TerminalLimitMetric)
    (x : G.terminalRegularOpen) :
    Tendsto (fun t => metricScalarAt (G.flow.base.metric t) x.1)
      (𝓝[<] s) (𝓝 (metricScalarAt L.metric x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [L.eventually_scalar_close_on_compact isCompact_singleton hε] with t ht
  simpa only [Real.dist_eq] using ht x (mem_singleton x)

theorem TerminalLimitMetric.scalar_lower_bound_of_tendsto
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen)
    {b : ℝ → ℝ} {B : ℝ} (hb : Tendsto b (𝓝[<] s) (𝓝 B))
    (hbound : ∀ᶠ t in 𝓝[<] s, b t ≤ metricScalarAt (G.flow.base.metric t) x.1) :
    B ≤ metricScalarAt L.metric x :=
  le_of_tendsto_of_tendsto hb (L.tendsto_metricScalarAt x) hbound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}

theorem scalar_lower_bound_output_of_incoming
    (G : GeometricCutoffRecord H i parameters)
    {b : ℝ → ℝ} {B : ℝ} (hB : B ≤ 0)
    (hb : Tendsto b (𝓝[<] H.time i.succ) (𝓝 B))
    (hbound : ∀ x : (H.event i).incoming.terminalRegularOpen,
      ∀ᶠ t in 𝓝[<] H.time i.succ,
        b t ≤ metricScalarAt ((H.event i).incoming.flow.base.metric t) x.1) :
    ∀ x : (H.stage i.succ).Carrier, B ≤ metricScalarAt (H.initialMetric i.succ) x := by
  have hterminal : ∀ x : (H.event i).incoming.terminalRegularOpen,
      B ≤ metricScalarAt (H.event i).terminal.metric x :=
    fun x => (H.event i).terminal.scalar_lower_bound_of_tendsto x hb (hbound x)
  intro x
  simpa only [H.event_output i] using G.scalar_preserving B hB hterminal x

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

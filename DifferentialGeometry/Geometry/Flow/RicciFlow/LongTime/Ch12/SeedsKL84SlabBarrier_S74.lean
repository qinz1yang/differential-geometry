import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Sub86Barrier_O16
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature

/-!
# CH12-S74 G2 (b1'), analytic step along one event slab

* `flow_scalar_tendsto_of_regularCrossing_S74`: at a regular crossing `p ↦ q` the flow scalar at `p`
  tends (as `t ↑ s`) to the output scalar at `q` (terminal scalar = `t ↑ s` limit, and the
  terminal metric is the pull-back of the output metric under the crossing).
* `incoming_scalar_backward_barrier_S74`: shifted global backward barrier `(β - 2C(σ₀ + (s - t)))⁻¹`
  on the open slab `(a, s)` from a *limit* bound at the terminal time (the terminal value is only
  a `t ↑ s` limit).  Chaining it event by event (σ₀ := elapsed time from the top) is the
  single-barrier route of the S63 constants table.
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open scoped Topology

namespace GC.LongTime.Ch12

universe u

theorem flow_scalar_tendsto_of_regularCrossing_S74 {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) {p : P.Carrier} {q : Q.Carrier} (h : E.RegularCrossing p q) :
    Tendsto (fun t => E.incoming.flow.scalar t p) (𝓝[<] s)
      (𝓝 (metricScalarAt E.outputMetric q)) := by
  let x : E.incoming.terminalRegularOpen := ⟨p, MetricCutCapEvent.RegularCrossing.mem_terminalRegularRegion E h⟩
  have h1 := E.terminal.tendsto_metricScalarAt x
  have h2 : metricScalarAt E.terminal.metric x = metricScalarAt E.outputMetric q :=
    MetricCutCapEvent.RegularCrossing.scalar_eq E (p := x) h
  rw [h2] at h1
  exact h1

theorem incoming_scalar_backward_barrier_S74 {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) (y : P.Carrier) {θ : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hP2 : ∀ t ∈ Ioo a s, θ t < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2)
    {M β σ0 L c : ℝ} (hac : a ≤ c) (hβ : 0 < β) (hβM : β * M < 1) (hσ0 : 0 ≤ σ0)
    (hθ : ∀ t ∈ Ioo a s, θ t ≤ M) (hden : 0 < β - 2 * C * (σ0 + (s - c)))
    (hL : Tendsto (fun v => G.flow.scalar v y) (𝓝[<] s) (𝓝 L))
    (hLB : L ≤ (β - 2 * C * σ0)⁻¹) :
    ∀ t ∈ Ioo c s, G.flow.scalar t y ≤ (β - 2 * C * (σ0 + (s - t)))⁻¹ := by
  intro t ht
  set den0 : ℝ := β - 2 * C * (σ0 + (s - t)) with hden0
  have hden0pos : 0 < den0 := by
    have : 2 * C * (σ0 + (s - t)) ≤ 2 * C * (σ0 + (s - c)) :=
      mul_le_mul_of_nonneg_left (by linarith [ht.1]) (by positivity)
    linarith
  set ε0 : ℝ := den0 / (2 * C) with hε0
  have hε0pos : 0 < ε0 := by positivity
  let ψ : ℝ → ℝ := fun ε => (β - 2 * C * (σ0 + ε + (s - t)))⁻¹
  have hψ0 : ψ 0 = den0⁻¹ := by simp only [ψ, hden0, add_zero]
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), G.flow.scalar t y ≤ ψ ε := by
    filter_upwards [Ioo_mem_nhdsGT hε0pos] with ε hε
    have hdenε : 0 < β - 2 * C * (σ0 + ε + (s - t)) := by
      have : 2 * C * ε < den0 := by
        have := hε.2
        rw [hε0, lt_div_iff₀ (by positivity)] at this
        linarith
      simp only [hden0] at this
      linarith
    have hdenσ : 0 < β - 2 * C * (σ0 + ε) := by
      have : 2 * C * (σ0 + ε) ≤ 2 * C * (σ0 + ε + (s - t)) :=
        mul_le_mul_of_nonneg_left (by linarith [ht.2]) (by positivity)
      linarith
    have hlt : (β - 2 * C * σ0)⁻¹ < (β - 2 * C * (σ0 + ε))⁻¹ := by
      rw [inv_lt_inv₀ (by nlinarith [hε.1]) hdenσ]
      nlinarith [hε.1]
    have hLlt : L < (β - 2 * C * (σ0 + ε))⁻¹ := lt_of_le_of_lt hLB hlt
    obtain ⟨b, hb1, hb2⟩ := ((hL.eventually (gt_mem_nhds hLlt)).and
      (Ioo_mem_nhdsLT ht.2)).exists
    have hcb : Icc t b ⊆ Ioo a s := fun v hv =>
      ⟨lt_of_le_of_lt hac (lt_of_lt_of_le ht.1 hv.1), lt_of_le_of_lt hv.2 hb2.2⟩
    have hder : ∀ v ∈ Icc t b, HasDerivAt (fun w => G.flow.scalar w y)
        (scalarEvolutionRate (G.flow.base.metric v) y) v := fun v hv =>
      G.hasDerivAt_scalar_scalarEvolutionRate (hcb hv) y
    have hbar := backward_barrier_O16 (f := fun w => G.flow.scalar w y) (c := t) (b := b) (M := M)
      (C := C) (β := β) (σ0 := σ0 + ε) hC hβ hβM (by linarith [hε.1])
      (by
        have : 2 * C * (σ0 + ε + (b - t)) ≤ 2 * C * (σ0 + ε + (s - t)) :=
          mul_le_mul_of_nonneg_left (by linarith [hb2.2]) (by positivity)
        linarith)
      (fun v hv => (hder v hv).continuousAt.continuousWithinAt)
      (fun v hv => (hder v (Ioc_subset_Icc_self hv)).differentiableAt.differentiableWithinAt)
      (fun v hv hMv => hP2 v (hcb (Ioc_subset_Icc_self hv))
        (lt_of_le_of_lt (hθ v (hcb (Ioc_subset_Icc_self hv))) hMv))
      (by simpa only [mul_add, add_assoc] using hb1.le)
    have h1 := hbar t ⟨le_rfl, hb2.1.le⟩
    refine h1.trans ?_
    apply inv_anti₀ hdenε
    have : 2 * C * (σ0 + ε + (b - t)) ≤ 2 * C * (σ0 + ε + (s - t)) :=
      mul_le_mul_of_nonneg_left (by linarith [hb2.2]) (by positivity)
    linarith
  have hcont : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 (ψ 0)) := by
    have : ContinuousAt ψ 0 := by
      refine ContinuousAt.inv₀ (by fun_prop) ?_
      simp only [add_zero]
      exact hden0pos.ne'
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have := ge_of_tendsto hcont hev
  rwa [hψ0] at this

end GC.LongTime.Ch12

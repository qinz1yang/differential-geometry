import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82RegBoot_O78
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TracedBarrier_S88
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceConcat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceLocalChart

/-!
# CH12-O78, G1b: local trace start from the regional input

* `trace_start_R_O78` (local trace start / first exit, KL 82.1 regional input layer): under the
  regional event clause (Reg-ev ρ), the Ricci bound `Ric ≤ C/(v−a)` on the `R0`-balls around the
  centre trace and the S68 margins, every point `q` with `d_t(X t, q)` inside the margin has a
  backward trace from `a`.  Backward Fin-induction over the events: given the trace of `q` from the
  stage `i.succ`, the regional boot on the sub-window `[time(i.succ), t]` keeps its point at the
  event inside the outgoing `ρ`-ball, which (Reg-ev ρ) puts in the backward survivor domain; the
  survivor trace is concatenated.
* `regEv_of_oldOutput_O78`: the O70/O79 outgoing form `B_out(X(i.succ), ρ) ⊆ interior (range
  oldOutput)` implies (Reg-ev ρ) (`outgoing_survivor_chart_of_barrier_S88`, `event_output`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold TopologicalSpace DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Metric DifferentialGeometry.PDE.RicciFlow
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- **G1b.** Local trace start from the regional input (first-exit form). -/
theorem trace_start_R_O78 (H : ObservedHistory.{u}) {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {p q : (H.stageAt t).Carrier}
    (X : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    {C ρ R0 : ℝ} (hC : 0 < C) (hρ : 0 < ρ)
    (hq : riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q < ENNReal.ofReal ρ)
    (hroom : (riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q).toReal +
      16 * Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - a) < ρ / 2)
    (hR0 : (riemannianEDistOf (H.stageMetric (H.activeStage t) t) p q).toReal +
      16 * Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - a) +
        Real.sqrt (3 * ((t : ℝ) - a) / C) < R0)
    (hEvt : ∀ (i : Fin H.eventCount) (hai : H.activeStage a ≤ i.castSucc)
        (hit : i.succ ≤ H.activeStage t),
      riemannianBallOf (H.initialMetric i.succ)
          (X.point i.succ (hai.trans i.castSucc_lt_succ.le) hit) ρ ⊆
        H.backwardSurvivorDomain i.castSucc i.succ i.castSucc_lt_succ.le)
    (hRic : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t), (a : ℝ) < v →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) z <
          ENNReal.ofReal R0 →
      ∀ w : TangentSpace ThreeModel z,
        ricciTensor (H.stageMetric (H.activeStage v) v) z w w ≤
          C / ((v : ℝ) - a) * (H.stageMetric (H.activeStage v) v).inner z w w) :
    Nonempty (BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) q) := by
  have hlast : ∀ (j : Fin (H.eventCount + 1)) (hj : j = H.activeStage t)
      (hjt : j ≤ H.activeStage t), Nonempty (BackwardPointTrace H j (H.activeStage t) hjt q) := by
    intro j hj hjt
    subst hj
    exact ⟨BackwardPointTrace.singleton H _ q⟩
  -- the boot on a sub-window `[e, t]` keeps the trace inside the `ρ`-ball at `e`
  have hsub : ∀ (e : Icc (0 : ℝ) H.horizon) (hae : a ≤ e) (het : e ≤ t)
      (k : Fin (H.eventCount + 1)) (hk : H.activeStage e = k) (hkt : k ≤ H.activeStage t)
      (B : BackwardPointTrace H k (H.activeStage t) hkt q) (hak : H.activeStage a ≤ k),
      riemannianEDistOf (H.stageMetric k e) (X.point k hak hkt) (B.point k le_rfl hkt) <
        ENNReal.ofReal ρ := by
    intro e hae het k hk hkt B hak
    subst hk
    have hae' : (a : ℝ) ≤ e := hae
    have hsq : Real.sqrt ((t : ℝ) - e) ≤ Real.sqrt ((t : ℝ) - a) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsq3 : Real.sqrt (3 * ((t : ℝ) - e) / C) ≤ Real.sqrt (3 * ((t : ℝ) - a) / C) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hC.le)
    have hB0 : 0 ≤ Real.sqrt (C / 3) := Real.sqrt_nonneg _
    have hmul : 16 * Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - e) ≤
        16 * Real.sqrt (C / 3) * Real.sqrt ((t : ℝ) - a) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    let Xe := X.restrictFirst (H.activeStage_mono hae) (H.activeStage_mono het)
    have hb := dist_trace_boot_R_O78 H het Xe B (R0 := R0) hC hρ hq (by linarith) (by linarith)
      (fun i hai hit => hEvt i ((H.activeStage_mono hae).trans hai) hit)
      (fun v hev hvt hev' z hz w => by
        have hav : a ≤ v := hae.trans hev
        have hva : (a : ℝ) < v := lt_of_le_of_lt hae' hev'
        have h1 := hRic v hav hvt hva z hz w
        have hgw : 0 ≤ (H.stageMetric (H.activeStage v) v).inner z w w :=
          metric_inner_self_nonneg _ z w
        have hle : C / ((v : ℝ) - a) ≤ C / ((v : ℝ) - e) :=
          div_le_div_of_nonneg_left hC.le (by linarith) (by linarith)
        exact h1.trans (mul_le_mul_of_nonneg_right hle hgw))
      e le_rfl het
    refine lt_of_le_of_lt hb ((ENNReal.ofReal_lt_ofReal_iff hρ).mpr ?_)
    have h0 : Real.sqrt ((e : ℝ) - e) = 0 := by rw [sub_self, Real.sqrt_zero]
    rw [h0, sub_zero]
    linarith
  have key : ∀ j : Fin (H.eventCount + 1), ∀ (_haj : H.activeStage a ≤ j)
      (hjt : j ≤ H.activeStage t), Nonempty (BackwardPointTrace H j (H.activeStage t) hjt q) := by
    intro j
    induction j using Fin.reverseInduction with
    | last =>
      intro _ hjt
      exact hlast _ (le_antisymm hjt (Fin.le_last _)) hjt
    | cast i ih =>
      intro haj hjt
      by_cases hit : i.castSucc = H.activeStage t
      · exact hlast _ hit hjt
      have hist : i.succ ≤ H.activeStage t :=
        Fin.castSucc_lt_iff_succ_le.mp (lt_of_le_of_ne hjt hit)
      obtain ⟨A'⟩ := ih (haj.trans i.castSucc_lt_succ.le) hist
      let e : Icc (0 : ℝ) H.horizon :=
        ⟨H.time i.succ, H.time_nonneg _, H.time_le_horizon_at _⟩
      have hae : a ≤ e :=
        (time_lt_of_activeStage_lt_CX2 H a i.succ (haj.trans_lt i.castSucc_lt_succ)).le
      have het : e ≤ t := (H.time_strictMono.monotone hist).trans (H.activeStage_time_le t)
      have hej : H.activeStage e = i.succ := H.activeStage_at_time i.succ
      have hd := hsub e hae het i.succ hej hist A' (haj.trans i.castSucc_lt_succ.le)
      have hmetricE : H.stageMetric i.succ e = H.initialMetric i.succ :=
        H.stageMetric_initial i.succ
      rw [hmetricE] at hd
      obtain ⟨Z⟩ := hEvt i haj hist hd
      exact ⟨A'.concat Z⟩
  exact key (H.activeStage a) le_rfl (H.activeStage_mono hat)

/-- The O70/O79 outgoing retention form implies the regional event clause (Reg-ev ρ). -/
theorem regEv_of_oldOutput_O78 (H : ObservedHistory.{u}) {a t : Icc (0 : ℝ) H.horizon}
    (hat : a ≤ t) {p : (H.stageAt t).Carrier}
    (X : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    {ρ : ℝ}
    (hout : ∀ (i : Fin H.eventCount) (hf : H.activeStage a ≤ i.castSucc)
        (hl : i.succ ≤ H.activeStage t),
      riemannianBallOf (H.event i).outputMetric
          (X.point i.succ (hf.trans i.castSucc_lt_succ.le) hl) ρ ⊆
        interior (range (H.event i).oldOutput)) :
    ∀ (i : Fin H.eventCount) (hai : H.activeStage a ≤ i.castSucc)
        (hit : i.succ ≤ H.activeStage t),
      riemannianBallOf (H.initialMetric i.succ)
          (X.point i.succ (hai.trans i.castSucc_lt_succ.le) hit) ρ ⊆
        H.backwardSurvivorDomain i.castSucc i.succ i.castSucc_lt_succ.le := by
  intro i hai hit z hz
  rw [← H.event_output i] at hz
  let x : (H.event i).incoming.terminalRegularOpen :=
    ⟨X.point i.castSucc hai (i.castSucc_lt_succ.le.trans hit),
      (X.crossing i hai hit).mem_terminalRegularRegion (H.event i)⟩
  obtain ⟨E, -, -, hcr, -⟩ :=
    outgoing_survivor_chart_of_barrier_S88 (x := x) (hout i hai hit) (X.crossing i hai hit)
  exact ⟨BackwardPointTrace.prepend (BackwardPointTrace.singleton H i.succ z) (E.symm z).val
    (hcr z hz)⟩

end GC.LongTime.Ch12

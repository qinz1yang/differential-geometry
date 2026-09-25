import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalReciprocalBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceLocalChart

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u
variable {H : ObservedHistory.{u}}

theorem inv_max_scalar_sub_endpoint_le
    (last first : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (endpoint : (H.stage last).Carrier) (A : BackwardPointTrace H first last hle endpoint)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ i : Fin H.eventCount, ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ last,
      ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ),
      q < (H.event i).incoming.flow.scalar t
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event i).incoming.flow.scalar t
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2) :
    |(max q (metricScalarAt (H.initialMetric first) (A.point first le_rfl hle)))⁻¹ -
      (max q (metricScalarAt (H.initialMetric last) endpoint))⁻¹| ≤
        C * (H.time last - H.time first) := by
  induction first using Fin.reverseInduction with
  | last =>
    have he : last = Fin.last H.eventCount := le_antisymm (Fin.le_last _) hle
    subst last
    simp only [A.endpoint_eq, sub_self, abs_zero, mul_zero, le_refl]
  | cast i ih =>
    by_cases he : i.castSucc = last
    · subst last
      simp only [A.endpoint_eq, sub_self, abs_zero, mul_zero, le_refl]
    · have hl : i.succ ≤ last := by
        apply Fin.le_iff_val_le_val.mpr
        have hlt : i.castSucc < last := lt_of_le_of_ne hle he
        exact Nat.succ_le_iff.mpr hlt
      let B := A.restrictFirst i.castSucc_lt_succ.le hl
      have htail := ih hl B (fun j hj hlast =>
        hbound j (i.castSucc_lt_succ.le.trans hj) hlast)
      have hcross := A.crossing i le_rfl hl
      let p : (H.event i).incoming.terminalRegularOpen :=
        ⟨A.point i.castSucc le_rfl hle, hcross.mem_terminalRegularRegion (H.event i)⟩
      have hstep := (H.event i).terminal.inv_max_scalar_initial_sub_terminal_le
        (H.event i).incoming hq p (hbound i le_rfl hl)
      have hscalar := MetricCutCapEvent.RegularCrossing.scalar_eq (H.event i)
        (p := p) hcross
      change |(max q (metricScalarAt ((H.event i).incoming.flow.base.metric
        (H.time i.castSucc)) p.val))⁻¹ -
        (max q (metricScalarAt (H.event i).terminal.metric p))⁻¹| ≤ _ at hstep
      rw [H.event_initial i] at hstep
      change metricScalarAt (H.event i).terminal.metric p =
        metricScalarAt (H.event i).outputMetric (A.point i.succ i.castSucc_lt_succ.le hl) at hscalar
      rw [H.event_output i] at hscalar
      rw [hscalar] at hstep
      have htri := abs_sub_le
        ((max q (metricScalarAt (H.initialMetric i.castSucc) (A.point i.castSucc le_rfl hle)))⁻¹)
        ((max q (metricScalarAt (H.initialMetric i.succ)
          (A.point i.succ i.castSucc_lt_succ.le hl)))⁻¹)
        ((max q (metricScalarAt (H.initialMetric last) endpoint))⁻¹)
      dsimp only [B, restrictFirst] at htail
      nlinarith

theorem scalar_le_two_mul_of_time_sub_le
    (last first : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (endpoint : (H.stage last).Carrier) (A : BackwardPointTrace H first last hle endpoint)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hbound : ∀ i : Fin H.eventCount, ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ last,
      ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ),
      q < (H.event i).incoming.flow.scalar t
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event i).incoming.flow.scalar t
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hscalar : metricScalarAt (H.initialMetric last) endpoint ≤ Q)
    (htime : 2 * C * (H.time last - H.time first) * Q ≤ 1) :
    metricScalarAt (H.initialMetric first) (A.point first le_rfl hle) ≤ 2 * Q := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hrec := inv_max_scalar_sub_endpoint_le last first hle endpoint A hq hbound
  have hinv : Q⁻¹ ≤ (max q (metricScalarAt (H.initialMetric last) endpoint))⁻¹ :=
    inv_anti₀ (hq.trans_le (le_max_left _ _)) (max_le hqQ hscalar)
  have hhalf : C * (H.time last - H.time first) ≤ (2 * Q)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Q)).mpr
    nlinarith
  have htwo : Q⁻¹ = 2 * (2 * Q)⁻¹ := by field_simp
  have hlower : (2 * Q)⁻¹ ≤
      (max q (metricScalarAt (H.initialMetric first) (A.point first le_rfl hle)))⁻¹ := by
    rw [htwo] at hinv
    linarith [(abs_le.mp hrec).1]
  have hup := (inv_le_inv₀ (by positivity : 0 < 2 * Q)
    (hq.trans_le (le_max_left q
      (metricScalarAt (H.initialMetric first) (A.point first le_rfl hle))))).mp hlower
  exact (le_max_right _ _).trans hup

section

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {s : ℝ}

theorem inv_max_scalar_initial_sub_incoming_terminal_le
    (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen) (A : BackwardPointTrace H first last hle x.val)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hderiv : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t
          (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤
        C * G.flow.scalar t x.val ^ 2) :
    |(max q (metricScalarAt (H.initialMetric first) (A.point first le_rfl hle)))⁻¹ -
      (max q (metricScalarAt L.metric x))⁻¹| ≤ C * (s - H.time first) := by
  have hpast := A.inv_max_scalar_sub_endpoint_le last first hle x.val hq hderiv
  have htail := L.inv_max_scalar_initial_sub_terminal_le G hq x hfinal
  change |(max q (metricScalarAt (G.flow.base.metric (H.time last)) x.val))⁻¹ - _| ≤ _ at htail
  rw [hinit] at htail
  have htri := abs_sub_le
    ((max q (metricScalarAt (H.initialMetric first) (A.point first le_rfl hle)))⁻¹)
    ((max q (metricScalarAt (H.initialMetric last) x.val))⁻¹)
    ((max q (metricScalarAt L.metric x))⁻¹)
  nlinarith


end

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

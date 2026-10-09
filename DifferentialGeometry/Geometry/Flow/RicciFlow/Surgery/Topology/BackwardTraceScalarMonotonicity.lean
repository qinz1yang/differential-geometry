import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBackwardScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceLocalChart

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u
variable {H : ObservedHistory.{u}}

theorem max_scalar_le_endpoint_of_deriv_nonneg
    (last first : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (endpoint : (H.stage last).Carrier) (A : BackwardPointTrace H first last hle endpoint)
    {q : ℝ}
    (hbound : ∀ i : Fin H.eventCount, ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ last,
      ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ),
      q < (H.event i).incoming.flow.scalar t
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      0 ≤ derivWithin (fun v => (H.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic t) t) :
    max q (metricScalarAt (H.initialMetric first) (A.point first le_rfl hle)) ≤
      max q (metricScalarAt (H.initialMetric last) endpoint) := by
  induction first using Fin.reverseInduction with
  | last =>
    have he : last = Fin.last H.eventCount := le_antisymm (Fin.le_last _) hle
    subst last
    simp only [A.endpoint_eq, le_refl]
  | cast i ih =>
    by_cases he : i.castSucc = last
    · subst last
      simp only [A.endpoint_eq, le_refl]
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
      have hstep := (H.event i).terminal.max_scalar_le_terminal_of_deriv_nonneg
        p (hbound i le_rfl hl) ⟨le_rfl,(H.event i).incoming.lt⟩
      have hscalar := MetricCutCapEvent.RegularCrossing.scalar_eq (H.event i)
        (p := p) hcross
      change max q (metricScalarAt ((H.event i).incoming.flow.base.metric
        (H.time i.castSucc)) p.val) ≤ max q (metricScalarAt (H.event i).terminal.metric p) at hstep
      rw [H.event_initial i] at hstep
      change metricScalarAt (H.event i).terminal.metric p =
        metricScalarAt (H.event i).outputMetric (A.point i.succ i.castSucc_lt_succ.le hl) at hscalar
      rw [H.event_output i] at hscalar
      rw [hscalar] at hstep
      dsimp only [B, restrictFirst] at htail
      exact hstep.trans htail

theorem max_scalar_le_endpoint_at_time_of_deriv_nonneg
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {endpoint : (H.stage last).Carrier} (A : BackwardPointTrace H first last hle endpoint)
    {q : ℝ}
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)) →
      0 ≤ derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) (Iic t) t)
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last)
    {t : ℝ} (ht : t ∈ Ico (H.time j.castSucc) (H.time j.succ)) :
    max q ((H.event j).incoming.flow.scalar t
      (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl))) ≤
      max q (metricScalarAt (H.initialMetric last) endpoint) := by
  let B := A.restrictFirst (hf.trans j.castSucc_lt_succ.le) hl
  have htail := B.max_scalar_le_endpoint_of_deriv_nonneg last j.succ hl endpoint
    (fun i hi hi' => hbound i ((hf.trans j.castSucc_lt_succ.le).trans hi) hi')
  have hcross := A.crossing j hf hl
  let p : (H.event j).incoming.terminalRegularOpen :=
    ⟨A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl),
      hcross.mem_terminalRegularRegion (H.event j)⟩
  have hstep := (H.event j).terminal.max_scalar_le_terminal_of_deriv_nonneg p
    (hbound j hf hl) ht
  have heq := MetricCutCapEvent.RegularCrossing.scalar_eq (H.event j) (p := p) hcross
  rw [H.event_output j] at heq
  rw [heq] at hstep
  dsimp only [B, restrictFirst] at htail
  exact hstep.trans htail

theorem max_scalar_le_at_times_of_deriv_nonneg
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {endpoint : (H.stage last).Carrier} (A : BackwardPointTrace H first last hle endpoint)
    {q : ℝ}
    (j k : Fin H.eventCount) (hj : first ≤ j.castSucc) (hjk : j ≤ k)
    (hk : k.castSucc ≤ last)
    (hbound : ∀ l : Fin H.eventCount, ∀ hf : j.castSucc ≤ l.castSucc,
      ∀ hl : l.castSucc ≤ k.castSucc, ∀ t ∈ Ioo (H.time l.castSucc) (H.time l.succ),
      q < (H.event l).incoming.flow.scalar t (A.point l.castSucc (hj.trans hf) (hl.trans hk)) →
      0 ≤ derivWithin (fun v => (H.event l).incoming.flow.scalar v
        (A.point l.castSucc (hj.trans hf) (hl.trans hk))) (Iic t) t)
    {t b : ℝ} (ht : t ∈ Ico (H.time j.castSucc) (H.time j.succ))
    (hb : b ∈ Ico (H.time k.castSucc) (H.time k.succ)) (htb : t ≤ b) :
    max q ((H.event j).incoming.flow.scalar t
        (A.point j.castSucc hj (Fin.castSucc_le_castSucc_iff.mpr hjk |>.trans hk))) ≤
      max q ((H.event k).incoming.flow.scalar b
        (A.point k.castSucc (hj.trans (Fin.castSucc_le_castSucc_iff.mpr hjk)) hk)) := by
  have hjk' : j.castSucc ≤ k.castSucc := Fin.castSucc_le_castSucc_iff.mpr hjk
  have hfk : first ≤ k.castSucc := hj.trans hjk'
  have hmono := (H.event k).incoming.monotoneOn_max_scalar_of_deriv_nonneg
    (A.point k.castSucc hfk hk) (hbound k hjk' le_rfl)
  by_cases he : j = k
  · subst j
    exact hmono ht hb htb
  have hjnext : j.succ ≤ k.castSucc := by
    change j.val + 1 ≤ k.val
    have hne : j.val ≠ k.val := fun h => he (Fin.ext h)
    have hjval : j.val ≤ k.val := hjk
    omega
  let B := (A.restrictLast hfk hk).restrictFirst hj hjk'
  have hstep := B.max_scalar_le_endpoint_at_time_of_deriv_nonneg
    (fun l hf hl => hbound l hf (l.castSucc_lt_succ.le.trans hl))
    j le_rfl hjnext ht
  have htail := hmono (show H.time k.castSucc ∈ Ico (H.time k.castSucc) (H.time k.succ) from
    ⟨le_rfl,(H.event k).incoming.lt⟩) hb hb.1
  change max q (metricScalarAt ((H.event k).incoming.flow.base.metric
    (H.time k.castSucc)) (A.point k.castSucc hfk hk)) ≤ _ at htail
  rw [H.event_initial k] at htail
  dsimp only [B, restrictLast, restrictFirst] at hstep
  exact hstep.trans htail

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

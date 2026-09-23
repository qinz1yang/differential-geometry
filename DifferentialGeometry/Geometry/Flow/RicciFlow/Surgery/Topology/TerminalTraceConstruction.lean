import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceScalarTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricCutCapScalarLower

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem scalar_le_of_inv_max_bound
    {q Qend Qcap R Rlast L : ℝ} (hq : 0 < q) (hqend : q ≤ Qend) (hendcap : Qend ≤ Qcap)
    (hlast : Rlast ≤ Qend) (hrec : |(max q R)⁻¹ - (max q Rlast)⁻¹| ≤ L)
    (hbudget : L ≤ Qend⁻¹ - Qcap⁻¹) : R ≤ Qcap := by
  have hend : 0 < Qend := hq.trans_le hqend
  have hcap : 0 < Qcap := hend.trans_le hendcap
  have hinv : Qend⁻¹ ≤ (max q Rlast)⁻¹ :=
    inv_anti₀ (hq.trans_le (le_max_left _ _)) (max_le hqend hlast)
  have hlo : Qcap⁻¹ ≤ (max q R)⁻¹ := by linarith [(abs_le.mp hrec).1]
  exact (le_max_right _ _).trans
    ((inv_le_inv₀ hcap (hq.trans_le (le_max_left _ _))).mp hlo)

private theorem scalar_lt_of_inv_max_bound
    {q Qend Qcap R Rlast L : ℝ} (hq : 0 < q) (hqend : q ≤ Qend) (hendcap : Qend ≤ Qcap)
    (hlast : Rlast ≤ Qend) (hrec : |(max q R)⁻¹ - (max q Rlast)⁻¹| ≤ L)
    (hbudget : L < Qend⁻¹ - Qcap⁻¹) : R < Qcap := by
  have hend : 0 < Qend := hq.trans_le hqend
  have hcap : 0 < Qcap := hend.trans_le hendcap
  have hinv : Qend⁻¹ ≤ (max q Rlast)⁻¹ :=
    inv_anti₀ (hq.trans_le (le_max_left _ _)) (max_le hqend hlast)
  have hlo : Qcap⁻¹ < (max q R)⁻¹ := by linarith [(abs_le.mp hrec).1]
  exact (le_max_right _ _).trans_lt
    ((inv_lt_inv₀ hcap (hq.trans_le (le_max_left _ _))).mp hlo)

private theorem inv_max_initial_sub_terminal_le
    {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}
    (x : (H.event i).incoming.terminalRegularOpen)
    (A : BackwardPointTrace H first i.castSucc hle x.val)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hderiv : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2) :
    |(max q (metricScalarAt (H.initialMetric first) (A.point first le_rfl hle)))⁻¹ -
      (max q (metricScalarAt (H.event i).terminal.metric x))⁻¹| ≤
        C * (H.time i.succ - H.time first) := by
  have htail := A.inv_max_scalar_sub_endpoint_le i.castSucc first hle x.val hq
    (fun j hf hl => hderiv j hf (j.castSucc_lt_succ.le.trans hl)
      (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)))
  have hlast := (H.event i).terminal.inv_max_scalar_initial_sub_terminal_le
    (H.event i).incoming hq x (hderiv i hle le_rfl x.val)
  change |(max q (metricScalarAt ((H.event i).incoming.flow.base.metric
      (H.time i.castSucc)) x.val))⁻¹ - _| ≤ _ at hlast
  rw [H.event_initial i] at hlast
  have htri := abs_sub_le
    ((max q (metricScalarAt (H.initialMetric first) (A.point first le_rfl hle)))⁻¹)
    ((max q (metricScalarAt (H.initialMetric i.castSucc) x.val))⁻¹)
    ((max q (metricScalarAt (H.event i).terminal.metric x))⁻¹)
  nlinarith

theorem ObservedHistory.exists_backwardPointTrace_to_terminal_of_cap_scalar_lower_bound
    (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (first : Fin (H.eventCount + 1)) (hle : first ≤ i.castSucc)
    (x : (H.event i).incoming.terminalRegularOpen) {q Qend Qcap : ℝ} {C : ℝ≥0}
    (hq : 0 < q) (hqend : q ≤ Qend) (hendcap : Qend < Qcap)
    (hscalar : metricScalarAt (H.event i).terminal.metric x ≤ Qend)
    (htime : C * (H.time i.succ - H.time first) ≤ Qend⁻¹ - Qcap⁻¹)
    (hderiv : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hOld : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      (H.event j).old = (H.event j).transition.trace.retainedCore)
    (hcap : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall)
        (y : (H.stage j.succ).Carrier),
        (H.event j).transition.trace.presentation
          ((H.event j).transition.trace.capping.cap b.val z) = Sum.inl y →
          Qcap ≤ metricScalarAt (H.event j).outputMetric y) :
    ∃ A : BackwardPointTrace H first i.castSucc hle x.val,
      ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.castSucc ≤ i.castSucc),
        ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ),
          (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ≤ Qcap := by
  have hend : 0 < Qend := hq.trans_le hqend
  have hcapPos : 0 < Qcap := hend.trans hendcap
  have hgap : 0 < Qend⁻¹ - Qcap⁻¹ := sub_pos.mpr ((inv_lt_inv₀ hcapPos hend).mpr hendcap)
  have hex : Nonempty (BackwardPointTrace H first i.castSucc hle x.val) := by
    induction first using Fin.reverseInduction with
    | last =>
      have hbad : H.eventCount ≤ i.val := hle
      exact False.elim (by omega)
    | cast j ih =>
      by_cases he : j = i
      · subst j
        exact ⟨BackwardPointTrace.singleton H i.castSucc x.val⟩
      · have hl : j.succ ≤ i.castSucc := by
          have hji : j.val ≤ i.val := hle
          have hne : j.val ≠ i.val := fun h => he (Fin.ext h)
          change j.val + 1 ≤ i.val
          omega
        have htime' : C * (H.time i.succ - H.time j.succ) ≤ Qend⁻¹ - Qcap⁻¹ :=
          (mul_le_mul_of_nonneg_left
            (sub_le_sub_left (H.time_strictMono.monotone j.castSucc_lt_succ.le) _)
            C.coe_nonneg).trans htime
        obtain ⟨A⟩ := ih hl htime'
          (fun k hf hkl => hderiv k (j.castSucc_lt_succ.le.trans hf) hkl)
          (fun k hf hkl => hOld k (j.castSucc_lt_succ.le.trans hf) hkl)
          (fun k hf hkl => hcap k (j.castSucc_lt_succ.le.trans hf) hkl)
        have hrec := inv_max_initial_sub_terminal_le x A hq
          (fun k hf hkl => hderiv k (j.castSucc_lt_succ.le.trans hf) hkl)
        have hstrict : C * (H.time i.succ - H.time j.succ) < Qend⁻¹ - Qcap⁻¹ := by
          by_cases hc : (C : ℝ) = 0
          · simpa only [hc, zero_mul] using hgap
          · have hcpos : 0 < (C : ℝ) := lt_of_le_of_ne C.coe_nonneg (Ne.symm hc)
            exact (mul_lt_mul_of_pos_left
              (sub_lt_sub_left (H.time_strictMono j.castSucc_lt_succ) _) hcpos).trans_le htime
        have hlow := scalar_lt_of_inv_max_bound hq hqend hendcap.le hscalar hrec hstrict
        rw [← H.event_output j] at hlow
        obtain ⟨p, hp⟩ := (H.event j).exists_regularCrossing_of_scalar_lt
          (hOld j le_rfl hl) Qcap (hcap j le_rfl hl) (A.point j.succ le_rfl hl) hlow
        exact ⟨A.prepend p.val hp⟩
  obtain ⟨A⟩ := hex
  refine ⟨A, ?_⟩
  intro j hf hl t ht
  have hrec := A.inv_max_scalar_sub_terminal_le_at_time x hq
    (fun k hk hkl => hderiv k hk hkl (A.point k.castSucc hk hkl)) j hf hl ht
  have hbudget : C * (H.time i.succ - t) ≤ Qend⁻¹ - Qcap⁻¹ := by
    apply le_trans _ htime
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_left ((H.time_strictMono.monotone hf).trans ht.1) _) C.coe_nonneg
  exact scalar_le_of_inv_max_bound hq hqend hendcap.le hscalar hrec hbudget

theorem ObservedHistory.exists_backwardPointTrace_to_terminal_of_scalar_le_three_halves
    (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (first : Fin (H.eventCount + 1)) (hle : first ≤ i.castSucc)
    (x : (H.event i).incoming.terminalRegularOpen) {q Q : ℝ} {C : ℝ≥0}
    (hq : 0 < q) (hqQ : q ≤ Q)
    (hscalar : metricScalarAt (H.event i).terminal.metric x ≤ (3 / 2 : ℝ) * Q)
    (htime : 6 * C * (H.time i.succ - H.time first) * Q ≤ 1)
    (hderiv : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hOld : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      (H.event j).old = (H.event j).transition.trace.retainedCore)
    (hcap : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall)
        (y : (H.stage j.succ).Carrier),
        (H.event j).transition.trace.presentation
          ((H.event j).transition.trace.capping.cap b.val z) = Sum.inl y →
          2 * Q ≤ metricScalarAt (H.event j).outputMetric y) :
    ∃ A : BackwardPointTrace H first i.castSucc hle x.val,
      ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.castSucc ≤ i.castSucc),
        ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ),
          (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ≤ 2 * Q := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hbudget : C * (H.time i.succ - H.time first) ≤
      ((3 / 2 : ℝ) * Q)⁻¹ - (2 * Q)⁻¹ := by
    have he : ((3 / 2 : ℝ) * Q)⁻¹ - (2 * Q)⁻¹ = (6 * Q)⁻¹ := by field_simp; ring
    rw [he, inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 6 * Q)).mpr
    nlinarith
  exact H.exists_backwardPointTrace_to_terminal_of_cap_scalar_lower_bound i first hle x
    hq (by linarith) (by linarith) hscalar hbudget hderiv hOld hcap

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

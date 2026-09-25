import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceScalarTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceScalarMonotonicity
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
  exact A.inv_max_scalar_initial_sub_incoming_terminal_le
    (H.event i).incoming (H.event i).terminal (H.event_initial i) x hq
    (fun j hf hl => hderiv j hf (j.castSucc_lt_succ.le.trans hl)
      (A.point j.castSucc hf (j.castSucc_lt_succ.le.trans hl)))
    (hderiv i hle le_rfl x.val)

private theorem exists_backwardPointTrace_of_crossing_time_lower_bound
    (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (first : Fin (H.eventCount + 1)) (hle : first ≤ i.castSucc)
    (x : (H.event i).incoming.terminalRegularOpen) {q Qend Qcap : ℝ} {C : ℝ≥0}
    (hq : 0 < q) (hqend : q ≤ Qend) (hendcap : Qend < Qcap)
    (hscalar : metricScalarAt (H.event i).terminal.metric x ≤ Qend)
    {c : ℝ} (htime : C * (H.time i.succ - c) ≤ Qend⁻¹ - Qcap⁻¹)
    (hcrossTime : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      c < H.time j.succ)
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
        ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ), c ≤ t →
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
        obtain ⟨A⟩ := ih hl
          (fun k hf hkl => hcrossTime k (j.castSucc_lt_succ.le.trans hf) hkl)
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
              (sub_lt_sub_left (hcrossTime j le_rfl hl) _) hcpos).trans_le htime
        have hlow := scalar_lt_of_inv_max_bound hq hqend hendcap.le hscalar hrec hstrict
        rw [← H.event_output j] at hlow
        obtain ⟨p, hp⟩ := (H.event j).exists_regularCrossing_of_scalar_lt
          (hOld j le_rfl hl) Qcap (hcap j le_rfl hl) (A.point j.succ le_rfl hl) hlow
        exact ⟨A.prepend p.val hp⟩
  obtain ⟨A⟩ := hex
  refine ⟨A, ?_⟩
  intro j hf hl t ht hct
  have hrec := A.inv_max_scalar_sub_terminal_le_at_time x hq
    (fun k hk hkl => hderiv k hk hkl (A.point k.castSucc hk hkl)) j hf hl ht
  have hbudget : C * (H.time i.succ - t) ≤ Qend⁻¹ - Qcap⁻¹ := by
    apply le_trans _ htime
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_left hct _) C.coe_nonneg
  exact scalar_le_of_inv_max_bound hq hqend hendcap.le hscalar hrec hbudget

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
  obtain ⟨A, hA⟩ := exists_backwardPointTrace_of_crossing_time_lower_bound H i first hle x
    hq hqend hendcap hscalar htime
    (fun j hf hl => (H.time_strictMono.monotone hf).trans_lt
      (H.time_strictMono j.castSucc_lt_succ)) hderiv hOld hcap
  exact ⟨A, fun j hf hl t ht => hA j hf hl t ht
    ((H.time_strictMono.monotone hf).trans ht.1)⟩

theorem ObservedHistory.exists_backwardPointTrace_to_terminal_on_time_window
    (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (first : Fin H.eventCount) (hle : first.castSucc ≤ i.castSucc)
    (x : (H.event i).incoming.terminalRegularOpen) {q Qend Qcap : ℝ} {C : ℝ≥0}
    (hq : 0 < q) (hqend : q ≤ Qend) (hendcap : Qend < Qcap)
    (hscalar : metricScalarAt (H.event i).terminal.metric x ≤ Qend)
    {c : ℝ} (hc : c ∈ Ico (H.time first.castSucc) (H.time first.succ))
    (htime : C * (H.time i.succ - c) ≤ Qend⁻¹ - Qcap⁻¹)
    (hderiv : ∀ j : Fin H.eventCount, first.castSucc ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hOld : ∀ j : Fin H.eventCount, first.castSucc ≤ j.castSucc → j.succ ≤ i.castSucc →
      (H.event j).old = (H.event j).transition.trace.retainedCore)
    (hcap : ∀ j : Fin H.eventCount, first.castSucc ≤ j.castSucc → j.succ ≤ i.castSucc →
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall)
        (y : (H.stage j.succ).Carrier),
        (H.event j).transition.trace.presentation
          ((H.event j).transition.trace.capping.cap b.val z) = Sum.inl y →
          Qcap ≤ metricScalarAt (H.event j).outputMetric y) :
    ∃ A : BackwardPointTrace H first.castSucc i.castSucc hle x.val,
      ∀ (j : Fin H.eventCount) (hf : first.castSucc ≤ j.castSucc) (hl : j.castSucc ≤ i.castSucc),
        ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ), c ≤ t →
          (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ≤ Qcap := by
  apply exists_backwardPointTrace_of_crossing_time_lower_bound H i first.castSucc hle x
    hq hqend hendcap hscalar htime _ hderiv hOld hcap
  intro j hf hl
  apply hc.2.trans_le (H.time_strictMono.monotone _)
  change first.val + 1 ≤ j.val + 1
  exact Nat.succ_le_succ hf

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

theorem ObservedHistory.exists_backwardPointTrace_on_window_of_scalar_le_three_halves
    (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (first : Fin H.eventCount) (hle : first.castSucc ≤ i.castSucc)
    (x : (H.event i).incoming.terminalRegularOpen) {q Q : ℝ} {C : ℝ≥0}
    (hq : 0 < q) (hqQ : q ≤ Q)
    (hscalar : metricScalarAt (H.event i).terminal.metric x ≤ (3 / 2 : ℝ) * Q)
    {c : ℝ} (hc : c ∈ Ico (H.time first.castSucc) (H.time first.succ))
    (htime : 6 * C * (H.time i.succ - c) * Q ≤ 1)
    (hderiv : ∀ j : Fin H.eventCount, first.castSucc ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hOld : ∀ j : Fin H.eventCount, first.castSucc ≤ j.castSucc → j.succ ≤ i.castSucc →
      (H.event j).old = (H.event j).transition.trace.retainedCore)
    (hcap : ∀ j : Fin H.eventCount, first.castSucc ≤ j.castSucc → j.succ ≤ i.castSucc →
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall)
        (y : (H.stage j.succ).Carrier),
        (H.event j).transition.trace.presentation
          ((H.event j).transition.trace.capping.cap b.val z) = Sum.inl y →
          2 * Q ≤ metricScalarAt (H.event j).outputMetric y) :
    ∃ A : BackwardPointTrace H first.castSucc i.castSucc hle x.val,
      ∀ (j : Fin H.eventCount) (hf : first.castSucc ≤ j.castSucc) (hl : j.castSucc ≤ i.castSucc),
        ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ), c ≤ t →
          (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ≤ 2 * Q := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hbudget : C * (H.time i.succ - c) ≤
      ((3 / 2 : ℝ) * Q)⁻¹ - (2 * Q)⁻¹ := by
    have he : ((3 / 2 : ℝ) * Q)⁻¹ - (2 * Q)⁻¹ = (6 * Q)⁻¹ := by field_simp; ring
    rw [he, inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 6 * Q)).mpr
    nlinarith
  exact H.exists_backwardPointTrace_to_terminal_on_time_window i first hle x
    hq (by linarith) (by linarith) hscalar hc hbudget hderiv hOld hcap

namespace ObservedHistory

theorem exists_backwardPointTrace_or_cap (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (endpoint : (H.stage last).Carrier)
    (hOld : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      (H.event j).old = (H.event j).transition.trace.retainedCore) :
    Nonempty (BackwardPointTrace H first last hle endpoint) ∨
      ∃ (j : Fin H.eventCount) (_ : first ≤ j.castSucc) (hl : j.succ ≤ last)
        (A : BackwardPointTrace H j.succ last hl endpoint)
        (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
        (H.event j).transition.trace.presentation
          ((H.event j).transition.trace.capping.cap b.val z) =
            Sum.inl (A.point j.succ le_rfl hl) := by
  induction first using Fin.reverseInduction with
  | last =>
      have he : last = Fin.last H.eventCount := le_antisymm (Fin.le_last _) hle
      subst last
      exact Or.inl ⟨BackwardPointTrace.singleton H _ endpoint⟩
  | cast j ih =>
      by_cases he : j.castSucc = last
      · subst last
        exact Or.inl ⟨BackwardPointTrace.singleton H _ endpoint⟩
      · have hl : j.succ ≤ last := by
          have hlt : j.castSucc < last := lt_of_le_of_ne hle he
          exact Nat.succ_le_iff.mpr hlt
        rcases ih hl (fun k hf hk => hOld k (j.castSucc_lt_succ.le.trans hf) hk) with
          hA | ⟨k, hf, hk, A, b, z, hz⟩
        · obtain ⟨A⟩ := hA
          by_cases hcap : A.point j.succ le_rfl hl ∈ (H.event j).capRegion
          · obtain ⟨b, z, hb⟩ := hcap
            have hret : (H.event j).RetainedBoundary b := by
              rw [MetricCutCapEvent.retainedBoundary_iff_capRetained]
              rcases (H.event j).transition.trace.cap_retained_or_discarded b with h | h
              · exact h
              · obtain ⟨d, hd⟩ := h z
                exact (Sum.inr_ne_inl (hd.trans hb)).elim
            exact Or.inr ⟨j, le_rfl, hl, A, ⟨b, hret⟩, z, hb⟩
          · obtain ⟨p, hp⟩ := (H.event j).exists_regularCrossing_of_not_mem_capRegion
              (hOld j le_rfl hl) hcap
            exact Or.inl ⟨A.prepend p.val hp⟩
        · exact Or.inr ⟨k, j.castSucc_lt_succ.le.trans hf, hk, A, b, z, hz⟩

theorem exists_backwardPointTrace_or_recent_presented_cap_on_time_window
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen)
    {q Q θ : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hθsmall : θ ≤ 1 / 4) (hbudget : 6 * C * θ ≤ 1)
    (hcrossTime : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      s - θ / Q < H.time j.succ)
    (hscalar : metricScalarAt L.metric x ≤ (3 / 2 : ℝ) * Q)
    (hderiv : ∀ j : Fin H.eventCount, first < j.castSucc → j.succ ≤ last →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      s - θ / Q ≤ t → q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ t ∈ Ioo (H.time last) s, s - θ / Q ≤ t → q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤
        C * G.flow.scalar t x.val ^ 2)
    (hOld : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      (H.event j).old = (H.event j).transition.trace.retainedCore)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ b : (H.event j).RetainedBoundaryIndex, (H.event j).PresentedStaticCap fixed D m ε b)
    (hcap : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc,
      ∀ hl : j.succ ≤ last,
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
        (S j hf hl b).neck.scale / 2 ≤
          metricScalarAt (S j hf hl b).witness.metric ((S j hf hl b).witness.cap z)) :
    Nonempty (BackwardPointTrace H first last hle x.val) ∨
      ∃ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last)
        (A : BackwardPointTrace H j.succ last hl x.val)
        (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
        (H.event j).transition.trace.presentation
          ((H.event j).transition.trace.capping.cap b.val z) =
            Sum.inl (A.point j.succ le_rfl hl) ∧
        A.point j.succ le_rfl hl = (S j hf hl b).inclusion ((S j hf hl b).witness.cap z) ∧
        metricScalarAt (H.event j).outputMetric (A.point j.succ le_rfl hl) < 2 * Q ∧
        (S j hf hl b).neck.scale < 4 * Q ∧
        0 < (S j hf hl b).neck.scale * (s - H.time j.succ) ∧
        (S j hf hl b).neck.scale * (s - H.time j.succ) < 4 * θ ∧
        (S j hf hl b).neck.scale * (s - H.time j.succ) < 1 := by
  have hQ : 0 < Q := hq.trans_le hqQ
  rcases H.exists_backwardPointTrace_or_cap first last hle x.val hOld with
    h | ⟨j, hf, hl, A, b, z, hz⟩
  · exact Or.inl h
  have hbirth : s - θ / Q < H.time j.succ := hcrossTime j hf hl
  have hdt : 0 < s - H.time j.succ :=
    sub_pos.mpr ((H.time_strictMono.monotone hl).trans_lt G.lt)
  have hdtle : s - H.time j.succ < θ / Q := by linarith
  have hrec := A.inv_max_scalar_initial_sub_incoming_terminal_le G L hinit x hq
    (fun k hk hkl t ht => hderiv k
      ((hf.trans_lt j.castSucc_lt_succ).trans_le hk) hkl
      (A.point k.castSucc hk (k.castSucc_lt_succ.le.trans hkl)) t ht
      ((hbirth.le.trans (H.time_strictMono.monotone hk)).trans ht.1.le))
    (fun t ht => hfinal t ht ((hbirth.le.trans (H.time_strictMono.monotone hl)).trans ht.1.le))
  have hgap : ((3 / 2 : ℝ) * Q)⁻¹ - (2 * Q)⁻¹ = (6 * Q)⁻¹ := by
    field_simp
    ring
  have hsmall : C * (s - H.time j.succ) <
      ((3 / 2 : ℝ) * Q)⁻¹ - (2 * Q)⁻¹ := by
    rw [hgap, inv_eq_one_div]
    apply (lt_div_iff₀ (by positivity : 0 < 6 * Q)).mpr
    by_cases hC : (C : ℝ) = 0
    · simp only [hC, zero_mul]
      norm_num
    · have hCpos : 0 < (C : ℝ) := lt_of_le_of_ne C.coe_nonneg (Ne.symm hC)
      have hdtQ : (s - H.time j.succ) * Q < θ := (lt_div_iff₀ hQ).mp hdtle
      nlinarith
  have hlow : metricScalarAt (H.initialMetric j.succ) (A.point j.succ le_rfl hl) < 2 * Q := by
    have hlast : max q (metricScalarAt L.metric x) ≤ (3 / 2 : ℝ) * Q :=
      max_le (by linarith) hscalar
    have hpos : 0 < max q (metricScalarAt L.metric x) := hq.trans_le (le_max_left _ _)
    have hinv : ((3 / 2 : ℝ) * Q)⁻¹ ≤ (max q (metricScalarAt L.metric x))⁻¹ :=
      inv_anti₀ hpos hlast
    have hlo : (2 * Q)⁻¹ <
        (max q (metricScalarAt (H.initialMetric j.succ) (A.point j.succ le_rfl hl)))⁻¹ := by
      linarith [(abs_le.mp hrec).1]
    exact (le_max_right _ _).trans_lt
      ((inv_lt_inv₀ (by positivity : 0 < 2 * Q)
        (hq.trans_le (le_max_left _ _))).mp hlo)
  rw [← H.event_output j] at hlow
  have hpoint : A.point j.succ le_rfl hl =
      (S j hf hl b).inclusion ((S j hf hl b).witness.cap z) :=
    Sum.inl_injective (hz.symm.trans ((S j hf hl b).cap_eq z))
  have hcapBound := hcap j hf hl b z
  rw [(S j hf hl b).scalar_eq (H.event j), ← hpoint] at hcapBound
  have hscale : (S j hf hl b).neck.scale < 4 * Q := by linarith
  have hage : (S j hf hl b).neck.scale * (s - H.time j.succ) < 4 * θ := by
    have hdtQ : (s - H.time j.succ) * Q < θ := (lt_div_iff₀ hQ).mp hdtle
    nlinarith [mul_lt_mul_of_pos_right hscale hdt]
  exact Or.inr ⟨j, hf, hl, A, b, z, hz, hpoint, hlow, hscale,
    mul_pos (S j hf hl b).neck.scale_pos hdt, hage, hage.trans_le (by linarith)⟩

theorem exists_backwardPointTrace_or_recent_presented_cap_of_incoming_slab
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen)
    {q Q θ : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hθsmall : θ ≤ 1 / 4) (hbudget : 6 * C * θ ≤ 1)
    (hcrossTime : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      s - θ / Q < H.time j.succ)
    (hscalar : metricScalarAt L.metric x ≤ (3 / 2 : ℝ) * Q)
    (hderiv : ∀ j : Fin H.eventCount, first < j.castSucc → j.succ ≤ last →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (Iic t) t| ≤
        C * G.flow.scalar t x.val ^ 2)
    (hOld : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      (H.event j).old = (H.event j).transition.trace.retainedCore)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ b : (H.event j).RetainedBoundaryIndex, (H.event j).PresentedStaticCap fixed D m ε b)
    (hcap : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc,
      ∀ hl : j.succ ≤ last,
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
        (S j hf hl b).neck.scale / 2 ≤
          metricScalarAt (S j hf hl b).witness.metric ((S j hf hl b).witness.cap z)) :
    Nonempty (BackwardPointTrace H first last hle x.val) ∨
      ∃ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last)
        (A : BackwardPointTrace H j.succ last hl x.val)
        (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
        (H.event j).transition.trace.presentation
          ((H.event j).transition.trace.capping.cap b.val z) =
            Sum.inl (A.point j.succ le_rfl hl) ∧
        A.point j.succ le_rfl hl = (S j hf hl b).inclusion ((S j hf hl b).witness.cap z) ∧
        metricScalarAt (H.event j).outputMetric (A.point j.succ le_rfl hl) < 2 * Q ∧
        (S j hf hl b).neck.scale < 4 * Q ∧
        0 < (S j hf hl b).neck.scale * (s - H.time j.succ) ∧
        (S j hf hl b).neck.scale * (s - H.time j.succ) < 4 * θ ∧
        (S j hf hl b).neck.scale * (s - H.time j.succ) < 1 := by
  exact H.exists_backwardPointTrace_or_recent_presented_cap_on_time_window first last hle G L hinit x
    hq hqQ hθsmall hbudget hcrossTime hscalar
    (fun j hf hl y t ht _ => hderiv j hf hl y t ht)
    (fun t ht _ => hfinal t ht) hOld S hcap

theorem exists_backwardPointTrace_or_recent_presented_cap
    (H : ObservedHistory.{u}) (first i : Fin H.eventCount)
    (hle : first.castSucc ≤ i.castSucc)
    (x : (H.event i).incoming.terminalRegularOpen)
    {q Q θ : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hθsmall : θ < 1 / 4) (hbudget : 6 * C * θ ≤ 1)
    (hfirst : H.time i.succ - θ / Q ∈ Ico (H.time first.castSucc) (H.time first.succ))
    (hscalar : metricScalarAt (H.event i).terminal.metric x ≤ (3 / 2 : ℝ) * Q)
    (hderiv : ∀ j : Fin H.eventCount, first.succ ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hOld : ∀ j : Fin H.eventCount, first.castSucc ≤ j.castSucc → j.succ ≤ i.castSucc →
      (H.event j).old = (H.event j).transition.trace.retainedCore)
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ j : Fin H.eventCount, first.castSucc ≤ j.castSucc → j.succ ≤ i.castSucc →
      ∀ b : (H.event j).RetainedBoundaryIndex, (H.event j).PresentedStaticCap fixed D m ε b)
    (hcap : ∀ j : Fin H.eventCount, ∀ hf : first.castSucc ≤ j.castSucc,
      ∀ hl : j.succ ≤ i.castSucc,
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
        (S j hf hl b).neck.scale / 2 ≤
          metricScalarAt (S j hf hl b).witness.metric ((S j hf hl b).witness.cap z)) :
    Nonempty (BackwardPointTrace H first.castSucc i.castSucc hle x.val) ∨
      ∃ (j : Fin H.eventCount) (hf : first.castSucc ≤ j.castSucc)
        (hl : j.succ ≤ i.castSucc)
        (A : BackwardPointTrace H j.succ i.castSucc hl x.val)
        (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
        (H.event j).transition.trace.presentation
          ((H.event j).transition.trace.capping.cap b.val z) =
            Sum.inl (A.point j.succ le_rfl hl) ∧
        A.point j.succ le_rfl hl = (S j hf hl b).inclusion ((S j hf hl b).witness.cap z) ∧
        metricScalarAt (H.event j).outputMetric (A.point j.succ le_rfl hl) < 2 * Q ∧
        (S j hf hl b).neck.scale < 4 * Q ∧
        0 < (S j hf hl b).neck.scale * (H.time i.succ - H.time j.succ) ∧
        (S j hf hl b).neck.scale * (H.time i.succ - H.time j.succ) < 4 * θ ∧
        (S j hf hl b).neck.scale * (H.time i.succ - H.time j.succ) < 1 := by
  by_cases hfi : first = i
  · subst first
    exact Or.inl ⟨BackwardPointTrace.singleton H i.castSucc x.val⟩
  have hfirsti : first.succ ≤ i.castSucc := by
    change first.val + 1 ≤ i.val
    have hlt : first.val < i.val := lt_of_le_of_ne hle (fun h => hfi (Fin.ext h))
    omega
  exact H.exists_backwardPointTrace_or_recent_presented_cap_of_incoming_slab
    first.castSucc i.castSucc hle (H.event i).incoming (H.event i).terminal
    (H.event_initial i) x hq hqQ hθsmall.le hbudget
    (fun j hj _ => hfirst.2.trans_le (H.time_strictMono.monotone (Nat.succ_le_succ hj)))
    hscalar
    (fun j hj hl => hderiv j (Nat.succ_le_of_lt hj) (j.castSucc_lt_succ.le.trans hl))
    (hderiv i hfirsti le_rfl x.val) hOld S hcap

end ObservedHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem BackwardPointTrace.max_scalar_initial_le_terminal_of_deriv_nonneg
    {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}
    (x : (H.event i).incoming.terminalRegularOpen)
    (A : BackwardPointTrace H first i.castSucc hle x.val) {q : ℝ}
    (hderiv : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc,
      ∀ hl : j.castSucc ≤ i.castSucc,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) →
      0 ≤ derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf hl)) (Iic t) t) :
    max q (metricScalarAt (H.initialMetric first) (A.point first le_rfl hle)) ≤
      max q (metricScalarAt (H.event i).terminal.metric x) := by
  have hbefore := A.max_scalar_le_endpoint_of_deriv_nonneg i.castSucc first hle x.val
    (fun j hf hl => hderiv j hf (j.castSucc_lt_succ.le.trans hl))
  have hfinal := (H.event i).terminal.max_scalar_le_terminal_of_deriv_nonneg x
    (by simpa only [A.endpoint_eq] using hderiv i hle le_rfl)
    (show H.time i.castSucc ∈ Ico (H.time i.castSucc) (H.time i.succ) from
      ⟨le_rfl,(H.event i).incoming.lt⟩)
  change max q (metricScalarAt ((H.event i).incoming.flow.base.metric
    (H.time i.castSucc)) x.val) ≤ _ at hfinal
  rw [H.event_initial i] at hfinal
  exact hbefore.trans hfinal

private theorem ObservedHistory.exists_backwardPointTrace_of_scalar_deriv_nonneg_of_cap_scalar_gt
    (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (first : Fin (H.eventCount + 1)) (hle : first ≤ i.castSucc)
    (x : (H.event i).incoming.terminalRegularOpen) {q Q : ℝ}
    (hq : q ≤ Q) (hscalar : metricScalarAt (H.event i).terminal.metric x ≤ Q)
    (hderiv : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      0 ≤ derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t)
    (hOld : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      (H.event j).old = (H.event j).transition.trace.retainedCore)
    (hcap : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall)
        (y : (H.stage j.succ).Carrier),
        (H.event j).transition.trace.presentation
          ((H.event j).transition.trace.capping.cap b.val z) = Sum.inl y →
          Q < metricScalarAt (H.event j).outputMetric y) :
    Nonempty (BackwardPointTrace H first i.castSucc hle x.val) := by
  rcases H.exists_backwardPointTrace_or_cap first i.castSucc hle x.val hOld with
    h | ⟨j,hjf,hji,A,b,z,hborn⟩
  · exact h
  · have hbound := A.max_scalar_initial_le_terminal_of_deriv_nonneg x
      (fun l hf hl => hderiv l (hjf.trans (j.castSucc_lt_succ.le.trans hf)) hl
        (A.point l.castSucc hf hl))
    have hlow : metricScalarAt (H.event j).outputMetric (A.point j.succ le_rfl hji) ≤ Q := by
      rw [H.event_output j]
      exact (le_max_right _ _).trans (hbound.trans (max_le hq hscalar))
    exact False.elim ((hcap j hjf hji b z _ hborn).not_ge hlow)

theorem ObservedHistory.exists_backwardPointTrace_scalar_bound_of_scalar_deriv_nonneg_of_cap_scalar_gt
    (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (first : Fin (H.eventCount + 1)) (hle : first ≤ i.castSucc)
    (x : (H.event i).incoming.terminalRegularOpen) {q Q : ℝ}
    (hq : q ≤ Q) (hscalar : metricScalarAt (H.event i).terminal.metric x ≤ Q)
    (hderiv : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      0 ≤ derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t)
    (hOld : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      (H.event j).old = (H.event j).transition.trace.retainedCore)
    (hcap : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ i.castSucc →
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall)
        (y : (H.stage j.succ).Carrier),
        (H.event j).transition.trace.presentation
          ((H.event j).transition.trace.capping.cap b.val z) = Sum.inl y →
          Q < metricScalarAt (H.event j).outputMetric y) :
    ∃ A : BackwardPointTrace H first i.castSucc hle x.val,
      ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.castSucc ≤ i.castSucc),
        ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ),
          (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ≤ Q := by
  obtain ⟨A⟩ := H.exists_backwardPointTrace_of_scalar_deriv_nonneg_of_cap_scalar_gt
    i first hle x hq hscalar hderiv hOld hcap
  refine ⟨A, ?_⟩
  intro j hf hl t ht
  have htail := A.max_scalar_le_at_times_of_deriv_nonneg j i hf
    (Fin.castSucc_le_castSucc_iff.mp hl) le_rfl
    (fun l hjl hli => hderiv l (hf.trans hjl) hli (A.point l.castSucc (hf.trans hjl) hli))
    ht (show H.time i.castSucc ∈ Ico (H.time i.castSucc) (H.time i.succ) from
      ⟨le_rfl,(H.event i).incoming.lt⟩)
  by_cases he : j = i
  · subst j
    have hlast := (H.event i).terminal.max_scalar_le_terminal_of_deriv_nonneg x
      (hderiv i hf le_rfl x.val) ht
    simpa only [A.endpoint_eq] using
      (le_max_right _ _).trans (hlast.trans (max_le hq hscalar))
  · have hji : j.succ ≤ i.castSucc := by
      change j.val + 1 ≤ i.val
      have hv : j.val ≤ i.val := hl
      have hn : j.val ≠ i.val := fun hv => he (Fin.ext hv)
      omega
    have htend : t ≤ H.time i.castSucc :=
      ht.2.le.trans (H.time_strictMono.monotone hji)
    have hlast := (H.event i).terminal.max_scalar_le_terminal_of_deriv_nonneg x
      (hderiv i hle le_rfl x.val)
      (show H.time i.castSucc ∈ Ico (H.time i.castSucc) (H.time i.succ) from
        ⟨le_rfl,(H.event i).incoming.lt⟩)
    have hb := htail htend
    have hb' : max q ((H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl)) ≤
        max q ((H.event i).incoming.flow.scalar (H.time i.castSucc) x.val) := by
      simpa only [A.endpoint_eq] using hb
    have hlast' : max q ((H.event i).incoming.flow.scalar (H.time i.castSucc) x.val) ≤ Q :=
      hlast.trans (max_le hq hscalar)
    exact (le_max_right q _).trans (hb'.trans hlast')

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

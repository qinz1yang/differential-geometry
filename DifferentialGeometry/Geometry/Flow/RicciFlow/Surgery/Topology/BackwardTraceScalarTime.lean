import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceReciprocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCurvatureContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.QuadraticForm

noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u
variable {H : ObservedHistory.{u}}

theorem inv_max_scalar_sub_endpoint_le_at_time
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {endpoint : (H.stage last).Carrier} (A : BackwardPointTrace H first last hle endpoint)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ i : Fin H.eventCount, ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ last,
      ∀ t ∈ Ioo (H.time i.castSucc) (H.time i.succ),
      q < (H.event i).incoming.flow.scalar t
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun v => (H.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic t) t| ≤
        C * (H.event i).incoming.flow.scalar t
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {t : ℝ} (ht : t ∈ Ico (H.time i.castSucc) (H.time i.succ)) :
    |(max q ((H.event i).incoming.flow.scalar t
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))))⁻¹ -
      (max q (metricScalarAt (H.initialMetric last) endpoint))⁻¹| ≤ C * (H.time last - t) := by
  let B := A.restrictFirst (hf.trans i.castSucc_lt_succ.le) hl
  have htail := inv_max_scalar_sub_endpoint_le last i.succ hl endpoint B hq
    (fun j hj hlast => hbound j ((hf.trans i.castSucc_lt_succ.le).trans hj) hlast)
  have hcross := A.crossing i hf hl
  let p : (H.event i).incoming.terminalRegularOpen :=
    ⟨A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
      hcross.mem_terminalRegularRegion (H.event i)⟩
  have hstep := (H.event i).terminal.inv_max_scalar_sub_terminal_le (H.event i).incoming
    hq p (hbound i hf hl) ht
  have heq := MetricCutCapEvent.RegularCrossing.scalar_eq (H.event i) (p := p) hcross
  rw [H.event_output i] at heq
  rw [heq] at hstep
  have htri := abs_sub_le
    ((max q ((H.event i).incoming.flow.scalar t p.val))⁻¹)
    ((max q (metricScalarAt (H.initialMetric i.succ)
      (A.point i.succ (hf.trans i.castSucc_lt_succ.le) hl)))⁻¹)
    ((max q (metricScalarAt (H.initialMetric last) endpoint))⁻¹)
  dsimp only [B, restrictFirst] at htail
  nlinarith

theorem inv_max_scalar_sub_terminal_le_at_time
    {i : Fin H.eventCount} {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}
    (x : (H.event i).incoming.terminalRegularOpen)
    (A : BackwardPointTrace H first i.castSucc hle x.val)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.castSucc ≤ i.castSucc,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf hl)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ^ 2)
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.castSucc ≤ i.castSucc)
    {t : ℝ} (ht : t ∈ Ico (H.time j.castSucc) (H.time j.succ)) :
    |(max q ((H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl)))⁻¹ -
      (max q (metricScalarAt (H.event i).terminal.metric x))⁻¹| ≤
      C * (H.time i.succ - t) := by
  have hlast := hbound i hle le_rfl
  simp only [A.endpoint_eq] at hlast
  by_cases he : j = i
  · subst j
    simpa only [A.endpoint_eq] using
      (H.event i).terminal.inv_max_scalar_sub_terminal_le (H.event i).incoming hq x hlast ht
  have hjnext : j.succ ≤ i.castSucc := by
    apply Fin.le_iff_val_le_val.mpr
    have hji : j.val ≠ i.val := fun h => he (Fin.ext h)
    have hjival : j.val ≤ i.val := hl
    change j.val + 1 ≤ i.val
    omega
  have hstep := inv_max_scalar_sub_endpoint_le_at_time A hq
    (fun k hk hkl => hbound k hk (k.castSucc_lt_succ.le.trans hkl)) j hf hjnext ht
  have htail := (H.event i).terminal.inv_max_scalar_initial_sub_terminal_le
    (H.event i).incoming hq x hlast
  change |(max q (metricScalarAt ((H.event i).incoming.flow.base.metric
    (H.time i.castSucc)) x.val))⁻¹ -
    (max q (metricScalarAt (H.event i).terminal.metric x))⁻¹| ≤ _ at htail
  rw [H.event_initial i] at htail
  have htri := abs_sub_le
    ((max q ((H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl)))⁻¹)
    ((max q (metricScalarAt (H.initialMetric i.castSucc) x.val))⁻¹)
    ((max q (metricScalarAt (H.event i).terminal.metric x))⁻¹)
  nlinarith

theorem inv_max_scalar_terminal_sub_terminal_le
    {i : Fin H.eventCount} {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}
    (x : (H.event i).incoming.terminalRegularOpen)
    (A : BackwardPointTrace H first i.castSucc hle x.val)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.castSucc ≤ i.castSucc,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf hl)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ^ 2)
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.castSucc ≤ i.castSucc)
    (y : (H.event j).incoming.terminalRegularOpen) (hy : y.val = A.point j.castSucc hf hl) :
    |(max q (metricScalarAt (H.event j).terminal.metric y))⁻¹ -
      (max q (metricScalarAt (H.event i).terminal.metric x))⁻¹| ≤
      C * (H.time i.succ - H.time j.succ) := by
  have hlim := ((tendsto_const_nhds.max ((H.event j).terminal.tendsto_metricScalarAt y)).inv₀
    (ne_of_gt (hq.trans_le (le_max_left _ _))))
  apply le_of_tendsto_of_tendsto ((hlim.sub tendsto_const_nhds).abs)
    (tendsto_const_nhds.mul (tendsto_const_nhds.sub
      (tendsto_id.mono_left nhdsWithin_le_nhds)))
  filter_upwards [Ioo_mem_nhdsLT (H.event j).incoming.lt] with t ht
  have hh := inv_max_scalar_sub_terminal_le_at_time x A hq hbound j hf hl ⟨ht.1.le,ht.2⟩
  rw [← hy] at hh
  exact hh


private theorem scalar_le_two_mul_of_reciprocal_bound
    {q Q R Rlast Δ : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hscalar : Rlast ≤ Q)
    (hrec : |(max q R)⁻¹ - (max q Rlast)⁻¹| ≤ C * Δ)
    (htime : 2 * C * Δ * Q ≤ 1) : R ≤ 2 * Q := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hinv : Q⁻¹ ≤ (max q Rlast)⁻¹ :=
    inv_anti₀ (hq.trans_le (le_max_left _ _)) (max_le hqQ hscalar)
  have hhalf : C * Δ ≤ (2 * Q)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Q)).mpr
    nlinarith
  have htwo : Q⁻¹ = 2 * (2 * Q)⁻¹ := by field_simp
  have hlower : (2 * Q)⁻¹ ≤ (max q R)⁻¹ := by
    rw [htwo] at hinv
    linarith [(abs_le.mp hrec).1]
  exact (le_max_right _ _).trans
    ((inv_le_inv₀ (by positivity : 0 < 2 * Q) (hq.trans_le (le_max_left q R))).mp hlower)

section

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {endpoint : (H.stage last).Carrier}

theorem inv_max_scalar_sub_le_at_times
    (A : BackwardPointTrace H first last hle endpoint)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (j k : Fin H.eventCount) (hj : first ≤ j.castSucc) (hjk : j ≤ k)
    (hk : k.castSucc ≤ last)
    (hbound : ∀ l : Fin H.eventCount, ∀ hf : j.castSucc ≤ l.castSucc,
      ∀ hl : l.castSucc ≤ k.castSucc, ∀ t ∈ Ioo (H.time l.castSucc) (H.time l.succ),
      q < (H.event l).incoming.flow.scalar t (A.point l.castSucc (hj.trans hf) (hl.trans hk)) →
      |derivWithin (fun v => (H.event l).incoming.flow.scalar v
        (A.point l.castSucc (hj.trans hf) (hl.trans hk))) (Iic t) t| ≤
        C * (H.event l).incoming.flow.scalar t (A.point l.castSucc (hj.trans hf) (hl.trans hk)) ^ 2)
    {t b : ℝ} (ht : t ∈ Ico (H.time j.castSucc) (H.time j.succ))
    (hb : b ∈ Ico (H.time k.castSucc) (H.time k.succ)) (htb : t ≤ b) :
    |(max q ((H.event j).incoming.flow.scalar t
        (A.point j.castSucc hj (Fin.castSucc_le_castSucc_iff.mpr hjk |>.trans hk))))⁻¹ -
      (max q ((H.event k).incoming.flow.scalar b
        (A.point k.castSucc (hj.trans (Fin.castSucc_le_castSucc_iff.mpr hjk)) hk)))⁻¹| ≤
      C * (b - t) := by
  have hjk' : j.castSucc ≤ k.castSucc := Fin.castSucc_le_castSucc_iff.mpr hjk
  have hfk : first ≤ k.castSucc := hj.trans hjk'
  have hlip := (H.event k).incoming.lipschitzOnWith_inv_max_scalar_at hq
    (A.point k.castSucc hfk hk) (hbound k hjk' le_rfl)
  by_cases he : j = k
  · subst j
    have hh := hlip.dist_le_mul t ht b hb
    simpa only [Real.dist_eq, abs_sub_comm t b, abs_of_nonneg (sub_nonneg.mpr htb)] using hh
  have hjnext : j.succ ≤ k.castSucc := by
    change j.val + 1 ≤ k.val
    have hne : j.val ≠ k.val := fun h => he (Fin.ext h)
    have hjval : j.val ≤ k.val := hjk
    omega
  let B := (A.restrictLast hfk hk).restrictFirst hj hjk'
  have hstep := B.inv_max_scalar_sub_endpoint_le_at_time hq
    (fun l hf hl => hbound l hf (l.castSucc_lt_succ.le.trans hl))
    j le_rfl hjnext ht
  have htail := hlip.dist_le_mul (H.time k.castSucc) ⟨le_rfl, (H.event k).incoming.lt⟩ b hb
  rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (H.time k.castSucc) b,
    abs_of_nonneg (sub_nonneg.mpr hb.1)] at htail
  change |(max q (metricScalarAt ((H.event k).incoming.flow.base.metric
    (H.time k.castSucc)) (A.point k.castSucc hfk hk)))⁻¹ - _| ≤ _ at htail
  rw [H.event_initial k] at htail
  have htri := abs_sub_le
    ((max q ((H.event j).incoming.flow.scalar t (A.point j.castSucc hj (hjk'.trans hk))))⁻¹)
    ((max q (metricScalarAt (H.initialMetric k.castSucc) (A.point k.castSucc hfk hk)))⁻¹)
    ((max q ((H.event k).incoming.flow.scalar b (A.point k.castSucc hfk hk)))⁻¹)
  dsimp only [B, restrictLast, restrictFirst] at hstep
  nlinarith

theorem scalar_le_two_mul_of_scalar_le_at_time
    (A : BackwardPointTrace H first last hle endpoint)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (j k : Fin H.eventCount) (hj : first ≤ j.castSucc) (hjk : j ≤ k)
    (hk : k.castSucc ≤ last)
    (hbound : ∀ l : Fin H.eventCount, ∀ hf : j.castSucc ≤ l.castSucc,
      ∀ hl : l.castSucc ≤ k.castSucc, ∀ t ∈ Ioo (H.time l.castSucc) (H.time l.succ),
      q < (H.event l).incoming.flow.scalar t (A.point l.castSucc (hj.trans hf) (hl.trans hk)) →
      |derivWithin (fun v => (H.event l).incoming.flow.scalar v
        (A.point l.castSucc (hj.trans hf) (hl.trans hk))) (Iic t) t| ≤
        C * (H.event l).incoming.flow.scalar t (A.point l.castSucc (hj.trans hf) (hl.trans hk)) ^ 2)
    {t b : ℝ} (ht : t ∈ Ico (H.time j.castSucc) (H.time j.succ))
    (hb : b ∈ Ico (H.time k.castSucc) (H.time k.succ)) (htb : t ≤ b)
    (hqQ : q ≤ Q)
    (hscalar : (H.event k).incoming.flow.scalar b
      (A.point k.castSucc (hj.trans (Fin.castSucc_le_castSucc_iff.mpr hjk)) hk) ≤ Q)
    (htime : 2 * C * (b - t) * Q ≤ 1) :
    (H.event j).incoming.flow.scalar t
      (A.point j.castSucc hj (Fin.castSucc_le_castSucc_iff.mpr hjk |>.trans hk)) ≤ 2 * Q :=
  scalar_le_two_mul_of_reciprocal_bound hq hqQ hscalar
    (A.inv_max_scalar_sub_le_at_times hq j k hj hjk hk hbound ht hb htb) htime

theorem scalar_le_two_mul_of_earlier_scalar_le_at_time
    (A : BackwardPointTrace H first last hle endpoint)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (j k : Fin H.eventCount) (hj : first ≤ j.castSucc) (hjk : j ≤ k)
    (hk : k.castSucc ≤ last)
    (hbound : ∀ l : Fin H.eventCount, ∀ hf : j.castSucc ≤ l.castSucc,
      ∀ hl : l.castSucc ≤ k.castSucc, ∀ t ∈ Ioo (H.time l.castSucc) (H.time l.succ),
      q < (H.event l).incoming.flow.scalar t (A.point l.castSucc (hj.trans hf) (hl.trans hk)) →
      |derivWithin (fun v => (H.event l).incoming.flow.scalar v
        (A.point l.castSucc (hj.trans hf) (hl.trans hk))) (Iic t) t| ≤
        C * (H.event l).incoming.flow.scalar t (A.point l.castSucc (hj.trans hf) (hl.trans hk)) ^ 2)
    {t b : ℝ} (ht : t ∈ Ico (H.time j.castSucc) (H.time j.succ))
    (hb : b ∈ Ico (H.time k.castSucc) (H.time k.succ)) (htb : t ≤ b)
    (hqQ : q ≤ Q)
    (hscalar : (H.event j).incoming.flow.scalar t
      (A.point j.castSucc hj (Fin.castSucc_le_castSucc_iff.mpr hjk |>.trans hk)) ≤ Q)
    (htime : 2 * C * (b - t) * Q ≤ 1) :
    (H.event k).incoming.flow.scalar b
      (A.point k.castSucc (hj.trans (Fin.castSucc_le_castSucc_iff.mpr hjk)) hk) ≤ 2 * Q :=
  scalar_le_two_mul_of_reciprocal_bound hq hqQ hscalar
    (by simpa only [abs_sub_comm] using
      A.inv_max_scalar_sub_le_at_times hq j k hj hjk hk hbound ht hb htb) htime

theorem inv_max_scalar_terminal_sub_le_at_time
    (A : BackwardPointTrace H first last hle endpoint)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (j k : Fin H.eventCount) (hj : first ≤ j.castSucc) (hjk : j.succ ≤ k.castSucc)
    (hk : k.castSucc ≤ last)
    (hbound : ∀ l : Fin H.eventCount, ∀ hf : j.succ ≤ l.castSucc,
      ∀ hl : l.castSucc ≤ k.castSucc, ∀ t ∈ Ioo (H.time l.castSucc) (H.time l.succ),
      q < (H.event l).incoming.flow.scalar t (A.point l.castSucc (hj.trans (j.castSucc_lt_succ.le.trans hf)) (hl.trans hk)) →
      |derivWithin (fun v => (H.event l).incoming.flow.scalar v
        (A.point l.castSucc (hj.trans (j.castSucc_lt_succ.le.trans hf)) (hl.trans hk))) (Iic t) t| ≤
        C * (H.event l).incoming.flow.scalar t (A.point l.castSucc (hj.trans (j.castSucc_lt_succ.le.trans hf)) (hl.trans hk)) ^ 2)
    (y : (H.event j).incoming.terminalRegularOpen)
    (hy : y.val = A.point j.castSucc hj (j.castSucc_lt_succ.le.trans (hjk.trans hk)))
    {b : ℝ} (hb : b ∈ Ico (H.time k.castSucc) (H.time k.succ)) :
    |(max q (metricScalarAt (H.event j).terminal.metric y))⁻¹ -
      (max q ((H.event k).incoming.flow.scalar b
        (A.point k.castSucc (hj.trans (j.castSucc_lt_succ.le.trans hjk)) hk)))⁻¹| ≤
      C * (b - H.time j.succ) := by
  have hfk : first ≤ k.castSucc := hj.trans (j.castSucc_lt_succ.le.trans hjk)
  let B := (A.restrictLast hfk hk).restrictFirst (hj.trans j.castSucc_lt_succ.le) hjk
  have hstep := B.inv_max_scalar_sub_endpoint_le k.castSucc j.succ hjk
    (A.point k.castSucc hfk hk) hq
    (fun l hf hl => hbound l hf (l.castSucc_lt_succ.le.trans hl))
  have hlip := (H.event k).incoming.lipschitzOnWith_inv_max_scalar_at hq
    (A.point k.castSucc hfk hk) (hbound k hjk le_rfl)
  have htail := hlip.dist_le_mul (H.time k.castSucc) ⟨le_rfl, (H.event k).incoming.lt⟩ b hb
  rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (H.time k.castSucc) b,
    abs_of_nonneg (sub_nonneg.mpr hb.1)] at htail
  change |(max q (metricScalarAt ((H.event k).incoming.flow.base.metric
    (H.time k.castSucc)) (A.point k.castSucc hfk hk)))⁻¹ - _| ≤ _ at htail
  rw [H.event_initial k] at htail
  have hcross := A.crossing j hj (hjk.trans hk)
  rw [← hy] at hcross
  have hscalar := MetricCutCapEvent.RegularCrossing.scalar_eq (H.event j) (p := y) hcross
  rw [H.event_output j] at hscalar
  rw [hscalar]
  have htri := abs_sub_le
    ((max q (metricScalarAt (H.initialMetric j.succ)
      (A.point j.succ (hj.trans j.castSucc_lt_succ.le) (hjk.trans hk))))⁻¹)
    ((max q (metricScalarAt (H.initialMetric k.castSucc) (A.point k.castSucc hfk hk)))⁻¹)
    ((max q ((H.event k).incoming.flow.scalar b (A.point k.castSucc hfk hk)))⁻¹)
  dsimp only [B, restrictLast, restrictFirst] at hstep
  nlinarith


theorem terminal_scalar_le_two_mul_of_scalar_le_at_time
    (A : BackwardPointTrace H first last hle endpoint)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (j k : Fin H.eventCount) (hj : first ≤ j.castSucc) (hjk : j.succ ≤ k.castSucc)
    (hk : k.castSucc ≤ last)
    (hbound : ∀ l : Fin H.eventCount, ∀ hf : j.succ ≤ l.castSucc,
      ∀ hl : l.castSucc ≤ k.castSucc, ∀ t ∈ Ioo (H.time l.castSucc) (H.time l.succ),
      q < (H.event l).incoming.flow.scalar t (A.point l.castSucc (hj.trans (j.castSucc_lt_succ.le.trans hf)) (hl.trans hk)) →
      |derivWithin (fun v => (H.event l).incoming.flow.scalar v
        (A.point l.castSucc (hj.trans (j.castSucc_lt_succ.le.trans hf)) (hl.trans hk))) (Iic t) t| ≤
        C * (H.event l).incoming.flow.scalar t (A.point l.castSucc (hj.trans (j.castSucc_lt_succ.le.trans hf)) (hl.trans hk)) ^ 2)
    (y : (H.event j).incoming.terminalRegularOpen)
    (hy : y.val = A.point j.castSucc hj (j.castSucc_lt_succ.le.trans (hjk.trans hk)))
    {b : ℝ} (hb : b ∈ Ico (H.time k.castSucc) (H.time k.succ))
    (hqQ : q ≤ Q)
    (hscalar : (H.event k).incoming.flow.scalar b
      (A.point k.castSucc (hj.trans (j.castSucc_lt_succ.le.trans hjk)) hk) ≤ Q)
    (htime : 2 * C * (b - H.time j.succ) * Q ≤ 1) :
    metricScalarAt (H.event j).terminal.metric y ≤ 2 * Q :=
  scalar_le_two_mul_of_reciprocal_bound hq hqQ hscalar
    (A.inv_max_scalar_terminal_sub_le_at_time hq j k hj hjk hk hbound y hy hb) htime
end


theorem scalar_le_two_mul_terminal_of_time_sub_le
    {i : Fin H.eventCount} {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}
    (x : (H.event i).incoming.terminalRegularOpen)
    (A : BackwardPointTrace H first i.castSucc hle x.val)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.castSucc ≤ i.castSucc,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf hl)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ^ 2)
    (hscalar : metricScalarAt (H.event i).terminal.metric x ≤ Q)
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.castSucc ≤ i.castSucc)
    {t : ℝ} (ht : t ∈ Ico (H.time j.castSucc) (H.time j.succ))
    (htime : 2 * C * (H.time i.succ - t) * Q ≤ 1) :
    (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ≤ 2 * Q :=
  scalar_le_two_mul_of_reciprocal_bound hq hqQ hscalar
    (inv_max_scalar_sub_terminal_le_at_time x A hq hbound j hf hl ht) htime


theorem scalar_le_two_mul_of_terminal_scalar_le_three_halves
    {i : Fin H.eventCount} {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}
    (x : (H.event i).incoming.terminalRegularOpen)
    (A : BackwardPointTrace H first i.castSucc hle x.val)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.castSucc ≤ i.castSucc,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf hl)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ^ 2)
    (hscalar : metricScalarAt (H.event i).terminal.metric x ≤ (3 / 2 : ℝ) * Q)
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.castSucc ≤ i.castSucc)
    {t : ℝ} (ht : t ∈ Ico (H.time j.castSucc) (H.time j.succ))
    (htime : 6 * C * (H.time i.succ - t) * Q ≤ 1) :
    (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ≤ 2 * Q := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hrec := inv_max_scalar_sub_terminal_le_at_time x A hq hbound j hf hl ht
  have hinv : ((3 / 2 : ℝ) * Q)⁻¹ ≤
      (max q (metricScalarAt (H.event i).terminal.metric x))⁻¹ :=
    inv_anti₀ (hq.trans_le (le_max_left _ _)) (max_le (by linarith) hscalar)
  have hsmall : C * (H.time i.succ - t) ≤ (6 * Q)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 6 * Q)).mpr
    nlinarith
  have heq : ((3 / 2 : ℝ) * Q)⁻¹ = (2 * Q)⁻¹ + (6 * Q)⁻¹ := by field_simp; ring
  have hlower : (2 * Q)⁻¹ ≤
      (max q ((H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl)))⁻¹ := by
    rw [heq] at hinv
    linarith [(abs_le.mp hrec).1]
  exact (le_max_right _ _).trans ((inv_le_inv₀ (by positivity : 0 < 2 * Q)
    (hq.trans_le (le_max_left _ _))).mp hlower)


theorem terminal_scalar_le_two_mul_of_time_sub_le
    {i : Fin H.eventCount} {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}
    (x : (H.event i).incoming.terminalRegularOpen)
    (A : BackwardPointTrace H first i.castSucc hle x.val)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.castSucc ≤ i.castSucc,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf hl)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ^ 2)
    (hscalar : metricScalarAt (H.event i).terminal.metric x ≤ (3 / 2 : ℝ) * Q)
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.castSucc ≤ i.castSucc)
    (y : (H.event j).incoming.terminalRegularOpen) (hy : y.val = A.point j.castSucc hf hl)
    (htime : 6 * C * (H.time i.succ - H.time j.succ) * Q ≤ 1) :
    metricScalarAt (H.event j).terminal.metric y ≤ 2 * Q := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hrec := inv_max_scalar_terminal_sub_terminal_le x A hq hbound j hf hl y hy
  have hinv : ((3 / 2 : ℝ) * Q)⁻¹ ≤
      (max q (metricScalarAt (H.event i).terminal.metric x))⁻¹ :=
    inv_anti₀ (hq.trans_le (le_max_left _ _)) (max_le (by linarith) hscalar)
  have hsmall : C * (H.time i.succ - H.time j.succ) ≤ (6 * Q)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 6 * Q)).mpr
    nlinarith
  have heq : ((3 / 2 : ℝ) * Q)⁻¹ = (2 * Q)⁻¹ + (6 * Q)⁻¹ := by field_simp; ring
  have hlower : (2 * Q)⁻¹ ≤
      (max q (metricScalarAt (H.event j).terminal.metric y))⁻¹ := by
    rw [heq] at hinv
    linarith [(abs_le.mp hrec).1]
  exact (le_max_right _ _).trans ((inv_le_inv₀ (by positivity : 0 < 2 * Q)
    (hq.trans_le (le_max_left _ _))).mp hlower)


theorem riemannNorm_le_of_terminal_scalar_le
    {i : Fin H.eventCount} {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}
    (x : (H.event i).incoming.terminalRegularOpen)
    (A : BackwardPointTrace H first i.castSucc hle x.val)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.castSucc ≤ i.castSucc,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf hl)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ^ 2)
    (hscalar : metricScalarAt (H.event i).terminal.metric x ≤ 2 * Q)
    {Phi : ℝ → ℝ} (hPhi : DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      DifferentialGeometry.PDE.RicciFlow.Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.castSucc ≤ i.castSucc)
    {t : ℝ} (ht : t ∈ Ico (H.time j.castSucc) (H.time j.succ))
    (htime : 4 * C * (H.time i.succ - t) * Q ≤ 1) :
    (H.event j).incoming.riemannNorm t (A.point j.castSucc hf hl) ≤
      4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0) := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hs := scalar_le_two_mul_terminal_of_time_sub_le x A hq (by linarith : q ≤ 2 * Q)
    hbound hscalar j hf hl ht (by nlinarith : 2 * C * (H.time i.succ - t) * (2 * Q) ≤ 1)
  have hub : (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ≤ 4 * Q := by
    linarith
  have hbridge : DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.RmNormBoundOn (H.event j).incoming.flow
      (2 * Real.sqrt 3) := fun t y basis horth _ ha =>
    DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.sqrt_rmNormSq_le_of_abs_orderedSectionalCurvaturesAt_le
      (H.event j).incoming.flow t y basis horth ha
  have hr := DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.sqrt_rmNormSq_le_of_scalar_le
    (by positivity : 0 ≤ 2 * Real.sqrt 3) hbridge hPhi (hpinch j hf hl)
    (by simp [ThreeSpace] : Module.finrank ℝ ThreeSpace = 3) ht
    (A.point j.castSucc hf hl) hQ hub
  exact hr.trans_eq (by ring)


theorem riemannNorm_terminal_le_of_terminal_scalar_le
    {i : Fin H.eventCount} {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}
    (x : (H.event i).incoming.terminalRegularOpen)
    (A : BackwardPointTrace H first i.castSucc hle x.val)
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    (hbound : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.castSucc ≤ i.castSucc,
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v
        (A.point j.castSucc hf hl)) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ^ 2)
    (hscalar : metricScalarAt (H.event i).terminal.metric x ≤ 2 * Q)
    {Phi : ℝ → ℝ} (hPhi : DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      DifferentialGeometry.PDE.RicciFlow.Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.castSucc ≤ i.castSucc)
    (y : (H.event j).incoming.terminalRegularOpen) (hy : y.val = A.point j.castSucc hf hl)
    (htime : 6 * C * (H.time i.succ - H.time j.succ) * Q ≤ 1) :
    Real.sqrt (Tensor0SBundle.normSq0S (H.event j).terminal.metric y 4
      (metricRm04At (H.event j).terminal.metric y)) ≤
      4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0) := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have hΔ : 0 ≤ H.time i.succ - H.time j.succ := by
    have hji : j.val ≤ i.val := hl
    exact sub_nonneg.mpr (H.time_strictMono.monotone (by
      change j.val + 1 ≤ i.val + 1
      omega))
  have hsmall : 4 * C * (H.time i.succ - H.time j.succ) * Q < 1 := by
    nlinarith [C.coe_nonneg]
  have hnear : ∀ᶠ t in 𝓝[<] H.time j.succ,
      4 * C * (H.time i.succ - t) * Q ≤ 1 := by
    have hc : ContinuousAt (fun t : ℝ => 4 * C * (H.time i.succ - t) * Q) (H.time j.succ) := by fun_prop
    exact (hc.eventually_lt_const hsmall).filter_mono nhdsWithin_le_nhds |>.mono fun _ h => h.le
  apply le_of_tendsto ((H.event j).terminal.tendsto_riemannNorm y)
  filter_upwards [hnear, Ioo_mem_nhdsLT (H.event j).incoming.lt] with t htime' ht
  have hh := A.riemannNorm_le_of_terminal_scalar_le x hq hqQ hbound hscalar
    hPhi hpinch j hf hl ⟨ht.1.le,ht.2⟩ htime'
  rw [← hy] at hh
  exact hh


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingRoom
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

variable (K : ObservedHistory.{u})

theorem activeStage_eq_of_forall_time_not_mem_Ioc {a b : Icc (0 : ℝ) K.horizon} (hab : a ≤ b)
    (hno : ∀ i : Fin K.eventCount, K.time i.succ ∉ Ioc (a : ℝ) b) :
    K.activeStage a = K.activeStage b := by
  refine le_antisymm (K.activeStage_mono hab) ?_
  by_contra h
  have hlt : K.activeStage a < K.activeStage b := lt_of_not_ge h
  have hne : K.activeStage a ≠ Fin.last K.eventCount := ne_of_lt (hlt.trans_le (Fin.le_last _))
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hne
  exact hno i ((K.crossed_event_iff_mem_Ioc a b i).mp
    ⟨hi.ge, Fin.castSucc_lt_iff_succ_le.mp (hi.trans_lt hlt)⟩)

theorem stageMetric_inner_le_exp_of_normSq_le (k : Fin (K.eventCount + 1))
    (x : (K.stage k).Carrier) {a b C s w : ℝ} (hak : K.time k ≤ a)
    (hnext : ∀ i : Fin K.eventCount, k = i.castSucc → b < K.time i.succ) (hb : b ≤ K.horizon)
    (hbound : ∀ r ∈ Icc a b,
      normSq0S (K.stageMetric k r) x 4 (metricRm04At (K.stageMetric k r) x) ≤ C)
    (hs : s ∈ Icc a b) (hw : w ∈ Icc a b) (ξ : TangentSpace ThreeModel x) :
    (K.stageMetric k s).inner x ξ ξ ≤
      Real.exp (18 * Real.sqrt C * |s - w|) * (K.stageMetric k w).inner x ξ ξ := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  cases k using Fin.lastCases with
  | last =>
    by_cases h : K.time (Fin.last K.eventCount) < K.horizon
    · simp only [ObservedHistory.stageMetric_last_of_lt (h := h)] at hbound ⊢
      have hc := (metric_inner_exp_bounds_of_curvature_bound (K.finalSlab h).flow
        (K.finalSlab h).equation (a := a) (b := b)
        (fun r hr => ⟨hak.trans hr.1, hr.2.trans hb⟩)
        (fun r hr => ⟨hak.trans_lt hr.1, hr.2.trans_le hb⟩) x hbound hs hw ξ).2
      rw [hdim] at hc
      convert hc using 3
      push_cast
      ring
    · simp only [ObservedHistory.stageMetric_last_of_le (not_lt.mp h)]
      have h0 := metric_inner_self_nonneg (K.initialMetric (Fin.last K.eventCount)) x ξ
      have h1 : 1 ≤ Real.exp (18 * Real.sqrt C * |s - w|) :=
        Real.one_le_exp (by positivity)
      nlinarith
  | cast i =>
    simp only [ObservedHistory.stageMetric_castSucc_apply] at hbound ⊢
    have hbi := hnext i rfl
    have hc := (metric_inner_exp_bounds_of_curvature_bound (K.event i).incoming.flow
      (K.event i).incoming.equation (a := a) (b := b)
      (fun r hr => ⟨hak.trans hr.1, hr.2.trans_lt hbi⟩)
      (fun r hr => ⟨hak.trans_lt hr.1, hr.2.trans hbi⟩) x hbound hs hw ξ).2
    rw [hdim] at hc
    convert hc using 3
    push_cast
    ring

end ObservedHistory

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

private theorem time_lt_succ_of_activeStage_eq_castSucc (t : Icc (0 : ℝ) H.toHistory.horizon)
    (i : Fin H.eventCount) (hi : H.toHistory.activeStage t = i.castSucc) :
    (t : ℝ) < H.time i.succ := by
  have hval : (H.toHistory.activeStage t).val < H.toHistory.eventCount := by
    rw [hi]
    exact i.isLt
  have h := H.toHistory.activeStage_before_next t hval
  have he : (⟨(H.toHistory.activeStage t).val + 1, Nat.succ_lt_succ hval⟩ :
      Fin (H.toHistory.eventCount + 1)) = i.succ := by
    ext
    simp [hi]
  rw [he] at h
  exact h

private theorem le_two_mul_of_abs_inv_max_sub_le_of_time {M R Rt Δ : ℝ} {C : ℝ≥0}
    (hM : 0 < M) (hRt : Rt ≤ M) (hrec : |(max M R)⁻¹ - (max M Rt)⁻¹| ≤ C * Δ)
    (htime : C * M * Δ ≤ 1 / 2) : R ≤ 2 * M := by
  rw [max_eq_left hRt] at hrec
  have hlow := (abs_le.mp hrec).1
  have hhalf : C * Δ ≤ (2 * M)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by positivity : 0 < 2 * M)]
    nlinarith
  have htwo : M⁻¹ = 2 * (2 * M)⁻¹ := by field_simp
  have hinv : (2 * M)⁻¹ ≤ (max M R)⁻¹ := by linarith
  exact (le_max_right M R).trans
    ((inv_le_inv₀ (by positivity : 0 < 2 * M) (hM.trans_le (le_max_left M R))).mp hinv)

private theorem normSq_le_sq_of_sqrt_le_mul_max {N C R M : ℝ} (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hsqrt : Real.sqrt N ≤ C * max R 1) (hR : R ≤ 2 * M) (hM : 1 ≤ M) :
    N ≤ (2 * C * M) ^ 2 := by
  have hmax : max R 1 ≤ 2 * M := max_le hR (by linarith)
  have h1 : Real.sqrt N ≤ 2 * C * M := hsqrt.trans (by nlinarith)
  calc N = Real.sqrt N ^ 2 := (Real.sq_sqrt hN).symm
    _ ≤ (2 * C * M) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2

private theorem trace_normSq_eq_of_stage_eq' {K : ObservedHistory.{u}}
    {first last : Fin (K.eventCount + 1)} {hle : first ≤ last} {x : (K.stage last).Carrier}
    (A : BackwardPointTrace K first last hle x) {j k : Fin (K.eventCount + 1)} (hjk : j = k)
    (hj : first ≤ j) (hjl : j ≤ last) (hk : first ≤ k) (hkl : k ≤ last) (v : ℝ) :
    normSq0S (K.stageMetric j v) (A.point j hj hjl) 4
      (metricRm04At (K.stageMetric j v) (A.point j hj hjl)) =
    normSq0S (K.stageMetric k v) (A.point k hk hkl) 4
      (metricRm04At (K.stageMetric k v) (A.point k hk hkl)) := by
  subst hjk
  rfl

theorem scalar_le_two_mul_of_backwardPointTrace_of_scalar_le_at
    {Ctime : ℝ≥0} {qcan M : ℝ} {u' u t : Icc (0 : ℝ) H.toHistory.horizon}
    (hu'u : u' ≤ u) (hut : u ≤ t)
    {p : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage u')
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono (hu'u.trans hut)) p)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hM : 0 < M) (hqcan : qcan ≤ M)
    (hanchor : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage u) u)
      (A.point (H.toHistory.activeStage u) (H.toHistory.activeStage_mono hu'u)
        (H.toHistory.activeStage_mono hut)) ≤ M)
    (htime : Ctime * M * ((u : ℝ) - u') ≤ 1 / 2)
    (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u' ≤ v) (hvu : v ≤ u) :
    metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
      (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
        (H.toHistory.activeStage_mono (hvu.trans hut))) ≤ 2 * M := by
  have hk1 := H.toHistory.activeStage_mono hu'u
  have hk2 := H.toHistory.activeStage_mono hut
  have hut' : (u : ℝ) ≤ t := hut
  have hcur : ∀ i : Fin H.eventCount, i.castSucc = H.toHistory.activeStage u →
      (H.toHistory.event i).incoming.DerivativeBoundBefore Ctime qcan u := by
    intro i hi
    rcases eq_or_lt_of_le hk2 with heq | hlt
    · exact (H.toHistory.event i).incoming.derivativeBoundBefore_mono hut'
        (hcurrent i (hi.trans heq))
    · exact (H.toHistory.event i).incoming.derivativeBoundBefore_mono
        (H.time_lt_succ_of_activeStage_eq_castSucc u i hi.symm).le
        (hslabs i (hi.trans_lt hlt))
  have hfin : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage u = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan u :=
    fun h hl => ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).derivativeBoundBefore_mono
      hut' (hfinal h (le_antisymm (Fin.le_last _) (hl.symm.trans_le hk2)))
  have hrec :=
    (A.restrictLast hk1 hk2).inv_max_stageMetric_scalar_sub_le_of_derivativeBoundBefore
      hM hqcan (H.toHistory.activeStage_time_le u)
      (fun i hi => H.time_lt_succ_of_activeStage_eq_castSucc u i hi) u.2.2
      (fun i hi => hslabs i (hi.trans_le hk2)) hcur hfin
      (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
      (H.toHistory.activeStage_mono hvu) (H.toHistory.activeStage_time_le v)
      (fun i hi => H.time_lt_succ_of_activeStage_eq_castSucc v i hi) hvu
  rw [BackwardPointTrace.restrictLast_point] at hrec
  refine le_two_mul_of_abs_inv_max_sub_le_of_time hM hanchor hrec ?_
  have hv : (u' : ℝ) ≤ v := huv
  have hC : 0 ≤ (Ctime : ℝ) * M := mul_nonneg Ctime.coe_nonneg hM.le
  nlinarith

theorem scalar_le_two_mul_of_backwardPointTrace_of_scalar_le_above
    {Ctime : ℝ≥0} {qcan M : ℝ} {u' u t : Icc (0 : ℝ) H.toHistory.horizon}
    (hu'u : u' ≤ u) (hut : u ≤ t)
    {p : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage u')
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono (hu'u.trans hut)) p)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hM : 0 < M) (hqcan : qcan ≤ M)
    (hupper : ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u' ≤ v) (hvt : v ≤ t), u ≤ v →
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
          (H.toHistory.activeStage_mono hvt)) ≤ M)
    (htime : Ctime * M * ((u : ℝ) - u') ≤ 1 / 2) :
    ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u' ≤ v) (hvt : v ≤ t),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
          (H.toHistory.activeStage_mono hvt)) ≤ 2 * M := by
  intro v huv hvt
  by_cases hvu : v ≤ u
  · exact H.scalar_le_two_mul_of_backwardPointTrace_of_scalar_le_at hu'u hut A hslabs hcurrent
      hfinal hM hqcan (hupper u hu'u hut le_rfl) htime v huv hvu
  · exact (hupper v huv hvt (lt_of_not_ge hvu).le).trans (by linarith)

theorem normSq_rm_le_of_backwardPointTrace_of_scalar_le_two_mul
    {M : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {a t : Icc (0 : ℝ) H.toHistory.horizon} (hat : a ≤ t)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    {p : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage a)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hat) p)
    (hM : 1 ≤ M)
    (hscal : ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hav)
          (H.toHistory.activeStage_mono hvt)) ≤ 2 * M) :
    (∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hav)
          (H.toHistory.activeStage_mono hvt)) 4
        (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hav)
            (H.toHistory.activeStage_mono hvt))) ≤
        (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2) ∧
    ∀ (i : Fin H.eventCount) (hf : H.toHistory.activeStage a ≤ i.castSucc)
      (hl : i.succ ≤ H.toHistory.activeStage t),
      let x : (H.toHistory.event i).incoming.terminalRegularOpen :=
        ⟨A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
          (A.crossing i hf hl).mem_terminalRegularRegion (H.toHistory.event i)⟩
      normSq0S (H.toHistory.event i).terminal.metric x 4
          (metricRm04At (H.toHistory.event i).terminal.metric x) ≤
        (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by
  have hC : 0 ≤ 4 * Real.sqrt 3 * (1 + phi 1 + phi 0) := by
    have := hphi.pos 0
    have := hphi.pos 1
    positivity
  have hall : ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hav)
          (H.toHistory.activeStage_mono hvt)) 4
        (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hav)
            (H.toHistory.activeStage_mono hvt))) ≤
        (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by
    intro v hav hvt
    have hv : H.toHistory.activeStage v = Fin.last H.eventCount →
        ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
          Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
            (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi := fun h =>
      hlast (le_antisymm (Fin.le_last _) (h ▸ H.toHistory.activeStage_mono hvt))
    have hs := H.sqrt_rmNormSq_stageMetric_le_of_pinched hphi hpinch v hv
      (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hav)
        (H.toHistory.activeStage_mono hvt))
    have hN := normSq_le_sq_of_sqrt_le_mul_max (normSq0S_nonneg _ _ _ _) hC hs
      (hscal v hav hvt) hM
    calc _ ≤ (2 * (4 * Real.sqrt 3 * (1 + phi 1 + phi 0)) * M) ^ 2 := hN
      _ = (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by ring
  refine ⟨hall, ?_⟩
  intro i hf hl x
  have hIoc := (H.toHistory.crossed_event_iff_mem_Ioc a t i).mp ⟨hf, hl⟩
  let v : Icc (0 : ℝ) H.toHistory.horizon :=
    ⟨H.time i.succ, H.toHistory.time_nonneg _, H.toHistory.time_le_horizon_at _⟩
  have hav' : H.toHistory.activeStage v = i.succ := H.toHistory.activeStage_at_time i.succ
  have hav : a ≤ v := hIoc.1.le
  have hvt : v ≤ t := hIoc.2
  have hb := hall v hav hvt
  rw [trace_normSq_eq_of_stage_eq' A hav' (H.toHistory.activeStage_mono hav)
    (H.toHistory.activeStage_mono hvt) (hf.trans (Fin.castSucc_lt_succ (i := i)).le) hl] at hb
  have hx := MetricCutCapEvent.RegularCrossing.rmNormSq_eq (H.toHistory.event i) (p := x)
    (A.crossing i hf hl)
  rw [hx, H.toHistory.event_output i, ← H.toHistory.stageMetric_initial]
  exact hb

theorem isRmControlled_of_backwardPointTrace_of_scalar_le_two_mul
    {M r : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {a t : Icc (0 : ℝ) H.toHistory.horizon} (hat : a ≤ t)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    {p : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage a)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hat) p)
    (hM : 1 ≤ M)
    (hscal : ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hav)
          (H.toHistory.activeStage_mono hvt)) ≤ 2 * M)
    (hrM : r ^ 4 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 ≤ 1) :
    A.isRmControlled (hat := hat) r := by
  obtain ⟨hall, hcross⟩ :=
    H.normSq_rm_le_of_backwardPointTrace_of_scalar_le_two_mul hphi hpinch hat hlast A hM hscal
  have hr4 : 0 ≤ r ^ 4 := by positivity
  refine ⟨fun v hav hvt => ?_, fun i hf hl => ?_⟩
  · exact (mul_le_mul_of_nonneg_left (hall v hav hvt) hr4).trans hrM
  · exact (mul_le_mul_of_nonneg_left (hcross i hf hl) hr4).trans hrM

theorem exists_backwardPointTrace_scalar_le_two_mul_of_backward_step
    {Ctime : ℝ≥0} {qcan Q R₀ : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u' u t : Icc (0 : ℝ) H.toHistory.horizon} (hu'u : u' ≤ u) (hut : u ≤ t)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hQR : 1 ≤ Q * R₀) (hqcan : qcan ≤ Q * R₀)
    (hdepth : 8 * Ctime * (Q * R₀) * ((u : ℝ) - u') ≤ 1)
    (U : Set (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hU : ∀ x ∈ U, ∀ B : BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
        (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) x,
      ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u ≤ v) (hvt : v ≤ t),
        metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (B.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
            (H.toHistory.activeStage_mono hvt)) ≤ Q * R₀)
    (htrace : ∀ x ∈ U, Nonempty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u')
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono (hu'u.trans hut)) x)) :
    ∀ x ∈ U, ∃ A : BackwardPointTrace H.toHistory (H.toHistory.activeStage u')
        (H.toHistory.activeStage t) (H.toHistory.activeStage_mono (hu'u.trans hut)) x,
      (∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u' ≤ v) (hvt : v ≤ t),
        metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
            (H.toHistory.activeStage_mono hvt)) ≤ 2 * (Q * R₀)) ∧
      (∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u' ≤ v) (hvt : v ≤ t),
        normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
            (H.toHistory.activeStage_mono hvt)) 4
          (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
              (H.toHistory.activeStage_mono hvt))) ≤
          (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (Q * R₀)) ^ 2) ∧
      ∀ (i : Fin H.eventCount) (hf : H.toHistory.activeStage u' ≤ i.castSucc)
        (hl : i.succ ≤ H.toHistory.activeStage t),
        let z : (H.toHistory.event i).incoming.terminalRegularOpen :=
          ⟨A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
            (A.crossing i hf hl).mem_terminalRegularRegion (H.toHistory.event i)⟩
        normSq0S (H.toHistory.event i).terminal.metric z 4
            (metricRm04At (H.toHistory.event i).terminal.metric z) ≤
          (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (Q * R₀)) ^ 2 := by
  intro x hx
  obtain ⟨A⟩ := htrace x hx
  have hM : 0 < Q * R₀ := by linarith
  have htime : Ctime * (Q * R₀) * ((u : ℝ) - u') ≤ 1 / 2 := by nlinarith
  have hscal := H.scalar_le_two_mul_of_backwardPointTrace_of_scalar_le_above hu'u hut A hslabs
    hcurrent hfinal hM hqcan
    (fun v huv hvt huv' => hU x hx (A.restrictFirst (H.toHistory.activeStage_mono hu'u)
      (H.toHistory.activeStage_mono hut)) v huv' hvt) htime
  obtain ⟨hall, hcross⟩ := H.normSq_rm_le_of_backwardPointTrace_of_scalar_le_two_mul hphi
    hpinch (hu'u.trans hut) hlast A hQR hscal
  exact ⟨A, hscal, hall, hcross⟩

private theorem eight_mul_depth_le_one_of_eq {Ctime : ℝ≥0} {M u u' : ℝ} (hM : 0 ≤ M)
    (hu' : u' = u - 1 / (8 * Ctime * M)) :
    u' ≤ u ∧ 8 * Ctime * M * (u - u') ≤ 1 := by
  have hC : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
  have hd : u - u' = 1 / (8 * Ctime * M) := by rw [hu']; ring
  have hnn : 0 ≤ 1 / (8 * Ctime * M) := by positivity
  refine ⟨by linarith, ?_⟩
  rw [hd]
  rcases eq_or_lt_of_le (show 0 ≤ 8 * (Ctime : ℝ) * M by positivity) with h0 | hpos
  · rw [← h0]
    norm_num
  · rw [mul_one_div, div_self hpos.ne']

theorem exists_backwardPointTrace_scalar_le_two_mul_of_depth_eq
    {Ctime : ℝ≥0} {qcan Q R₀ : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u' u t : Icc (0 : ℝ) H.toHistory.horizon} (hu'u : u' ≤ u) (hut : u ≤ t)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hQR : 1 ≤ Q * R₀) (hqcan : qcan ≤ Q * R₀)
    (hu' : (u' : ℝ) = u - 1 / (8 * Ctime * (Q * R₀)))
    (U : Set (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hU : ∀ x ∈ U, ∀ B : BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
        (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) x,
      ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u ≤ v) (hvt : v ≤ t),
        metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (B.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
            (H.toHistory.activeStage_mono hvt)) ≤ Q * R₀)
    (htrace : ∀ x ∈ U, Nonempty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u')
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono (hu'u.trans hut)) x)) :
    ∀ x ∈ U, ∃ A : BackwardPointTrace H.toHistory (H.toHistory.activeStage u')
        (H.toHistory.activeStage t) (H.toHistory.activeStage_mono (hu'u.trans hut)) x,
      (∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u' ≤ v) (hvt : v ≤ t),
        metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
            (H.toHistory.activeStage_mono hvt)) ≤ 2 * (Q * R₀)) ∧
      (∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u' ≤ v) (hvt : v ≤ t),
        normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
            (H.toHistory.activeStage_mono hvt)) 4
          (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
              (H.toHistory.activeStage_mono hvt))) ≤
          (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (Q * R₀)) ^ 2) ∧
      ∀ (i : Fin H.eventCount) (hf : H.toHistory.activeStage u' ≤ i.castSucc)
        (hl : i.succ ≤ H.toHistory.activeStage t),
        let z : (H.toHistory.event i).incoming.terminalRegularOpen :=
          ⟨A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
            (A.crossing i hf hl).mem_terminalRegularRegion (H.toHistory.event i)⟩
        normSq0S (H.toHistory.event i).terminal.metric z 4
            (metricRm04At (H.toHistory.event i).terminal.metric z) ≤
          (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (Q * R₀)) ^ 2 :=
  H.exists_backwardPointTrace_scalar_le_two_mul_of_backward_step hphi hpinch hu'u hut hlast hslabs
    hcurrent hfinal hQR hqcan (eight_mul_depth_le_one_of_eq (by linarith) hu').2 U hU htrace

theorem exists_backwardPointTrace_scalar_le_two_mul_of_backward_step_of_no_event
    {Ctime : ℝ≥0} {qcan Q R₀ : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u' u t : Icc (0 : ℝ) H.toHistory.horizon} (hu'u : u' ≤ u) (hut : u ≤ t)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hQR : 1 ≤ Q * R₀) (hqcan : qcan ≤ Q * R₀)
    (hdepth : 8 * Ctime * (Q * R₀) * ((u : ℝ) - u') ≤ 1)
    (hno : ∀ i : Fin H.eventCount, H.time i.succ ∉ Ioc (u' : ℝ) u)
    (U : Set (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hU : ∀ x ∈ U, ∀ B : BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
        (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) x,
      ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u ≤ v) (hvt : v ≤ t),
        metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (B.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
            (H.toHistory.activeStage_mono hvt)) ≤ Q * R₀)
    (htraceU : ∀ x ∈ U, Nonempty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) x)) :
    ∀ x ∈ U, ∃ A : BackwardPointTrace H.toHistory (H.toHistory.activeStage u')
        (H.toHistory.activeStage t) (H.toHistory.activeStage_mono (hu'u.trans hut)) x,
      (∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u' ≤ v) (hvt : v ≤ t),
        metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
            (H.toHistory.activeStage_mono hvt)) ≤ 2 * (Q * R₀)) ∧
      (∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u' ≤ v) (hvt : v ≤ t),
        normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
            (H.toHistory.activeStage_mono hvt)) 4
          (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
              (H.toHistory.activeStage_mono hvt))) ≤
          (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (Q * R₀)) ^ 2) ∧
      (∀ (i : Fin H.eventCount) (hf : H.toHistory.activeStage u' ≤ i.castSucc)
        (hl : i.succ ≤ H.toHistory.activeStage t),
        let z : (H.toHistory.event i).incoming.terminalRegularOpen :=
          ⟨A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
            (A.crossing i hf hl).mem_terminalRegularRegion (H.toHistory.event i)⟩
        normSq0S (H.toHistory.event i).terminal.metric z 4
            (metricRm04At (H.toHistory.event i).terminal.metric z) ≤
          (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (Q * R₀)) ^ 2) ∧
      ∀ s ∈ Icc (u' : ℝ) u, ∀ w ∈ Icc (u' : ℝ) u,
        ∀ ξ : TangentSpace ThreeModel
          (A.point (H.toHistory.activeStage u) (H.toHistory.activeStage_mono hu'u)
            (H.toHistory.activeStage_mono hut)),
          (H.toHistory.stageMetric (H.toHistory.activeStage u) s).inner
              (A.point (H.toHistory.activeStage u) (H.toHistory.activeStage_mono hu'u)
                (H.toHistory.activeStage_mono hut)) ξ ξ ≤
            Real.exp (18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (Q * R₀)) *
              ((u : ℝ) - u')) *
            (H.toHistory.stageMetric (H.toHistory.activeStage u) w).inner
              (A.point (H.toHistory.activeStage u) (H.toHistory.activeStage_mono hu'u)
                (H.toHistory.activeStage_mono hut)) ξ ξ := by
  have hstage := H.toHistory.activeStage_eq_of_forall_time_not_mem_Ioc hu'u hno
  have htrace : ∀ x ∈ U, Nonempty (BackwardPointTrace H.toHistory
      (H.toHistory.activeStage u') (H.toHistory.activeStage t)
      (H.toHistory.activeStage_mono (hu'u.trans hut)) x) := fun x hx => by
    obtain ⟨B⟩ := htraceU x hx
    exact ⟨B.restrictFirst hstage.ge (H.toHistory.activeStage_mono (hu'u.trans hut))⟩
  intro x hx
  obtain ⟨A, hscal, hall, hcross⟩ :=
    H.exists_backwardPointTrace_scalar_le_two_mul_of_backward_step hphi hpinch hu'u hut hlast
      hslabs hcurrent hfinal hQR hqcan hdepth U hU htrace x hx
  refine ⟨A, hscal, hall, hcross, ?_⟩
  intro s hs w hw ξ
  have hK : 0 ≤ 8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (Q * R₀) := by
    have := hphi.pos 0
    have := hphi.pos 1
    exact mul_nonneg (by positivity) (by linarith)
  have hbound : ∀ r ∈ Icc (u' : ℝ) u,
      normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage u) r)
          (A.point (H.toHistory.activeStage u) (H.toHistory.activeStage_mono hu'u)
            (H.toHistory.activeStage_mono hut)) 4
        (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage u) r)
          (A.point (H.toHistory.activeStage u) (H.toHistory.activeStage_mono hu'u)
            (H.toHistory.activeStage_mono hut))) ≤
        (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (Q * R₀)) ^ 2 := by
    intro r hr
    let v : Icc (0 : ℝ) H.toHistory.horizon := ⟨r, u'.2.1.trans hr.1, hr.2.trans u.2.2⟩
    have huv : u' ≤ v := hr.1
    have hvu : v ≤ u := hr.2
    have hvt : v ≤ t := hvu.trans hut
    have hav : H.toHistory.activeStage v = H.toHistory.activeStage u :=
      le_antisymm (H.toHistory.activeStage_mono hvu)
        (hstage.symm.le.trans (H.toHistory.activeStage_mono huv))
    have hb := hall v huv hvt
    rw [trace_normSq_eq_of_stage_eq' A hav (H.toHistory.activeStage_mono huv)
      (H.toHistory.activeStage_mono hvt) (H.toHistory.activeStage_mono hu'u)
      (H.toHistory.activeStage_mono hut)] at hb
    exact hb
  have hak : H.toHistory.time (H.toHistory.activeStage u) ≤ u' := by
    rw [← hstage]
    exact H.toHistory.activeStage_time_le u'
  have hd := H.toHistory.stageMetric_inner_le_exp_of_normSq_le (H.toHistory.activeStage u)
    (A.point (H.toHistory.activeStage u) (H.toHistory.activeStage_mono hu'u)
      (H.toHistory.activeStage_mono hut)) hak
    (fun i hi => H.time_lt_succ_of_activeStage_eq_castSucc u i hi) u.2.2 hbound hs hw ξ
  rw [Real.sqrt_sq hK] at hd
  have habs : |s - w| ≤ (u : ℝ) - u' :=
    abs_le.mpr ⟨by linarith [hs.1, hw.2], by linarith [hs.2, hw.1]⟩
  have hexp : Real.exp (18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (Q * R₀)) * |s - w|) ≤
      Real.exp (18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (Q * R₀)) * ((u : ℝ) - u')) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs (by linarith))
  exact hd.trans (mul_le_mul_of_nonneg_right hexp (metric_inner_self_nonneg _ _ _))

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

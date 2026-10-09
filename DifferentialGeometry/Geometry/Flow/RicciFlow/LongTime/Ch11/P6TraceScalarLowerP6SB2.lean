import DifferentialGeometry.Analysis.Calculus.Derivative.ClippedReciprocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceReciprocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPartition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStageMetric

/-!
# 沿 backward trace 的标量下界（bootstrap；O-CH11-SLICE-BCBD2 G7 / G1-C L1，后缀 `_P6SB2`）

树内 `BackwardTraceScalarControl/TimeLocal.lean` 只公开上界版
`scalar_le_two_mul_of_time_local_derivative_control`；其核心（clipped reciprocal `(max M R)⁻¹` 沿 trace 的
`Ctime`-Lipschitz，跨 surgery 经 crossing 标量相等）是 private。本文件逐字公开孪生该核心
（`lipschitzOnWith_inv_max_scalar_Icc_P6SB2`、`inv_max_scalar_sub_endpoint_le_on_time_window_P6SB2`、
`inv_max_scalar_sub_le_of_time_local_derivative_control_P6SB2`），并给出 G1-C 情形 (B) 需要的**下界**
`scalar_gt_of_time_local_derivative_control_P6SB2`：导数界只在天花板 `{R > M}` 上要求（= 先验供给），
端点 `R(t, y) > 2M`、`Ctime·R(t, y)·(t − a) ≤ 1/2` ⇒ 整段 trace `R > M`。
生成器 `build-logs/scratch/O-CH11-SLICE-BCBD2/gen/gen7.py`（TimeLocal 源切片 + assert 替换）。
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- clipped reciprocal 的 Lipschitz 性（TimeLocal 私有引理的公开孪生，`_P6SB2`）。 -/
theorem lipschitzOnWith_inv_max_scalar_Icc_P6SB2 {P : OrientedThreeStage.{u}}
    {D : RealTimeInterval} {S : SolutionOn (I := ThreeModel) (M := P.Carrier) D}
    (hS : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn S) {a b q : ℝ} {C : ℝ≥0}
    (hq : 0 < q) (hsub : Icc a b ⊆ D.carrier) (x : P.Carrier)
    (hbound : ∀ v ∈ Ioo a b, q < S.scalar v x →
      |derivWithin (fun w => S.scalar w x) (Iic v) v| ≤ C * S.scalar v x ^ 2) :
    LipschitzOnWith C (fun v => (max q (S.scalar v x))⁻¹) (Icc a b) := by
  apply DifferentialGeometry.Analysis.lipschitzOnWith_inv_max_of_quadratic_deriv_bound_Icc
    (r' := fun v => derivWithin (fun w => S.scalar w x) (Iic v) v) hq
  · intro v hv
    exact (hS.scalarTime hv hsub x).continuousWithinAt
  · intro v hv _
    have hd : DifferentiableAt ℝ (fun w => S.scalar w x) v :=
      (hS.scalarTime (K := Ioo a b) hv (Ioo_subset_Icc_self.trans hsub) x).differentiableAt
        (Ioo_mem_nhds hv.1 hv.2)
    rw [hd.derivWithin (uniqueDiffWithinAt_Iic v)]
    exact hd.hasDerivAt
  · exact hbound

namespace BackwardPointTrace

/-- 首段从实际 cut 时刻起算的 reciprocal 估计（TimeLocal 私有引理的公开孪生，`_P6SB2`）。 -/
theorem inv_max_scalar_sub_endpoint_le_on_time_window_P6SB2
    {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {endpoint : (H.stage last).Carrier} (A : BackwardPointTrace H first last hle endpoint)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {v : ℝ} (hv : v ∈ Ico (H.time i.castSucc) (H.time i.succ))
    (hbound : ∀ j : Fin H.eventCount, ∀ hfj : i.castSucc ≤ j.castSucc,
      ∀ hjl : j.succ ≤ last, ∀ s ∈ Ioo (H.time j.castSucc) (H.time j.succ), v ≤ s →
      q < (H.event j).incoming.flow.scalar s
        (A.point j.castSucc (hf.trans hfj) (j.castSucc_lt_succ.le.trans hjl)) →
      |derivWithin (fun w => (H.event j).incoming.flow.scalar w
        (A.point j.castSucc (hf.trans hfj) (j.castSucc_lt_succ.le.trans hjl))) (Iic s) s| ≤
        C * (H.event j).incoming.flow.scalar s
          (A.point j.castSucc (hf.trans hfj) (j.castSucc_lt_succ.le.trans hjl)) ^ 2) :
    |(max q ((H.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))))⁻¹ -
      (max q (metricScalarAt (H.initialMetric last) endpoint))⁻¹| ≤
        C * (H.time last - v) := by
  let B := A.restrictFirst (hf.trans i.castSucc_lt_succ.le) hl
  have htail := inv_max_scalar_sub_endpoint_le last i.succ hl endpoint B hq
    (fun j hj hjl s hs => hbound j (i.castSucc_lt_succ.le.trans hj) hjl s hs
      ((hv.2.le.trans (H.time_strictMono.monotone hj)).trans hs.1.le))
  have hcross := A.crossing i hf hl
  let p : (H.event i).incoming.terminalRegularOpen :=
    ⟨A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
      hcross.mem_terminalRegularRegion (H.event i)⟩
  have hstep := (H.event i).terminal.inv_max_scalar_sub_terminal_le_on_time_window
    (H.event i).incoming hq p hv.1 hv.2
    (fun s hs => hbound i le_rfl hl s ⟨hv.1.trans_lt hs.1, hs.2⟩ hs.1.le)
    (show v ∈ Ico v (H.time i.succ) from ⟨le_rfl, hv.2⟩)
  have heq := MetricCutCapEvent.RegularCrossing.scalar_eq (H.event i) (p := p) hcross
  rw [H.event_output i] at heq
  rw [heq] at hstep
  have htri := abs_sub_le
    ((max q ((H.event i).incoming.flow.scalar v p.val))⁻¹)
    ((max q (metricScalarAt (H.initialMetric i.succ)
      (A.point i.succ (hf.trans i.castSucc_lt_succ.le) hl)))⁻¹)
    ((max q (metricScalarAt (H.initialMetric last) endpoint))⁻¹)
  dsimp only [B, restrictFirst] at htail
  nlinarith

/-- **clipped reciprocal 沿 trace 的 Lipschitz 估计（`_P6SB2`，PROVED）**：TimeLocal
`scalar_le_two_mul_of_time_local_derivative_control` 证明中的中间结论 `hrec` 单独陈述——导数界只在
`{R > M}` 上要求，`|(max M R(v))⁻¹ − (max M R(t, y))⁻¹| ≤ C·(t − v)`（跨 surgery，crossing 处标量相等）。 -/
theorem inv_max_scalar_sub_le_of_time_local_derivative_control_P6SB2
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {y : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) y)
    {Ctime : ℝ≥0} {M : ℝ} (hM : 0 < M)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < H.horizon →
      M < metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) →
      |derivWithin (fun s => metricScalarAt (H.stageMetric (H.activeStage v) s)
        (A.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvt))) (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav)
            (H.activeStage_mono hvt)) ^ 2)
    :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      |(max M (metricScalarAt (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))))⁻¹ -
        (max M (metricScalarAt (H.stageMetric (H.activeStage t) t) y))⁻¹| ≤
        Ctime * ((t : ℝ) - v) := by
  have hstageBound (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
      (j : Fin (H.eventCount + 1)) (hj : H.activeStage v = j)
      (hfj : H.activeStage a ≤ j) (hjl : j ≤ H.activeStage t) :
      H.time j < (v : ℝ) → (v : ℝ) < H.horizon →
      M < metricScalarAt (H.stageMetric j v) (A.point j hfj hjl) →
      |derivWithin (fun s => metricScalarAt (H.stageMetric j s) (A.point j hfj hjl))
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt (H.stageMetric j v) (A.point j hfj hjl) ^ 2 := by
    subst j
    exact hbound v hav hvt
  have hvalue_eq (j k : Fin (H.eventCount + 1)) (hjk : j = k)
      (hfj : H.activeStage a ≤ j) (hjt : j ≤ H.activeStage t)
      (hfk : H.activeStage a ≤ k) (hkt : k ≤ H.activeStage t) (w : ℝ) :
      metricScalarAt (H.stageMetric j w) (A.point j hfj hjt) =
        metricScalarAt (H.stageMetric k w) (A.point k hfk hkt) := by
    subst k
    rfl
  let c : ℝ := max (a : ℝ) (H.time (H.activeStage t))
  have hac : (a : ℝ) ≤ c := le_max_left _ _
  have hbc : H.time (H.activeStage t) ≤ c := le_max_right _ _
  have hct : c ≤ (t : ℝ) := max_le hat (H.activeStage_time_le t)
  have hlip : LipschitzOnWith Ctime
      (fun w => (max M (metricScalarAt (H.stageMetric (H.activeStage t) w) y))⁻¹)
      (Icc c (t : ℝ)) := by
    by_cases hage : H.time (H.activeStage t) < (t : ℝ)
    · let G := H.closedPrefixAt t hage
      have hfun : (fun w => G.flow.scalar w y) =
          (fun w => metricScalarAt (H.stageMetric (H.activeStage t) w) y) := by
        funext w
        change metricScalarAt (G.flow.base.metric w) y = _
        rw [H.closedPrefixAt_metric]
      have hh := lipschitzOnWith_inv_max_scalar_Icc_P6SB2 G.equation hM
        (a := c) (b := (t : ℝ)) (fun w hw => ⟨hbc.trans hw.1, hw.2⟩) y
        (fun w hw hRw => by
          have haw : (a : ℝ) ≤ w := hac.trans hw.1.le
          let wI : Icc (0 : ℝ) H.horizon := ⟨w, a.2.1.trans haw, hw.2.le.trans t.2.2⟩
          have hactive : H.activeStage wI = H.activeStage t :=
            le_antisymm (H.activeStage_mono (show wI ≤ t from hw.2.le))
              (H.le_activeStage wI _ (hbc.trans hw.1.le))
          change M < (fun s => G.flow.scalar s y) w at hRw
          rw [hfun] at hRw
          have hb := hstageBound wI haw hw.2.le (H.activeStage t) hactive
            (H.activeStage_mono hat) le_rfl (hbc.trans_lt hw.1) (hw.2.trans_le t.2.2)
          have hd := hb (by simpa only [A.endpoint_eq] using hRw)
          change |derivWithin (fun s => G.flow.scalar s y) (Iic w) w| ≤
            Ctime * ((fun s => G.flow.scalar s y) w) ^ 2
          rw [hfun]
          simpa only [A.endpoint_eq] using hd)
      change LipschitzOnWith Ctime (fun w => (max M ((fun s => G.flow.scalar s y) w))⁻¹)
        (Icc c (t : ℝ)) at hh
      rw [hfun] at hh
      exact hh
    · have hzero : H.time (H.activeStage t) = (t : ℝ) :=
        le_antisymm (H.activeStage_time_le t) (not_lt.mp hage)
      have hc : c = (t : ℝ) := by dsimp [c]; rw [hzero]; exact max_eq_right hat
      rw [hc, Icc_self]
      intro u hu w hw
      have hu' : u = (t : ℝ) := mem_singleton_iff.mp hu
      have hw' : w = (t : ℝ) := mem_singleton_iff.mp hw
      subst u
      subst w
      simp only [edist_self, mul_zero, le_refl]
  intro v hav hvt
  have hrec :
      |(max M (metricScalarAt (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))))⁻¹ -
        (max M (metricScalarAt (H.stageMetric (H.activeStage t) t) y))⁻¹| ≤
        Ctime * ((t : ℝ) - v) := by
    rcases (H.activeStage_mono hvt).lt_or_eq with hlt | heq
    · have hjlast : H.activeStage v ≠ Fin.last H.eventCount :=
        ne_of_lt (hlt.trans_le (Fin.le_last _))
      obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hjlast
      have hf : H.activeStage a ≤ i.castSucc := by rw [hi]; exact H.activeStage_mono hav
      have hil : i.castSucc < H.activeStage t := by simpa only [hi] using hlt
      have hl : i.succ ≤ H.activeStage t := Fin.castSucc_lt_iff_succ_le.mp hil
      have hvdom : (v : ℝ) ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
        have hd := H.activeStage_mem v
        rw [← hi] at hd
        simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using hd
      have hstep := inv_max_scalar_sub_endpoint_le_on_time_window_P6SB2 A hM i hf hl hvdom
        (fun j hfj hjl w hw hvw hRw => by
          have haw : (a : ℝ) ≤ w := (show (a : ℝ) ≤ v from hav).trans hvw
          have hwt : w ≤ (t : ℝ) :=
            hw.2.le.trans ((H.time_strictMono.monotone hjl).trans (H.activeStage_time_le t))
          let wI : Icc (0 : ℝ) H.horizon := ⟨w, a.2.1.trans haw, hwt.trans t.2.2⟩
          have hactive : H.activeStage wI = j.castSucc :=
            (H.mem_stageDomain_iff wI j.castSucc).mp (by
              simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
                (show w ∈ Ico (H.time j.castSucc) (H.time j.succ) from ⟨hw.1.le, hw.2⟩))
          have hb := hstageBound wI haw hwt j.castSucc hactive (hf.trans hfj)
            (j.castSucc_lt_succ.le.trans hjl) hw.1
            (hw.2.trans_le (H.time_le_horizon_at j.succ))
          simp only [ObservedHistory.stageMetric_castSucc_apply] at hb
          exact hb hRw)
      have hab : (a : ℝ) ≤ H.time (H.activeStage t) :=
        (show (a : ℝ) ≤ v from hav).trans (hvdom.2.le.trans (H.time_strictMono.monotone hl))
      have hc : c = H.time (H.activeStage t) := max_eq_right hab
      have htop := hlip.dist_le_mul (H.time (H.activeStage t))
        ⟨hc.le, H.activeStage_time_le t⟩ (t : ℝ) ⟨hct, le_rfl⟩
      rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (H.time (H.activeStage t)) (t : ℝ),
        abs_of_nonneg (sub_nonneg.mpr (H.activeStage_time_le t))] at htop
      simp only [H.stageMetric_initial] at htop
      rw [hvalue_eq _ _ hi.symm (H.activeStage_mono hav) (H.activeStage_mono hvt)
        hf (i.castSucc_lt_succ.le.trans hl) v, ObservedHistory.stageMetric_castSucc_apply]
      have htri := abs_sub_le
        ((max M ((H.event i).incoming.flow.scalar v
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))))⁻¹)
        ((max M (metricScalarAt (H.initialMetric (H.activeStage t)) y))⁻¹)
        ((max M (metricScalarAt (H.stageMetric (H.activeStage t) t) y))⁻¹)
      change |(max M ((H.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))))⁻¹ - _| ≤ _
      nlinarith
    · have hvbirth : H.time (H.activeStage t) ≤ (v : ℝ) := by
        rw [← heq]
        exact H.activeStage_time_le v
      have hvc : c ≤ (v : ℝ) := max_le hav hvbirth
      have hh := hlip.dist_le_mul (v : ℝ) ⟨hvc, hvt⟩ (t : ℝ) ⟨hct, le_rfl⟩
      rw [hvalue_eq _ _ heq (H.activeStage_mono hav) (H.activeStage_mono hvt)
        (H.activeStage_mono hat) le_rfl v, A.endpoint_eq]
      simpa only [Real.dist_eq, abs_sub_comm (v : ℝ) (t : ℝ),
        abs_of_nonneg (sub_nonneg.mpr (show (v : ℝ) ≤ t from hvt))] using hh
  exact hrec

/-- **trace 上的标量下界（bootstrap，`_P6SB2`，PROVED）**：导数界只在 `{R > M}` 上要求；端点
`R(t, y) > 2M` 且 `Ctime·R(t, y)·(t − a) ≤ 1/2` ⇒ 整段 `[a, t]` 上 trace 点 `R > M`（实际
`(max M R(v))⁻¹ ≤ (3/2)/R(t, y)`）。 -/
theorem scalar_gt_of_time_local_derivative_control_P6SB2
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {y : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) y)
    {Ctime : ℝ≥0} {M : ℝ} (hM : 0 < M)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < H.horizon →
      M < metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) →
      |derivWithin (fun s => metricScalarAt (H.stageMetric (H.activeStage v) s)
        (A.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvt))) (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav)
            (H.activeStage_mono hvt)) ^ 2)
    (hend : 2 * M < metricScalarAt (H.stageMetric (H.activeStage t) t) y)
    (htime : Ctime * metricScalarAt (H.stageMetric (H.activeStage t) t) y * ((t : ℝ) - a) ≤
      1 / 2) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      M < metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) := by
  intro v hav hvt
  have hrec := inv_max_scalar_sub_le_of_time_local_derivative_control_P6SB2 hat A hM hbound v hav
    hvt
  generalize hRt : metricScalarAt (H.stageMetric (H.activeStage t) t) y = Rt at hrec hend htime
  generalize hRv : metricScalarAt (H.stageMetric (H.activeStage v) v)
    (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) = Rv at hrec ⊢
  have hRt0 : 0 < Rt := by linarith
  have hmaxt : max M Rt = Rt := max_eq_right (by linarith)
  rw [hmaxt] at hrec
  have hav' : (a : ℝ) ≤ v := hav
  have hvt' : (v : ℝ) ≤ t := hvt
  have hC : (Ctime : ℝ) * ((t : ℝ) - v) ≤ (2 * Rt)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Rt)]
    have h1 : (Ctime : ℝ) * ((t : ℝ) - v) * Rt ≤ Ctime * Rt * ((t : ℝ) - a) := by
      have hCt : 0 ≤ (Ctime : ℝ) * Rt := mul_nonneg Ctime.coe_nonneg hRt0.le
      nlinarith [Ctime.coe_nonneg]
    linarith
  by_contra hle
  push Not at hle
  have hmaxv : max M Rv = M := max_eq_left hle
  rw [hmaxv] at hrec
  have hup := (abs_le.mp hrec).2
  have h2 : M⁻¹ ≤ Rt⁻¹ + (2 * Rt)⁻¹ := by linarith
  have h3 : Rt⁻¹ + (2 * Rt)⁻¹ = 3 / (2 * Rt) := by field_simp; ring
  rw [h3] at h2
  have h4 : 2 * Rt ≤ 3 * M := by
    rw [inv_eq_one_div, div_le_div_iff₀ hM (by positivity)] at h2
    linarith
  linarith

end BackwardPointTrace

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

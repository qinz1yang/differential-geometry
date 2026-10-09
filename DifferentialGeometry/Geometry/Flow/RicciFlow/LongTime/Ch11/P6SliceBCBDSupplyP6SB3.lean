import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDSlabsCaseP6SB2

/-!
# 先验供给槽改前缀形：G8″ `hslabs_of_sepRho_prefixDt_P6SB3`（O-CH11-SLICE-BCBD3 G1，后缀 `_P6SB3`）

SLICE-BCBD2 G8 / G9 的先验供给槽 `EventSlabsDerivative Ctime′ (max (n+1) (ρs n (t n))⁻²) (Fin.last)`
阈值取 `t_n`、
范围却到 `Fin.last`：`ρ` 反单调 ⇒ `t_n` 之后的 slab 不被 `TimeDerivativeSupply_C11E` 覆盖（KSLABK 天花板事实），
该槽不是先验供给。G8 证明只在 `< t_n` 的时刻用导数界，故改为**前缀形**（HNOT G5 `prefixDt_rescale_seq_P6HN` 结论形，
KTRUNC 截断形同向）：
* `BackwardPointTrace.inv_max_scalar_sub_le_of_time_local_strict_P6SB3` /
  `…scalar_gt_of_time_local_strict_P6SB3`：
  SLICE-BCBD2 G7 的严格端点孪生（导数界只要 `v < t`）；
* `RetainedCoreHistory.hbound_of_prefixDt_P6SB3`：前缀 Dt ⇒ 严格端点逐点界；
* `RetainedCoreHistory.scalar_gt_of_prefixDt_P6SB3`：情形 (B) 排除（前缀形）；
* **`ObservedHistory.hslabs_of_sepRho_prefixDt_P6SB3`**（G8″）：结论 = G5 `hslabs` 槽逐字；前提 = G8 去
`hslabK`、
  加 `hpre1 / hpre2`（前缀形，阈值 `max (n+1) (ρs n (t n))⁻²`）。
`ρs` 换算：tower 帧 `K n = (F.tower.history (ind n)).rescale_P6N (c n)`、`ρ := q.neckRadius` 时取
`ρs n s := ρ (c n * s) / √(c n)`，则 `(ρs n s)⁻² = c n · (ρ (c n * s))⁻²` = HNOT G5 的 K 帧阈值 `Qp
n`（`s = t n`）；
`max (n+1) Qp ≥ Qp` ⇒ HNOT 前缀 Dt 经阈值单调（`derivativeBoundBefore_mono_qcan_P6SN`）付 `hpre1 /
hpre2`（G3 example）。
生成器 `build-logs/scratch/O-CH11-SLICE-BCBD3/gen/gen1.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace BackwardPointTrace

/-- **严格端点版（`_P6SB3`，PROVED）**：SLICE-BCBD2 G7 同名引理的孪生，导数界只在 `v < t`（不含端点）
且 `{R > M}` 上要求（TimeLocal 证明本来只用开区间内部）；`|(max M R(v))⁻¹ − (max M R(t, y))⁻¹| ≤ C·(t − v)`（跨
surgery，crossing 处标量相等）。 -/
theorem inv_max_scalar_sub_le_of_time_local_strict_P6SB3
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {y : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) y)
    {Ctime : ℝ≥0} {M : ℝ} (hM : 0 < M)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < t →
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
      H.time j < (v : ℝ) → (v : ℝ) < t →
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
            (H.activeStage_mono hat) le_rfl (hbc.trans_lt hw.1) hw.2
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
            (hw.2.trans_le ((H.time_strictMono.monotone hjl).trans
              (H.activeStage_time_le t)))
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

/-- **trace 上的标量下界，严格端点版（`_P6SB3`，PROVED）**：导数界只在 `v < t`、`{R > M}` 上要求；端点
`R(t, y) > 2M` 且 `Ctime·R(t, y)·(t − a) ≤ 1/2` ⇒ 整段 `[a, t]` 上 trace 点 `R > M`（实际
`(max M R(v))⁻¹ ≤ (3/2)/R(t, y)`）。 -/
theorem scalar_gt_of_time_local_strict_P6SB3
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {y : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) y)
    {Ctime : ℝ≥0} {M : ℝ} (hM : 0 < M)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < t →
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
  have hrec := inv_max_scalar_sub_le_of_time_local_strict_P6SB3 hat A hM hbound v hav
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

namespace RetainedCoreHistory

/-- **前缀 Dt ⇒ TimeLocal 严格端点型逐点导数界（`_P6SB3`，PROVED）**：`σ` 在 slab `j`（`activeStage σ = j⁻`），
前缀形供给 `EventSlabsDerivative C q j⁻` + `(event j).incoming.DerivativeBoundBefore C q σ` ⇒ 沿 `[a,
σ]` 的 trace
上 `v < σ`、`q < R` 处 `|∂R| ≤ C·R²`。 -/
theorem hbound_of_prefixDt_P6SB3 (K : RetainedCoreHistory.{u}) {C : ℝ≥0} {q : ℝ}
    (j : Fin K.eventCount) (σ : Icc (0 : ℝ) K.toHistory.horizon)
    (hact : K.toHistory.activeStage σ = j.castSucc)
    (hpre1 : K.EventSlabsDerivative C q j.castSucc)
    (hpre2 : (K.toHistory.event j).incoming.DerivativeBoundBefore C q σ)
    {a : Icc (0 : ℝ) K.toHistory.horizon} (hat : a ≤ σ) {y : (K.toHistory.stageAt σ).Carrier}
    (A : BackwardPointTrace K.toHistory (K.toHistory.activeStage a) (K.toHistory.activeStage σ)
      (K.toHistory.activeStage_mono hat) y) :
    ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ σ),
      K.toHistory.time (K.toHistory.activeStage v) < (v : ℝ) → (v : ℝ) < σ →
      q < metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
        (A.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
          (K.toHistory.activeStage_mono hvt)) →
      |derivWithin (fun s => metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) s)
        (A.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
          (K.toHistory.activeStage_mono hvt))) (Iic (v : ℝ)) v| ≤
        C * metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
          (A.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
            (K.toHistory.activeStage_mono hvt)) ^ 2 := by
  intro v hav hvt htv hvσ hq
  have hle : K.toHistory.activeStage v ≤ j.castSucc := hact ▸ K.toHistory.activeStage_mono hvt
  have hlt : K.toHistory.activeStage v < Fin.last K.eventCount :=
    lt_of_le_of_lt hle (Fin.castSucc_lt_last j)
  obtain ⟨e, he⟩ := Fin.exists_castSucc_eq.mpr (ne_of_lt hlt)
  have hvlt : (K.toHistory.activeStage v).val < K.eventCount := by
    rw [← he]
    exact e.isLt
  have hnext := K.toHistory.activeStage_before_next v hvlt
  have hfin : (⟨(K.toHistory.activeStage v).val + 1, by omega⟩ : Fin (K.eventCount + 1)) =
      e.succ := by
    apply Fin.ext
    change (K.toHistory.activeStage v).val + 1 = e.succ.val
    rw [Fin.val_succ, ← he, Fin.val_castSucc]
  have hv2 : (v : ℝ) < K.toHistory.time e.succ :=
    hnext.trans_eq (congrArg K.toHistory.time hfin)
  have hDB : (K.toHistory.event e).incoming.DerivativeBoundBefore C q (K.toHistory.time e.succ) ∨
      (e = j ∧ (K.toHistory.event e).incoming.DerivativeBoundBefore C q σ) := by
    rcases lt_or_eq_of_le (show e.castSucc ≤ j.castSucc from he ▸ hle) with h | h
    · exact Or.inl (hpre1 e h)
    · have hej : e = j := Fin.castSucc_injective _ h
      subst hej
      exact Or.inr ⟨rfl, hpre2⟩
  have hgen : ∀ (m : Fin (K.eventCount + 1)) (hm : e.castSucc = m)
      (h1 : K.toHistory.activeStage a ≤ m) (h2 : m ≤ K.toHistory.activeStage σ),
      K.toHistory.time m < (v : ℝ) →
      q < metricScalarAt (K.toHistory.stageMetric m v) (A.point m h1 h2) →
      |derivWithin (fun s => metricScalarAt (K.toHistory.stageMetric m s) (A.point m h1 h2))
          (Iic (v : ℝ)) v| ≤
        C * metricScalarAt (K.toHistory.stageMetric m v) (A.point m h1 h2) ^ 2 := by
    intro m hm h1 h2 htm hqm
    subst hm
    simp only [ObservedHistory.stageMetric_castSucc_apply] at hqm ⊢
    rcases hDB with hD | ⟨_, hD⟩
    · exact hD _ v ⟨htm, hv2⟩ hqm
    · exact hD _ v ⟨htm, hvσ⟩ hqm
  exact hgen _ he _ _ htv hq

/-- **情形 (B) 排除，前缀形供给（`_P6SB3`，PROVED）**：前缀 Dt（`EventSlabsDerivative C Q j⁻` + 当前 slab 到 `σ`）+ 端点
`R(σ, z) > 2Q` +
`Ctime·R(σ, z)·(σ − v′) ≤ 1/2` ⇒ prefix trace 点 `R(v′, x) > Q`。 -/
theorem scalar_gt_of_prefixDt_P6SB3 (K : RetainedCoreHistory.{u}) {C : ℝ≥0} {Q : ℝ}
    (hQ : 0 < Q) (j : Fin K.eventCount) (hpre1 : K.EventSlabsDerivative C Q j.castSucc)
    (σ : Icc (0 : ℝ) K.toHistory.horizon)
    (hpre2 : (K.toHistory.event j).incoming.DerivativeBoundBefore C Q σ)
    (hact : K.toHistory.activeStage σ = j.castSucc)
    (i : Fin (K.prefixAt j.castSucc).eventCount)
    (first : Fin ((K.prefixAt j.castSucc).eventCount + 1)) (hf : first ≤ i.castSucc)
    (z : (K.stage j.castSucc).Carrier)
    (Btr : BackwardPointTrace (K.prefixAt j.castSucc).toHistory first
      (Fin.last (K.prefixAt j.castSucc).eventCount) (Fin.le_last first) z)
    (v' : Icc (0 : ℝ) K.toHistory.horizon) (hv1 : (K.prefixAt j.castSucc).time i.castSucc < v')
    (hv2 : (v' : ℝ) < (K.prefixAt j.castSucc).time i.succ) (hvs : v' ≤ σ)
    (hend : 2 * Q < (K.toHistory.event j).incoming.flow.scalar σ z)
    (htime : C * (K.toHistory.event j).incoming.flow.scalar σ z * ((σ : ℝ) - v') ≤ 1 / 2) :
    Q < ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar v'
      (Btr.point i.castSucc hf (Fin.le_last _)) := by
  obtain ⟨z', A, hz', hAx⟩ := K.exists_historyTrace_of_prefix_P6SB2 j σ hact i first hf z Btr v'
    hv1 hv2 hvs
  have hsc := K.scalar_of_incoming_P6JG3H j hact.symm (σ : ℝ) z z' hz'
  have hlow := BackwardPointTrace.scalar_gt_of_time_local_strict_P6SB3 hvs A hQ
    (K.hbound_of_prefixDt_P6SB3 j σ hact hpre1 hpre2 hvs A) (by rw [hsc]; exact hend)
    (by rw [hsc]; exact htime) v' le_rfl hvs
  let e : Fin K.eventCount := Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i
  have hvact : K.toHistory.activeStage v' = e.castSucc :=
    K.activeStage_eq_of_mem_slab_P6JG3H e v' hv1.le hv2
  have hsc2 := K.scalar_of_incoming_P6JG3H e hvact.symm v'
    (Btr.point i.castSucc hf (Fin.le_last _)) _ hAx
  rw [hsc2] at hlow
  exact hlow

end RetainedCoreHistory

namespace ObservedHistory

/-- **G8″：G5 `hslabs` 槽 ⇐ (SEP-ρ⁺) + 前缀形先验供给（`_P6SB3`，PROVISIONAL[(SEP-ρ⁺)、前缀 Dt]）**：
SLICE-BCBD2 G8 的孪生，先验供给槽由全 `Fin.last` 形换成**前缀形**（`EventSlabsDerivative … (j n)⁻` + 当前 slab 到
`t n`；= HNOT G5 `prefixDt_rescale_seq_P6HN` 结论形，阈值 `max (n+1) (ρs n (t n))⁻²`，`ρs n s := ρ(c
n·s)/√(c n)` 时
`ρs⁻² = c·ρ(c·s)⁻²` 即 HNOT 的 `Qp`）。结论 = SLTPROD G1 `hslabsLoc_cstar_of_hgood_P6SP` 结论逐字（= G5 内
`hslabs`
类型）。三情形 (A)/(B)/(C) 见模块注释；前提无 `hprotC`，X-records 族只留 `hOldX`。 -/
theorem hslabs_of_sepRho_prefixDt_P6SB3 {eps C1' C2' : ℝ}
    {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (hCg : 1 ≤ Cg) {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hR1 : ∀ n, 1 ≤ R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (K n).eventCount), T₀X n ≤ (K n).toHistory.time e.succ →
      ((K n).toHistory.event e).old = ((K n).toHistory.event e).transition.trace.retainedCore)
    (hdσ : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) ≠ ⊤)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (ρs : ℕ → ℝ → ℝ) {θ₀ : ℝ}
    (hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ ≤
          ((recordsK n i hi).static b).neck.scale)
    (hpre1 : ∀ n, (K n).EventSlabsDerivative Ctime' (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹)
      (j n).castSucc)
    (hpre2 : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore Ctime'
      (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹) (t n)) :
    ∀ Rad B : ℝ, ∀ᶠ n in atTop,
      ∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
      ∀ (first : Fin (((K n).prefixAt (j n).castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      ∀ Btr : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory first
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) (Fin.le_last first) z,
      ∀ v ∈ Ioo (((K n).prefixAt (j n).castSucc).time i.castSucc)
        (((K n).prefixAt (j n).castSucc).time i.succ),
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
      (t n - v) * max (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) ≤
        1 / (2 * max (Ctime' : ℝ) 1) →
      Cg * R n < (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
        (Btr.point i.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w =>
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar w
            (Btr.point i.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime' * (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
          (Btr.point i.castSucc hf (Fin.le_last _)) ^ 2 := by
  obtain ⟨ε₀, hε₀, hnc0⟩ := exists_hnc_of_records_P6SB2.{u}
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min (min (r / 50) (localPropagationRadius C2' / 2))
      (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4)))) := ⟨_, rfl⟩
  have hρ : 0 < localPropagationRadius C2' := localPropagationRadius_pos hC2
  have hm1 : (1 : ℝ) ≤ max (Ctime' : ℝ) 1 := le_max_right _ _
  have hc0 : (0 : ℝ) ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by positivity
  have hc1 : 1 / (2 * max (Ctime' : ℝ) 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hCc : (Ctime' : ℝ) * (1 / (2 * max (Ctime' : ℝ) 1)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [le_max_left (Ctime' : ℝ) 1]
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  intro Rad B
  filter_upwards [hL.eventually_ge_atTop (max (max (4 * localPropagationRadius C2')
    (2 * (Rad + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κ) + 2)) 1), hwin 1 one_pos,
    hT₀ (max B 1), hsepρ (max B 1) (by positivity),
    hnat.eventually_gt_atTop (StandardCap.transitionEnd + 10), hnat.eventually_ge_atTop 9,
    hnat.eventually_ge_atTop (6 / r ^ 2 + 1),
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (ge_mem_nhds (lt_min hε₀ (by norm_num : (0 : ℝ) < 1 / 2)))]
    with n hLn hwn hT₀n hsepn hTEn h9 hr6 hacn
  intro i first hf z hz Btr v hv hBv hguard hq
  have hR0 := hR n
  have hQ1 : (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ := le_max_left _ _
  have hQ0 : 0 < max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ :=
    lt_of_lt_of_le (Nat.cast_add_one_pos n) hQ1
  have hL4 : 4 * localPropagationRadius C2' ≤ L n :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hLn
  have hL5 : 2 * (Rad + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κ) + 2 ≤ L n :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hLn
  have hL6 : (1 : ℝ) ≤ L n := (le_max_right _ _).trans hLn
  have hlast : ((K n).prefixAt (j n).castSucc).time i.succ ≤ (K n).time (j n).castSucc :=
    (((K n).prefixAt (j n).castSucc).time_strictMono.monotone (Fin.le_last _)).trans_eq
      ((K n).prefixAt_time_last _)
  have hvt : v < t n := hv.2.trans_le (hlast.trans (hjt n).le)
  have htv0 : 0 ≤ t n - v := sub_nonneg.mpr hvt.le
  have hRle : (t n - v) * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by
    have h3 := mul_le_mul_of_nonneg_left ((le_mul_of_one_le_left hR0.le hCg).trans
      (le_max_left (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z)))
      htv0
    exact h3.trans hguard
  have hTv : t n - v ≤ 1 / R n := by
    rw [le_div_iff₀ hR0]
    exact hRle.trans hc1
  have hBR : t n - max B 1 / R n ≤ v := by
    have hBv' : t n - B / R n ≤ v := by rw [hRn n]; exact hBv
    have : B / R n ≤ max B 1 / R n := div_le_div_of_nonneg_right (le_max_left _ _) hR0.le
    linarith only [hBv', this]
  have hv0 : 0 ≤ v := (((K n).prefixAt (j n).castSucc).toHistory.time_nonneg _).trans hv.1.le
  have hvH : v ≤ (K n).toHistory.horizon :=
    (hvt.trans (htj n)).le.trans ((K n).toHistory.time_le_horizon_at (j n).succ)
  let v' : Icc (0 : ℝ) (K n).toHistory.horizon := ⟨v, hv0, hvH⟩
  have hav : aSeed n ≤ v' :=
    hwn.trans (show (σ n : ℝ) - 1 / R n ≤ v by rw [hσ n]; linarith only [hTv])
  have hav' : (aSeed n : ℝ) ≤ v := hav
  have hvs : v' ≤ σ n := show v ≤ (σ n : ℝ) by rw [hσ n]; exact hvt.le
  have hLv : (σ n : ℝ) - L n ^ 2 / R n ≤ (v' : ℝ) := by
    have : 1 / R n ≤ L n ^ 2 / R n :=
      div_le_div_of_nonneg_right (by nlinarith only [hL6]) hR0.le
    change (σ n : ℝ) - L n ^ 2 / R n ≤ v
    rw [hσ n]
    linarith only [this, hTv]
  have hact : (K n).toHistory.activeStage (σ n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6JG3H (j n) (σ n) (by rw [hσ n]; exact (hjt n).le)
      (by rw [hσ n]; exact htj n)
  by_cases hA : max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ <
      (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
        (Btr.point i.castSucc hf (Fin.le_last _))
  · -- (A) 天花板以上：先验供给逐点
    have hilt : (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i).castSucc <
        (j n).castSucc := by
      rw [Fin.lt_def]
      exact i.isLt
    exact hpre1 n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i) hilt _ v ⟨hv.1, hv.2⟩ hA
  · push Not at hA
    by_cases hB : 2 * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ <
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z
    · -- (B) 不可能：trace 下界
      exfalso
      have hRz : (t n - v) * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          1 / (2 * max (Ctime' : ℝ) 1) :=
        (mul_le_mul_of_nonneg_left (le_max_right _ _) htv0).trans hguard
      have htime : (Ctime' : ℝ) * ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) z *
          ((σ n : ℝ) - v') ≤ 1 / 2 := by
        change (Ctime' : ℝ) * ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) z *
          ((σ n : ℝ) - v) ≤ 1 / 2
        rw [hσ n]
        have h1 := mul_le_mul_of_nonneg_left hRz Ctime'.coe_nonneg
        calc (Ctime' : ℝ) * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z * (t n - v)
            = (Ctime' : ℝ) * ((t n - v) *
              ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) := by ring
          _ ≤ 1 / 2 := h1.trans hCc
      have hpre2σ : ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore Ctime'
          (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹) (σ n) := by
        rw [hσ n]
        exact hpre2 n
      have hgt := (K n).scalar_gt_of_prefixDt_P6SB3 hQ0 (j n) (hpre1 n) (σ n) hpre2σ hact i first hf
        z Btr v' hv.1 hv.2 hvs (by rw [hσ n]; exact hB) htime
      exact absurd hgt (not_lt.mpr hA)
    · -- (C) 天花板以下：CXJD stay（保护由 guarded producer + (SEP-ρ⁺) 付）+ hgood
      push Not at hB
      obtain ⟨Qb, hQbdef⟩ : ∃ Qb : ℝ, Qb = max (max
          (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z / R n) Cg) 1 := ⟨_, rfl⟩
      obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 1 / (2 * max (Ctime' : ℝ) 1) / Qb := ⟨_, rfl⟩
      have hQb1 : (1 : ℝ) ≤ Qb := by rw [hQbdef]; exact le_max_right _ _
      have hQbpos : 0 < Qb := lt_of_lt_of_le one_pos hQb1
      have hQbM : Qb * R n ≤
          max (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) := by
        have hCgR : R n ≤ Cg * R n := le_mul_of_one_le_left hR0.le hCg
        have hle : Qb ≤ max (Cg * R n)
            (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) / R n := by
          rw [hQbdef]
          refine max_le (max_le ?_ ?_) ?_
          · exact div_le_div_of_nonneg_right (le_max_right _ _) hR0.le
          · rw [le_div_iff₀ hR0]
            exact le_max_left _ _
          · rw [le_div_iff₀ hR0, one_mul]
            exact hCgR.trans (le_max_left _ _)
        calc Qb * R n ≤ max (Cg * R n)
              (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) / R n * R n :=
            mul_le_mul_of_nonneg_right hle hR0.le
          _ = _ := div_mul_cancel₀ _ hR0.ne'
      have hQbQ : Qb * R n ≤ 2 * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ :=
        hQbM.trans (max_le (by linarith only [hq, hA, hQ0]) hB)
      have hT₀v : T₀ n ≤ (v' : ℝ) := hT₀n.trans (show (σ n : ℝ) - max B 1 / R n ≤ v by
        rw [hσ n]; exact hBR)
      have hacc1 : (p n).modelAccuracy ≤ min ε₀ (1 / 2) := (hacc n).trans hacn
      have hDm' : StandardCap.transitionEnd + 10 < (p n).modelRadius := by
        linarith only [hrad n, hTEn]
      have hncK := hnc0 (H := (K n).toHistory) (q := p n) (T₀ := T₀ n) (recordsK n)
        (hacc1.trans (min_le_left _ _)) (le_trans (by omega) (hord n)) (hcanK n)
      have hscaleK : ∀ (e : Fin (K n).eventCount) (he : T₀ n ≤ (K n).time e.succ) b,
          (v' : ℝ) < (K n).toHistory.time e.succ →
          e.succ ≤ (K n).toHistory.activeStage (σ n) →
          2 * max (3 / r ^ 2) (2 * (Qb * R n)) < ((recordsK n e he).static b).neck.scale := by
        intro e he b' hve he4
        have hej : e.succ ≤ (j n).castSucc := hact ▸ he4
        have hwin' : t n - max B 1 / R n ≤ (K n).time e.succ := hBR.trans hve.le
        have hS := hsepn e he b' hej (Or.inl hwin')
        have h8 : 8 * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ <
            ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ := by nlinarith only [h9, hQ0]
        have hn1 : (1 : ℝ) ≤ max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ :=
          le_trans (by linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hQ1
        have hnQ : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ :=
          le_mul_of_one_le_right (Nat.cast_add_one_pos n).le hn1
        have h6 : 6 / r ^ 2 < ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ := by
          linarith only [hnQ, hr6]
        have h63 : 2 * (3 / r ^ 2) = 6 / r ^ 2 := by ring
        have hmx : max (3 / r ^ 2) (2 * (Qb * R n)) <
            ((recordsK n e he).static b').neck.scale / 2 :=
          max_lt (by linarith only [h6, hS, h63]) (by linarith only [hQbQ, h8, hS])
        linarith only [hmx]
      have hL0 : 0 ≤ L n := le_trans zero_le_one hL6
      have hRa' : 1 ≤ R n * v' := by
        have := mul_le_mul_of_nonneg_left hav' hR0.le
        change 1 ≤ R n * v
        linarith only [this, hRa n]
      have hz' := hz
      rw [← hRn n] at hz'
      obtain ⟨hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hnum⟩ := cstar_numerics_P6SP (Qb := Qb) (R := R n)
        (Rad := Rad) (L := L n) hr hρ hc0 hQb1 (hR1 n) hκdef (by linarith only [hL4])
        (by linarith only [hL5])
      have hTeq : T / R n = 1 / (2 * max (Ctime' : ℝ) 1) / Qb / R n := by rw [hTdef]
      rw [← hTeq] at hnum
      have hstay := stay_cstar_prefix_sepRho_P6SB2 hC2 hCg (K n) (j n) (hjt n) (htj n) (hσ n)
        (haT n) (hsmall n) (hclock n) (seedTrace n) (ha₀ n) (hpin n) (hsT n) (has n) (y n) (yG n)
        (hyG n) (L n) hR0 (hgood n) i first hf z hz' Btr v' hv.1 hv.2 hav hvs hLv hRa' hQbdef hTdef
        hguard hℓ hKℓ hℓr hKr hKC hℓρ hρL ((hT₀X n).trans hav') (hOldX n) (recordsK n) hT₀v
        (hcanK n) (hacc1.trans (min_le_right _ _)) hDm' hncK hscaleK hL0 (hdσ n) hnum
      exact ObservedHistory.slabDeriv_prefix_of_hgood_stay_P6SP (K n) (j n).castSucc (haT n) (hsT n)
        (has n) (seedTrace n) (y n) (R n) (L n) (hgood n) i
        (Btr.point i.castSucc hf (Fin.le_last _)) v' hav hvs hv.1 hv.2 hLv hstay hq

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BackwardTraceScalarControl_P6L

/-!
# G1 footprint 时间窗改形（`_P6L′`）：`BackwardTraceScalarControl:105/168` 的 `[u, t]` 窗口形（`_P6N`）

rev1 §R2 改形标记 / P6A3 HANDOVER [V]：`BTSC:105_P6L` 的 `hslabs` 按整段 event slab
`Ioo (time i.castSucc) (time i.succ)` 求值，但 Lipschitz 论证只用 `[v, time i.succ] ⊆ [u, t]`
（`BackwardTraceScalarTime:16` 内部经 `inv_max_scalar_sub_terminal_le` 用整段；改走树内
`TerminalLimitMetric.inv_max_scalar_sub_terminal_le_on_time_window`，同
`BackwardTraceScalarControl/TimeLocal` 的 private 引理）。本文件把 `hslabs` / `hcurrent` / `hfinal`
三个 footprint 前提都加窗口 guard `a ≤ v`（`a` = 窗口起点，`168′` 中 `a = u`）：
* `hslabs`：`∀ v ∈ Ioo (time i.castSucc) (time i.succ), a ≤ v → …`（⇔ `v ∈ Ioo (max … a) …`）；
* `hcurrent` / `hfinal`：`∀ v ∈ Ioo (time k) t, a ≤ v → …`。
无具名新 Prop；结论与 `_P6L` 逐字。consumer：全 slab 形（`_P6L` 前提）⇒ 窗口形（丢 guard）。
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem le_two_mul_of_abs_inv_max_sub_le_P6N {M R Rt Δ : ℝ} {C : ℝ≥0} (hM : 0 < M)
    (hRt : Rt ≤ M) (hrec : |(max M R)⁻¹ - (max M Rt)⁻¹| ≤ C * Δ)
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

private theorem lipschitzOnWith_inv_max_scalar_Icc_P6N {P : OrientedThreeStage.{u}}
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

variable {K : ObservedHistory.{u}}

/-- 树内 `BackwardTraceScalarControl/TimeLocal` 的 private
`inv_max_scalar_sub_endpoint_le_on_time_window` 的副本：首段从实际时刻 `v` 起，后续段整段
（均在 `[v, time last]` 内）。 -/
theorem inv_max_scalar_sub_endpoint_le_on_time_window_P6N
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

/-- 当前 stage 的 Lipschitz 段，取任意起点 `c ∈ [max (time k) a, t]`（窗口形 `hcurrent`/`hfinal`）。 -/
private theorem lipschitzOnWith_inv_max_stageMetric_scalar_window_P6N
    (k : Fin (K.eventCount + 1)) (x : (K.stage k).Carrier) {Ctime : ℝ≥0} {qcan q t a c : ℝ}
    (hq : 0 < q) (hqcan : qcan ≤ q) (hkc : K.time k ≤ c) (hac : a ≤ c)
    (hnext : ∀ i : Fin K.eventCount, k = i.castSucc → t < K.time i.succ) (ht : t ≤ K.horizon)
    (hcurrent : ∀ i : Fin K.eventCount, ∀ y : (K.stage i.castSucc).Carrier,
      i.castSucc = k → HEq y x → ∀ v ∈ Ioo (K.time i.castSucc) t, a ≤ v →
      qcan < (K.event i).incoming.flow.scalar v y →
      |derivWithin (fun w => (K.event i).incoming.flow.scalar w y) (Iic v) v| ≤
        Ctime * (K.event i).incoming.flow.scalar v y ^ 2)
    (hfinal : ∀ h : K.time (Fin.last K.eventCount) < K.horizon,
      ∀ y : (K.stage (Fin.last K.eventCount)).Carrier, k = Fin.last K.eventCount → HEq y x →
      ∀ v ∈ Ioo (K.time (Fin.last K.eventCount)) t, a ≤ v →
      qcan < ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y →
      |derivWithin (fun w => ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar w y)
        (Iic v) v| ≤
        Ctime * ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y ^ 2) :
    LipschitzOnWith Ctime (fun v => (max q (metricScalarAt (K.stageMetric k v) x))⁻¹)
      (Icc c t) := by
  cases k using Fin.lastCases with
  | last =>
    by_cases h : K.time (Fin.last K.eventCount) < K.horizon
    · simp only [ObservedHistory.stageMetric_last_of_lt (h := h)]
      exact lipschitzOnWith_inv_max_scalar_Icc_P6N (K.finalSlab h).equation hq
        (fun _ hv => ⟨hkc.trans hv.1, hv.2.trans ht⟩) x
        (fun v hv hR => hfinal h x rfl HEq.rfl v ⟨hkc.trans_lt hv.1, hv.2⟩ (hac.trans hv.1.le)
          (hqcan.trans_lt hR))
    · simp only [ObservedHistory.stageMetric_last_of_le (not_lt.mp h)]
      exact (LipschitzWith.const _).lipschitzOnWith.weaken zero_le
  | cast i =>
    simp only [ObservedHistory.stageMetric_castSucc_apply]
    exact lipschitzOnWith_inv_max_scalar_Icc_P6N (K.event i).incoming.equation hq
      (fun _ hv => ⟨hkc.trans hv.1, hv.2.trans_lt (hnext i rfl)⟩) x
      (fun v hv hR => hcurrent i x rfl HEq.rfl v ⟨hkc.trans_lt hv.1, hv.2⟩ (hac.trans hv.1.le)
        (hqcan.trans_lt hR))

/-- **`_P6N`（`BTSC:105` 窗口形）**：`_P6L` 版的 `hslabs`/`hcurrent`/`hfinal` 加窗口 guard `a ≤ v`
（`a ≤ v₀`，`v₀` 为求值时刻）。结论与 `_P6L` 逐字。 -/
theorem inv_max_stageMetric_scalar_sub_le_of_derivativeBoundBefore_window_P6N
    {first k : Fin (K.eventCount + 1)} {hle : first ≤ k} {x : (K.stage k).Carrier}
    (A : BackwardPointTrace K first k hle x) {Ctime : ℝ≥0} {qcan q t a : ℝ}
    (hq : 0 < q) (hqcan : qcan ≤ q) (htk : K.time k ≤ t)
    (hnext : ∀ i : Fin K.eventCount, k = i.castSucc → t < K.time i.succ) (ht : t ≤ K.horizon)
    (hslabs : ∀ i : Fin K.eventCount, ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ k,
      ∀ v ∈ Ioo (K.time i.castSucc) (K.time i.succ), a ≤ v →
      qcan < (K.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun w => (K.event i).incoming.flow.scalar w
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic v) v| ≤
        Ctime * (K.event i).incoming.flow.scalar v
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hcurrent : ∀ i : Fin K.eventCount, ∀ y : (K.stage i.castSucc).Carrier,
      i.castSucc = k → HEq y x → ∀ v ∈ Ioo (K.time i.castSucc) t, a ≤ v →
      qcan < (K.event i).incoming.flow.scalar v y →
      |derivWithin (fun w => (K.event i).incoming.flow.scalar w y) (Iic v) v| ≤
        Ctime * (K.event i).incoming.flow.scalar v y ^ 2)
    (hfinal : ∀ h : K.time (Fin.last K.eventCount) < K.horizon,
      ∀ y : (K.stage (Fin.last K.eventCount)).Carrier, k = Fin.last K.eventCount → HEq y x →
      ∀ v ∈ Ioo (K.time (Fin.last K.eventCount)) t, a ≤ v →
      qcan < ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y →
      |derivWithin (fun w => ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar w y)
        (Iic v) v| ≤
        Ctime * ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y ^ 2)
    (j : Fin (K.eventCount + 1)) (hfj : first ≤ j) (hjk : j ≤ k) {v : ℝ}
    (hjv : K.time j ≤ v) (hvnext : ∀ i : Fin K.eventCount, j = i.castSucc → v < K.time i.succ)
    (hvt : v ≤ t) (hav : a ≤ v) :
    |(max q (metricScalarAt (K.stageMetric j v) (A.point j hfj hjk)))⁻¹ -
      (max q (metricScalarAt (K.stageMetric k t) x))⁻¹| ≤ Ctime * (t - v) := by
  rcases hjk.lt_or_eq with hlt | heq
  · have hjl : j ≠ Fin.last K.eventCount := ne_of_lt (hlt.trans_le (Fin.le_last k))
    obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hjl
    have hsucc : j'.succ ≤ k := Fin.castSucc_lt_iff_succ_le.mp hlt
    have hvk : v < K.time k :=
      (hvnext j' rfl).trans_le (K.time_strictMono.monotone hsucc)
    have hstep := A.inv_max_scalar_sub_endpoint_le_on_time_window_P6N hq j' hfj hsucc
      ⟨hjv, hvnext j' rfl⟩
      (fun i hfi hil w hw hvw hR => hslabs i (hfj.trans hfi) hil w hw (hav.trans hvw)
        (hqcan.trans_lt hR))
    have hlip := lipschitzOnWith_inv_max_stageMetric_scalar_window_P6N k x hq hqcan le_rfl
      (hav.trans hvk.le) hnext ht hcurrent hfinal
    have htop := hlip.dist_le_mul (K.time k) ⟨le_rfl, htk⟩ t ⟨htk, le_rfl⟩
    rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (K.time k) t,
      abs_of_nonneg (sub_nonneg.mpr htk)] at htop
    simp only [K.stageMetric_initial] at htop
    rw [ObservedHistory.stageMetric_castSucc_apply]
    have htri := abs_sub_le
      ((max q ((K.event j').incoming.flow.scalar v (A.point j'.castSucc hfj hjk)))⁻¹)
      ((max q (metricScalarAt (K.initialMetric k) x))⁻¹)
      ((max q (metricScalarAt (K.stageMetric k t) x))⁻¹)
    change |(max q ((K.event j').incoming.flow.scalar v (A.point j'.castSucc hfj hjk)))⁻¹ -
      (max q (metricScalarAt (K.stageMetric k t) x))⁻¹| ≤ _
    nlinarith
  · subst heq
    have hpt : A.point j hfj hjk = x := A.endpoint_eq
    rw [hpt]
    have hlip := lipschitzOnWith_inv_max_stageMetric_scalar_window_P6N j x hq hqcan hjv hav
      hnext ht hcurrent hfinal
    have hd := hlip.dist_le_mul v ⟨le_rfl, hvt⟩ t ⟨hvt, le_rfl⟩
    rwa [Real.dist_eq, Real.dist_eq, abs_sub_comm v t,
      abs_of_nonneg (sub_nonneg.mpr hvt)] at hd

end BackwardPointTrace

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

private theorem lt_time_succ_of_activeStage_eq_P6N (t : Icc (0 : ℝ) H.toHistory.horizon)
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

/-- **`_P6N`（`BTSC:168` 窗口形）**：`_P6L` 版的三个 footprint 前提只在时间窗 `[u, t]` 内要
（guard `(u : ℝ) ≤ v`）。结论与 `_P6L` 逐字。 -/
theorem scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds_window_P6N
    {Ctime : ℝ≥0} {qcan M : ℝ} {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    {p : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) p)
    (hslabs : ∀ i : Fin H.toHistory.eventCount, ∀ hf : H.toHistory.activeStage u ≤ i.castSucc,
      ∀ hl : i.succ ≤ H.toHistory.activeStage t,
      ∀ v ∈ Ioo (H.toHistory.time i.castSucc) (H.toHistory.time i.succ), (u : ℝ) ≤ v →
      qcan < (H.toHistory.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun w => (H.toHistory.event i).incoming.flow.scalar w
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic v) v| ≤
        Ctime * (H.toHistory.event i).incoming.flow.scalar v
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hcurrent : ∀ j : Fin H.toHistory.eventCount, ∀ y : (H.toHistory.stage j.castSucc).Carrier,
      j.castSucc = H.toHistory.activeStage t → HEq y p →
      ∀ v ∈ Ioo (H.toHistory.time j.castSucc) t, (u : ℝ) ≤ v →
      qcan < (H.toHistory.event j).incoming.flow.scalar v y →
      |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w y) (Iic v) v| ≤
        Ctime * (H.toHistory.event j).incoming.flow.scalar v y ^ 2)
    (hfinal : ∀ h : H.toHistory.time (Fin.last H.toHistory.eventCount) < H.toHistory.horizon,
      ∀ y : (H.toHistory.stage (Fin.last H.toHistory.eventCount)).Carrier,
      H.toHistory.activeStage t = Fin.last H.toHistory.eventCount → HEq y p →
      ∀ v ∈ Ioo (H.toHistory.time (Fin.last H.toHistory.eventCount)) t, (u : ℝ) ≤ v →
      qcan < ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y →
      |derivWithin (fun w =>
        ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar w y) (Iic v) v| ≤
        Ctime * ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y ^ 2)
    (hM : 0 < M) (hqcan : qcan ≤ M)
    (hscalar : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2) :
    ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u ≤ v) (hvt : v ≤ t),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
          (H.toHistory.activeStage_mono hvt)) ≤ 2 * M := by
  intro v huv hvt
  have hrec := A.inv_max_stageMetric_scalar_sub_le_of_derivativeBoundBefore_window_P6N hM hqcan
    (H.toHistory.activeStage_time_le t)
    (fun i hi => H.lt_time_succ_of_activeStage_eq_P6N t i hi) t.2.2 hslabs hcurrent hfinal
    (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
    (H.toHistory.activeStage_mono hvt) (H.toHistory.activeStage_time_le v)
    (fun i hi => H.lt_time_succ_of_activeStage_eq_P6N v i hi) hvt huv
  refine le_two_mul_of_abs_inv_max_sub_le_P6N hM hscalar hrec ?_
  have huv' : (u : ℝ) ≤ v := huv
  have hC : 0 ≤ (Ctime : ℝ) * M := mul_nonneg Ctime.coe_nonneg hM.le
  nlinarith

/-- consumer：`BTSC:168_P6L`（全 slab footprint 形）由窗口形推回（丢 guard）。 -/
example : type_of% @scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds_P6L.{u} := by
  intro H Ctime qcan M u t hut p A hslabs hcurrent hfinal hM hqcan hscalar htime
  exact H.scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds_window_P6N hut A
    (fun i hf hl v hv _ hR => hslabs i hf hl v hv hR)
    (fun j y hj hy v hv _ hR => hcurrent j y hj hy v hv hR)
    (fun h y ht hy v hv _ hR => hfinal h y ht hy v hv hR) hM hqcan hscalar htime

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

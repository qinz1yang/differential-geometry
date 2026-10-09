import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceScalarControl

/-!
# L6-A spine 叶子：`BackwardTraceScalarControl` 的 footprint 局部化（`_P6L`，合同 §5 通用叶子）

局部化合同 §2 (D-event)/(D-final) 与 rev1a-centers C2：原 `ST/BackwardTraceScalarControl.lean`
`:56,:82,:105,:168` 的导数界前提（`DerivativeBoundBefore` / `EventSlabsDerivative`，carrier 全局）
在证明里只在**一条 backward trace 的点**上求值 [V]：
* `hslabs` 只经 `BackwardTraceScalarTime:16`（`inv_max_scalar_sub_endpoint_le_at_time`，其 `hbound`
  本就是 trace 点形）在 `A.point i.castSucc …` 上用（原 l.127）；
* `hcurrent` / `hfinal` 只在 trace 端点 `x`（`:168` 中为 `p`）上用（原 l.97、l.103 经 `:56`）。
⇒ `hslabs` 改 trace 点形；`hcurrent`/`hfinal` 改"在端点"形（stage 依赖用 `HEq y x`，同 P6C
`htested` 的写法）；`:56` 的 `hG` 改为点 `y` 处。无具名新 Prop。私有 `:20,:33` 无前提，原样复制。
证明体照抄；结论逐字。
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem le_two_mul_of_abs_inv_max_sub_le_P6L {M R Rt Δ : ℝ} {C : ℝ≥0} (hM : 0 < M)
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

private theorem lipschitzOnWith_inv_max_scalar_Icc_P6L {P : OrientedThreeStage.{u}}
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

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ}

/-- **`_P6L`**：原 `IncomingSlab.lipschitzOnWith_inv_max_scalar_of_derivativeBoundBefore`
（`BTSC:56`）；`hG` 只在点 `y` 处。 -/
theorem lipschitzOnWith_inv_max_scalar_of_derivativeBoundBefore_P6L (G : P.IncomingSlab a s)
    {Ctime : ℝ≥0} {qcan q t : ℝ} (hq : 0 < q) (hqcan : qcan ≤ q) (hts : t < s) (y : P.Carrier)
    (hG : ∀ v ∈ Ioo a t, qcan < G.flow.scalar v y →
      |derivWithin (fun w => G.flow.scalar w y) (Iic v) v| ≤ Ctime * G.flow.scalar v y ^ 2) :
    LipschitzOnWith Ctime (fun v => (max q (G.flow.scalar v y))⁻¹) (Icc a t) :=
  lipschitzOnWith_inv_max_scalar_Icc_P6L G.equation hq (fun _ hv => ⟨hv.1, hv.2.trans_lt hts⟩) y
    (fun v hv hR => hG v hv (hqcan.trans_lt hR))

end OrientedThreeStage.IncomingSlab

namespace BackwardPointTrace

variable {K : ObservedHistory.{u}}

private theorem lipschitzOnWith_inv_max_stageMetric_scalar_P6L (k : Fin (K.eventCount + 1))
    (x : (K.stage k).Carrier) {Ctime : ℝ≥0} {qcan q t : ℝ} (hq : 0 < q) (hqcan : qcan ≤ q)
    (hnext : ∀ i : Fin K.eventCount, k = i.castSucc → t < K.time i.succ) (ht : t ≤ K.horizon)
    (hcurrent : ∀ i : Fin K.eventCount, ∀ y : (K.stage i.castSucc).Carrier,
      i.castSucc = k → HEq y x → ∀ v ∈ Ioo (K.time i.castSucc) t,
      qcan < (K.event i).incoming.flow.scalar v y →
      |derivWithin (fun w => (K.event i).incoming.flow.scalar w y) (Iic v) v| ≤
        Ctime * (K.event i).incoming.flow.scalar v y ^ 2)
    (hfinal : ∀ h : K.time (Fin.last K.eventCount) < K.horizon,
      ∀ y : (K.stage (Fin.last K.eventCount)).Carrier, k = Fin.last K.eventCount → HEq y x →
      ∀ v ∈ Ioo (K.time (Fin.last K.eventCount)) t,
      qcan < ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y →
      |derivWithin (fun w => ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar w y)
        (Iic v) v| ≤
        Ctime * ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y ^ 2) :
    LipschitzOnWith Ctime (fun v => (max q (metricScalarAt (K.stageMetric k v) x))⁻¹)
      (Icc (K.time k) t) := by
  cases k using Fin.lastCases with
  | last =>
    by_cases h : K.time (Fin.last K.eventCount) < K.horizon
    · simp only [ObservedHistory.stageMetric_last_of_lt (h := h)]
      exact lipschitzOnWith_inv_max_scalar_Icc_P6L (K.finalSlab h).equation hq
        (fun _ hv => ⟨hv.1, hv.2.trans ht⟩) x
        (fun v hv hR => hfinal h x rfl HEq.rfl v hv (hqcan.trans_lt hR))
    · simp only [ObservedHistory.stageMetric_last_of_le (not_lt.mp h)]
      exact (LipschitzWith.const _).lipschitzOnWith.weaken zero_le
  | cast i =>
    simp only [ObservedHistory.stageMetric_castSucc_apply]
    exact (K.event i).incoming.lipschitzOnWith_inv_max_scalar_of_derivativeBoundBefore_P6L hq
      hqcan (hnext i rfl) x (hcurrent i x rfl HEq.rfl)

/-- **`_P6L`**：原 `BackwardPointTrace.inv_max_stageMetric_scalar_sub_le_of_derivativeBoundBefore`
（`BTSC:105`）；`hslabs` 改 trace 点形，`hcurrent`/`hfinal` 改端点 `x` 形。结论逐字。 -/
theorem inv_max_stageMetric_scalar_sub_le_of_derivativeBoundBefore_P6L
    {first k : Fin (K.eventCount + 1)} {hle : first ≤ k} {x : (K.stage k).Carrier}
    (A : BackwardPointTrace K first k hle x) {Ctime : ℝ≥0} {qcan q t : ℝ}
    (hq : 0 < q) (hqcan : qcan ≤ q) (htk : K.time k ≤ t)
    (hnext : ∀ i : Fin K.eventCount, k = i.castSucc → t < K.time i.succ) (ht : t ≤ K.horizon)
    (hslabs : ∀ i : Fin K.eventCount, ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ k,
      ∀ v ∈ Ioo (K.time i.castSucc) (K.time i.succ),
      qcan < (K.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun w => (K.event i).incoming.flow.scalar w
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic v) v| ≤
        Ctime * (K.event i).incoming.flow.scalar v
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hcurrent : ∀ i : Fin K.eventCount, ∀ y : (K.stage i.castSucc).Carrier,
      i.castSucc = k → HEq y x → ∀ v ∈ Ioo (K.time i.castSucc) t,
      qcan < (K.event i).incoming.flow.scalar v y →
      |derivWithin (fun w => (K.event i).incoming.flow.scalar w y) (Iic v) v| ≤
        Ctime * (K.event i).incoming.flow.scalar v y ^ 2)
    (hfinal : ∀ h : K.time (Fin.last K.eventCount) < K.horizon,
      ∀ y : (K.stage (Fin.last K.eventCount)).Carrier, k = Fin.last K.eventCount → HEq y x →
      ∀ v ∈ Ioo (K.time (Fin.last K.eventCount)) t,
      qcan < ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y →
      |derivWithin (fun w => ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar w y)
        (Iic v) v| ≤
        Ctime * ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y ^ 2)
    (j : Fin (K.eventCount + 1)) (hfj : first ≤ j) (hjk : j ≤ k) {v : ℝ}
    (hjv : K.time j ≤ v) (hvnext : ∀ i : Fin K.eventCount, j = i.castSucc → v < K.time i.succ)
    (hvt : v ≤ t) :
    |(max q (metricScalarAt (K.stageMetric j v) (A.point j hfj hjk)))⁻¹ -
      (max q (metricScalarAt (K.stageMetric k t) x))⁻¹| ≤ Ctime * (t - v) := by
  have hlip := lipschitzOnWith_inv_max_stageMetric_scalar_P6L k x hq hqcan hnext ht hcurrent
    hfinal
  rcases hjk.lt_or_eq with hlt | heq
  · have hjl : j ≠ Fin.last K.eventCount := ne_of_lt (hlt.trans_le (Fin.le_last k))
    obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hjl
    have hsucc : j'.succ ≤ k := Fin.castSucc_lt_iff_succ_le.mp hlt
    have hstep := A.inv_max_scalar_sub_endpoint_le_at_time hq
      (fun i hf hl w hw hR => hslabs i hf hl w hw (hqcan.trans_lt hR)) j' hfj hsucc
      ⟨hjv, hvnext j' rfl⟩
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
    have hd := hlip.dist_le_mul v ⟨hjv, hvt⟩ t ⟨htk, le_rfl⟩
    rwa [Real.dist_eq, Real.dist_eq, abs_sub_comm v t,
      abs_of_nonneg (sub_nonneg.mpr hvt)] at hd

end BackwardPointTrace

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

private theorem lt_time_succ_of_activeStage_eq_P6L (t : Icc (0 : ℝ) H.toHistory.horizon)
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

/-- **`_P6L`**：原 `RetainedCoreHistory.scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds`
（`BTSC:168`）；`hslabs` 改 trace `A` 的点形，`hcurrent`/`hfinal` 改端点 `p` 形（`HEq`）。 -/
theorem scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds_P6L
    {Ctime : ℝ≥0} {qcan M : ℝ} {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    {p : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) p)
    (hslabs : ∀ i : Fin H.toHistory.eventCount, ∀ hf : H.toHistory.activeStage u ≤ i.castSucc,
      ∀ hl : i.succ ≤ H.toHistory.activeStage t,
      ∀ v ∈ Ioo (H.toHistory.time i.castSucc) (H.toHistory.time i.succ),
      qcan < (H.toHistory.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun w => (H.toHistory.event i).incoming.flow.scalar w
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic v) v| ≤
        Ctime * (H.toHistory.event i).incoming.flow.scalar v
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hcurrent : ∀ j : Fin H.toHistory.eventCount, ∀ y : (H.toHistory.stage j.castSucc).Carrier,
      j.castSucc = H.toHistory.activeStage t → HEq y p →
      ∀ v ∈ Ioo (H.toHistory.time j.castSucc) t,
      qcan < (H.toHistory.event j).incoming.flow.scalar v y →
      |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w y) (Iic v) v| ≤
        Ctime * (H.toHistory.event j).incoming.flow.scalar v y ^ 2)
    (hfinal : ∀ h : H.toHistory.time (Fin.last H.toHistory.eventCount) < H.toHistory.horizon,
      ∀ y : (H.toHistory.stage (Fin.last H.toHistory.eventCount)).Carrier,
      H.toHistory.activeStage t = Fin.last H.toHistory.eventCount → HEq y p →
      ∀ v ∈ Ioo (H.toHistory.time (Fin.last H.toHistory.eventCount)) t,
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
  have hrec := A.inv_max_stageMetric_scalar_sub_le_of_derivativeBoundBefore_P6L hM hqcan
    (H.toHistory.activeStage_time_le t)
    (fun i hi => H.lt_time_succ_of_activeStage_eq_P6L t i hi) t.2.2 hslabs hcurrent hfinal
    (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
    (H.toHistory.activeStage_mono hvt) (H.toHistory.activeStage_time_le v)
    (fun i hi => H.lt_time_succ_of_activeStage_eq_P6L v i hi) hvt
  refine le_two_mul_of_abs_inv_max_sub_le_P6L hM hscalar hrec ?_
  have huv' : (u : ℝ) ≤ v := huv
  have hC : 0 ≤ (Ctime : ℝ) * M := mul_nonneg Ctime.coe_nonneg hM.le
  nlinarith

/-- consumer：原 `BTSC:168`（carrier 全局 `EventSlabsDerivative` / `DerivativeBoundBefore`）由 `_P6L`
版推出（全局界在 trace 点 / 端点处特化）。 -/
example
    {Ctime : ℝ≥0} {qcan M : ℝ} {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    {p : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) p)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hM : 0 < M) (hqcan : qcan ≤ M)
    (hscalar : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2) :
    ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u ≤ v) (hvt : v ≤ t),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
          (H.toHistory.activeStage_mono hvt)) ≤ 2 * M :=
  scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds_P6L H hut A
    (fun i _ hl v hv hR => hslabs i (i.castSucc_lt_succ.trans_le hl) _ v hv hR)
    (fun j y hj _ v hv hR => hcurrent j hj y v hv hR)
    (fun h y ht _ v hv hR => hfinal h ht y v hv hR) hM hqcan hscalar htime

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

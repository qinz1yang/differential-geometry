import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceScalarControl.TimeLocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefix

/-!
# L-RS：selection 切片 ↔ SLT 的 `(prefixAt k, incoming slab G)` 呈现（`_P6N`，导数 footprint 部分）

selection（G4）在 `K = F.tower.history n` 的 `toHistory` 上（SMALLVOL 核：RC 的 `toHistory` 定义等，
无 ObservedHistory ↔ RC 桥）；SLT 在 `H := K.prefixAt k`（`hend` = 树内 `prefixAt_time_last`，`rfl`）+
终端 incoming slab `G` 上。本文件把 K 层的窗口 footprint 时间导数界（G4 L10 形，阈值 `q`、窗口起点 `a`、
上界 `b`、终点 stage `k`）搬到：
* `prefix_slabs_footprint_P6N`：prefix 的 `hslabs`（SLT / G1–G2a 的 RC footprint 形 + guard `a ≤ v`）；
  trace 走树内 `backwardPointTraceOfPrefix` + `restrictFirst`，`activeStage v = j.castSucc` 用
  `subst` 推广（同 `TimeLocal` 的 `hstageBound`）。
* `incoming_derivative_of_window_P6N`：`k = i.castSucc` 时 `G := (K.event i).incoming`
  （stage / time 定义等），  `G` 上 `U` 中点的 `hder`（trace = `BackwardPointTrace.singleton`）。
records ⇐ 树内 `geometricCutoffRecordOfPrefix`（逐点，late 形直接套）；`hnc` 的受控球识别不在本文件。
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable (K : RetainedCoreHistory.{u})

/-- **`_P6N`（L-RS 1）**：K 层窗口 footprint（traces 终于 stage `k`、时刻 `a ≤ v ≤ b`）⇒ `K.prefixAt k`
的 RC footprint `hslabs`（guard `a ≤ v`）。 -/
theorem prefix_slabs_footprint_P6N (k : Fin (K.eventCount + 1)) {a b q : ℝ} {C : ℝ≥0}
    (hkb : K.time k ≤ b) (U : Set (K.stage k).Carrier)
    (hK : ∀ x ∈ U, ∀ (v : Icc (0 : ℝ) K.toHistory.horizon)
      (hvk : K.toHistory.activeStage v ≤ k), a ≤ (v : ℝ) → (v : ℝ) ≤ b →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v) k hvk x,
        K.toHistory.time (K.toHistory.activeStage v) < (v : ℝ) → (v : ℝ) < K.toHistory.horizon →
        q < metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
          (tr.point (K.toHistory.activeStage v) le_rfl hvk) →
        |derivWithin (fun w =>
            metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) w)
            (tr.point (K.toHistory.activeStage v) le_rfl hvk)) (Iic (v : ℝ)) v| ≤
          C * metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (tr.point (K.toHistory.activeStage v) le_rfl hvk) ^ 2) :
    ∀ j : Fin (K.prefixAt k).eventCount,
      ∀ (first : Fin ((K.prefixAt k).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U, ∀ B : BackwardPointTrace (K.prefixAt k).toHistory first
        (Fin.last (K.prefixAt k).eventCount) (Fin.le_last first) z,
      ∀ v ∈ Ioo ((K.prefixAt k).time j.castSucc) ((K.prefixAt k).time j.succ), a ≤ v →
      q < ((K.prefixAt k).toHistory.event j).incoming.flow.scalar v
        (B.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w => ((K.prefixAt k).toHistory.event j).incoming.flow.scalar w
        (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        C * ((K.prefixAt k).toHistory.event j).incoming.flow.scalar v
          (B.point j.castSucc hf (Fin.le_last _)) ^ 2 := by
  intro j first hf z hz B v hv hav hR
  let jK : Fin K.eventCount := Fin.castLE (Nat.le_of_lt_succ k.isLt) j
  have hjk : jK.succ ≤ k := by
    change j.val + 1 ≤ k.val
    exact j.isLt
  have hvk : v < K.time k :=
    hv.2.trans_le (K.toHistory.time_strictMono.monotone hjk)
  have hv0 : 0 ≤ v := (K.toHistory.time_nonneg _).trans hv.1.le
  have hvH : v < K.horizon := hvk.trans_le (K.toHistory.time_le_horizon_at k)
  let vI : Icc (0 : ℝ) K.toHistory.horizon := ⟨v, hv0, hvH.le⟩
  have hact : K.toHistory.activeStage vI = jK.castSucc :=
    (K.toHistory.mem_stageDomain_iff vI jK.castSucc).mp (by
      simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
        (show v ∈ Ico (K.time jK.castSucc) (K.time jK.succ) from ⟨hv.1.le, hv.2⟩))
  let Bk := K.backwardPointTraceOfPrefix k B
  have key : ∀ (m : Fin (K.eventCount + 1)) (hm : K.toHistory.activeStage vI = m)
      (hfm : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) first ≤ m) (hml : m ≤ k),
      K.toHistory.time m < v →
      q < metricScalarAt (K.toHistory.stageMetric m v) (Bk.point m hfm hml) →
      |derivWithin (fun w => metricScalarAt (K.toHistory.stageMetric m w) (Bk.point m hfm hml))
          (Iic v) v| ≤
        C * metricScalarAt (K.toHistory.stageMetric m v) (Bk.point m hfm hml) ^ 2 := by
    intro m hm hfm hml
    subst hm
    exact fun h1 => hK z hz vI hml hav (hvk.le.trans hkb) (Bk.restrictFirst hfm hml) h1 hvH
  have hfK : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) first ≤ jK.castSucc :=
    Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hf)
  have h := key jK.castSucc hact hfK (jK.castSucc_lt_succ.le.trans hjk) hv.1
  simp only [ObservedHistory.stageMetric_castSucc_apply] at h
  exact h hR

/-- **`_P6N`（L-RS 2）**：`k = i.castSucc` 时 `G := (K.event i).incoming`（定义等地是 `K.prefixAt i.castSucc`
的终端 incoming slab）上 `U` 中点的 `hder`（guard `a ≤ v`，`v < t ≤ b`、`t ≤ time i.succ`）。 -/
theorem incoming_derivative_of_window_P6N (i : Fin K.eventCount) {a b q t : ℝ} {C : ℝ≥0}
    (htb : t ≤ b) (hts : t ≤ K.time i.succ) (U : Set (K.stage i.castSucc).Carrier)
    (hK : ∀ x ∈ U, ∀ (v : Icc (0 : ℝ) K.toHistory.horizon)
      (hvk : K.toHistory.activeStage v ≤ i.castSucc), a ≤ (v : ℝ) → (v : ℝ) ≤ b →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v) i.castSucc hvk x,
        K.toHistory.time (K.toHistory.activeStage v) < (v : ℝ) → (v : ℝ) < K.toHistory.horizon →
        q < metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
          (tr.point (K.toHistory.activeStage v) le_rfl hvk) →
        |derivWithin (fun w =>
            metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) w)
            (tr.point (K.toHistory.activeStage v) le_rfl hvk)) (Iic (v : ℝ)) v| ≤
          C * metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (tr.point (K.toHistory.activeStage v) le_rfl hvk) ^ 2) :
    ∀ x ∈ U, ∀ v ∈ Ioo (K.time i.castSucc) t, a ≤ v →
      q < (K.toHistory.event i).incoming.flow.scalar v x →
      |derivWithin (fun w => (K.toHistory.event i).incoming.flow.scalar w x) (Iic v) v| ≤
        C * (K.toHistory.event i).incoming.flow.scalar v x ^ 2 := by
  intro x hx v hv hav hR
  have hv0 : 0 ≤ v := (K.toHistory.time_nonneg _).trans hv.1.le
  have hvi : v < K.time i.succ := hv.2.trans_le hts
  have hvH : v < K.horizon := hvi.trans_le (K.toHistory.time_le_horizon_at i.succ)
  let vI : Icc (0 : ℝ) K.toHistory.horizon := ⟨v, hv0, hvH.le⟩
  have hact : K.toHistory.activeStage vI = i.castSucc :=
    (K.toHistory.mem_stageDomain_iff vI i.castSucc).mp (by
      simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
        (show v ∈ Ico (K.time i.castSucc) (K.time i.succ) from ⟨hv.1.le, hvi⟩))
  have h := hK x hx vI
  generalize hm : K.toHistory.activeStage vI = m at h
  obtain rfl : m = i.castSucc := hm.symm.trans hact
  have h2 := h le_rfl hav (hv.2.le.trans htb)
    (BackwardPointTrace.singleton K.toHistory i.castSucc x) hv.1 hvH
  simp only [ObservedHistory.stageMetric_castSucc_apply] at h2
  exact h2 hR

/-- consumer（G4 L10 ⇒ L-RS 1）：selection 窗口 `[σ − θ/Q, σ]` 的 K 层 footprint（G4
`derivative_footprint_on_window_traces_P6N` 的输出形，`q = 4Q`）⇒ `K.prefixAt (activeStage σ)` 的 RC
footprint `hslabs`（guard `σ − θ/Q ≤ v`）。 -/
example {σ : Icc (0 : ℝ) K.toHistory.horizon} {θ Q : ℝ} {C : ℝ≥0}
    (U : Set (K.stage (K.toHistory.activeStage σ)).Carrier)
    (hL10 : ∀ x ∈ U, ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hvs : v ≤ σ),
      (σ : ℝ) - θ / Q ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
        (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono hvs) x,
        K.toHistory.time (K.toHistory.activeStage v) < (v : ℝ) → (v : ℝ) < K.toHistory.horizon →
        4 * Q < metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
          (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvs)) →
        |derivWithin (fun w =>
            metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) w)
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvs)))
            (Iic (v : ℝ)) v| ≤
          C * metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvs)) ^ 2) :
    ∀ j : Fin (K.prefixAt (K.toHistory.activeStage σ)).eventCount,
      ∀ (first : Fin ((K.prefixAt (K.toHistory.activeStage σ)).eventCount + 1))
        (hf : first ≤ j.castSucc),
      ∀ z ∈ U, ∀ B : BackwardPointTrace (K.prefixAt (K.toHistory.activeStage σ)).toHistory first
        (Fin.last (K.prefixAt (K.toHistory.activeStage σ)).eventCount) (Fin.le_last first) z,
      ∀ v ∈ Ioo ((K.prefixAt (K.toHistory.activeStage σ)).time j.castSucc)
        ((K.prefixAt (K.toHistory.activeStage σ)).time j.succ), (σ : ℝ) - θ / Q ≤ v →
      4 * Q < ((K.prefixAt (K.toHistory.activeStage σ)).toHistory.event j).incoming.flow.scalar v
        (B.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w =>
        ((K.prefixAt (K.toHistory.activeStage σ)).toHistory.event j).incoming.flow.scalar w
          (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        C * ((K.prefixAt (K.toHistory.activeStage σ)).toHistory.event j).incoming.flow.scalar v
          (B.point j.castSucc hf (Fin.le_last _)) ^ 2 :=
  K.prefix_slabs_footprint_P6N (K.toHistory.activeStage σ) (K.toHistory.activeStage_time_le σ) U
    (fun x hx v _ hav hvb tr => hL10 x hx v hvb hav tr)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAgeRecord_P6M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HistoryRescale_P6N
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching

/-!
# 重标度 K 层的窗口 pinching `hpinchK0`（O-CH11-P6SEL2 G2 部分，后缀 `_P6X2`）

`hpinchK0_rescale_P6X2`：存在**固定** admissible `Phi`（与 history、尺度 `c`、`n` 无关），使任意
原尺度 history `K`（全 records `recordsF` + 时刻 0 的 HI `a₀ > 0`）重标度 `K̃ := K.rescale_P6N c`
后，每个 event slab 在年龄窗 `t̃ ≥ T̃₀ ≥ 1` 内 `PhiAlmostNonnegative`。证明：树内
`exists_admissiblePinchingFunction_phiAlmostNonnegative_of_fixedHamiltonIveyRegion`（`a₀ := 1`）
+ 重标度年龄 `a₀/c + t̃ ≥ 1`（`inFixedHamiltonIveyRegion_scaleMetric_inv_iff_P6M`：`c⁻¹ g(ct̃)` 在
年龄 `a₀/c + t̃` ⇔ `g(ct̃)` 在年龄 `a₀ + ct̃`）⇐ slab 内 HI 传播
（`IncomingSlab.fixedHamiltonIveyRegion_and_scalar_lower`）⇐ history HI
（`fixedHamiltonIveyRegion_and_scalar_lower`）。这是 lateHI 收口主形 `hpinchK0` 窗口形在 D-17
重标度序列上的供给（`T̃₀ := max 1 (T₀/c)`）。
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 单 history 版（树内 `ObservedHistory.rescale`）：给定 age-normalized `Phi` 的生产者 `hphi`。 -/
theorem ObservedHistory.phiAlmostNonnegative_rescale_P6X2 {Phi : ℝ → ℝ}
    (hphi : ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X],
        ∀ (D : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := X) D)
          (W : Set ℝ) (a : ℝ → ℝ),
          (∀ t ∈ W, 1 ≤ a t) →
          (∀ t ∈ W, ∀ x : X, InFixedHamiltonIveyRegion (S.base.metric t) (a t) x) →
          Perelman.PhiAlmostNonnegative S W Phi)
    (H : ObservedHistory.{u}) {c : ℝ} (hc : 0 < c) {pF : CutoffParameters}
    (recordsF : ∀ i, GeometricCutoffRecord H i pF) {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    {T₀ : ℝ} (hT₀ : 1 ≤ T₀) (i : Fin H.eventCount) :
    Perelman.PhiAlmostNonnegative ((H.rescale c hc).event i).incoming.flow
      (Ico ((H.rescale c hc).time i.castSucc) ((H.rescale c hc).time i.succ) ∩ Ici T₀) Phi := by
  have hhistory := H.fixedHamiltonIveyRegion_and_scalar_lower recordsF ha₀
    (fun x => (hHI x).1) (fun x => (hHI x).2)
  have hstart : H.time i.castSucc ∈ H.stageDomain i.castSucc := by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show H.time i.castSucc ∈ Ico (H.time i.castSucc) (H.time i.succ) from
        ⟨le_rfl, H.time_strictMono i.castSucc_lt_succ⟩)
  have hinit := H.event_initial i
  have hstage (x : (H.stage i.castSucc).Carrier) :
      InFixedHamiltonIveyRegion (H.initialMetric i.castSucc) (a₀ + H.time i.castSucc) x ∧
        -3 / (a₀ + H.time i.castSucc) ≤ metricScalarAt (H.initialMetric i.castSucc) x := by
    simpa only [H.stageMetric_initial] using hhistory.1 i.castSucc (H.time i.castSucc) hstart x
  have hA : 0 < a₀ + H.time i.castSucc := by linarith [H.time_nonneg i.castSucc]
  have hfuture := (H.event i).incoming.fixedHamiltonIveyRegion_and_scalar_lower hA
    (fun x => by rw [hinit]; exact (hstage x).1)
    (fun x => by
      change -3 / (a₀ + H.time i.castSucc) ≤
        metricScalarAt ((H.event i).incoming.flow.base.metric (H.time i.castSucc)) x
      rw [hinit]
      exact (hstage x).2)
  refine hphi _ _ ((H.event i).incoming.rescale c hc).flow _ (fun t => a₀ / c + t) ?_ ?_
  · intro t ht
    have h1 : T₀ ≤ t := ht.2
    have h2 : 0 < a₀ / c := div_pos ha₀ hc
    linarith
  · intro t ht x
    rw [OrientedThreeStage.IncomingSlab.rescale_metric,
      inFixedHamiltonIveyRegion_scaleMetric_inv_iff_P6M hc]
    have hlo : H.time i.castSucc / c ≤ t := ht.1.1
    have hhi : t < H.time i.succ / c := ht.1.2
    rw [div_le_iff₀ hc] at hlo
    rw [lt_div_iff₀ hc] at hhi
    have hct : c * t ∈ Ico (H.time i.castSucc) (H.time i.succ) := ⟨by linarith, by linarith⟩
    have h := (hfuture (c * t) hct x).1
    have heq : a₀ + H.time i.castSucc + c * t - H.time i.castSucc = c * (a₀ / c + t) := by
      field_simp
      ring
    rw [← heq]
    exact h

/-- **重标度 K 层的窗口 pinching（`_P6X2`）**：见文件头（`Phi` 固定，与 `K c pF a₀ T₀` 无关）。 -/
theorem hpinchK0_rescale_P6X2 :
    ∃ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi ∧
      ∀ (K : RetainedCoreHistory.{u}) (c : ℝ) (hc : 0 < c) (pF : CutoffParameters),
        (∀ i, GeometricCutoffRecord K.toHistory i pF) →
      ∀ (a₀ : ℝ), 0 < a₀ →
        (∀ x, InFixedHamiltonIveyRegion (K.initialMetric 0) a₀ x ∧
          -3 / a₀ ≤ metricScalarAt (K.initialMetric 0) x) →
      ∀ (T₀ : ℝ), 1 ≤ T₀ → ∀ i : Fin K.eventCount,
        Perelman.PhiAlmostNonnegative ((K.rescale_P6N c hc).toHistory.event i).incoming.flow
          (Ico ((K.rescale_P6N c hc).time i.castSucc) ((K.rescale_P6N c hc).time i.succ) ∩
            Ici T₀) Phi := by
  obtain ⟨Phi, hPhi, hphi⟩ :=
    Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_of_fixedHamiltonIveyRegion.{u}
      (a₀ := 1) one_pos
  exact ⟨Phi, hPhi, fun K c hc _ recordsF a₀ ha₀ hHI _ hT₀ i =>
    K.toHistory.phiAlmostNonnegative_rescale_P6X2 hphi hc recordsF ha₀ hHI hT₀ i⟩

/-- consumer：lateHI 收口主形 `hpinchK0` 窗口形（`K n := (Kn n).rescale_P6N (c n)`、
`T̃₀ n := max 1 (T₀ n / c n)`、`phi` 与 n 无关）由原尺度 `recordsF` + 逐 n HI 供给。 -/
example {Kn : ℕ → RetainedCoreHistory.{u}} (c : ℕ → ℝ) (hc : ∀ n, 0 < c n)
    {pF : ℕ → CutoffParameters} (recordsF : ∀ n i, GeometricCutoffRecord (Kn n).toHistory i (pF n))
    {a₀ : ℕ → ℝ} (ha₀ : ∀ n, 0 < a₀ n)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((Kn n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((Kn n).initialMetric 0) x) (T₀ : ℕ → ℝ) :
    ∃ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi ∧
      let K : ℕ → RetainedCoreHistory.{u} := fun n => (Kn n).rescale_P6N (c n) (hc n)
      ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
        ((K n).toHistory.event i).incoming.flow
        (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (max 1 (T₀ n / c n))) phi := by
  obtain ⟨Phi, hPhi, h⟩ := hpinchK0_rescale_P6X2.{u}
  exact ⟨Phi, hPhi, fun n i => h (Kn n) (c n) (hc n) (pF n) (recordsF n) (a₀ n) (ha₀ n) (hHI n) _
    (le_max_left _ _) i⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

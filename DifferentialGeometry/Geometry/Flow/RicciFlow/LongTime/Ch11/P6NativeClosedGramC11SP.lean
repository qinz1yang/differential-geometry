import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Metric.Family.Regularity.DifferentialOperator

set_option autoImplicit false

/-!
# trace 公共 flow 的闭窗 Gram 光滑（O-CH11-SPINE-B G6 = SL2-b 第一部分，后缀 `_C11SP`）

Codex native 交接点名的缺口："`InitialLocalEndpointHorizon` / `LocalWindowCurvatureHorizon` 都要
**闭窗** `[0, θ]` 上的时空 Gram 光滑，而 `closed a t` 的 `regular` 只有 `Ioo a t`，没有任何定理产出它"。
本页对 `exists_common_flow_with_compact_neighborhood_of_isTracedRegion` 形的公共 flow（`S / f / hmetric`，
跨任意多个 event，patch 在中间 crossing 处 retained）在**闭**窗 `[a, t]` 上产出 chart Gram 联合光滑：
* 内部 `Ioo a t`：`IsSolutionOn` 的 `smoothMetric.chartGramMatrix_contDiffOn`；
* 左端 `a`：`activeStage a` 的 slab（incoming / final）`smoothUpTo` 含 stage 起点——
  `stageMetric_smoothUpTo_C11SP` + `chartGramMatrix_joint_contMDiffOn` +
  `localPullback_chartGramMatrix_joint_contMDiffOn`；
* 右端 `t`（正 stage age `time (activeStage t) < t`，RegularSlice 时刻满足）：同上用 `activeStage t` 的 slab；
三段经 `ContMDiffWithinAt.mono_of_mem_nhdsWithin` 拼合。`a` 可以是 birth（新生 cap 的 reset 时刻）。
**SL2-b 余项**（未做）：把它与时间平移、`a` 时刻 U 内闭球紧性（需 `[a,t]` 上 Rm 界的距离畸变）、初始 jets 经 `f`
（局部微分同胚）的搬运接成 traced-region 版 reset Shi。
-/

noncomputable section

open Set Bundle Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch11

universe u

/-- stage `j` 的 history 度量在整个 stage domain（含 birth 端点）上 smooth up to。 -/
theorem stageMetric_smoothUpTo_C11SP (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1))
    (hj : j = Fin.last H.eventCount → H.time j < H.horizon) :
    (H.stage j).MetricSmoothUpTo (H.stageMetric j) (H.stageDomain j) := by
  cases j using Fin.lastCases with
  | last =>
    have h := hj rfl
    have hm : H.stageMetric (Fin.last H.eventCount) = (H.finalSlab h).flow.base.metric := by
      simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_left h]
    have hd : H.stageDomain (Fin.last H.eventCount) =
        Icc (H.time (Fin.last H.eventCount)) H.horizon := by
      simp only [ObservedHistory.stageDomain, Fin.lastCases_last]
    rw [hm, hd]
    exact (H.finalSlab h).smoothUpTo
  | cast i =>
    have hm : H.stageMetric i.castSucc = (H.event i).incoming.flow.base.metric := by
      simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]
    have hd : H.stageDomain i.castSucc = Ico (H.time i.castSucc) (H.time i.succ) := by
      simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc]
    rw [hm, hd]
    exact (H.event i).incoming.smoothUpTo

/-- stage domain 在其任一点右侧（到 horizon 为止）有开邻域。 -/
theorem exists_open_right_stageDomain_C11SP (H : ObservedHistory.{u})
    (j : Fin (H.eventCount + 1)) {v : ℝ} (hv : v ∈ H.stageDomain j) :
    ∃ O : Set ℝ, IsOpen O ∧ v ∈ O ∧
      ∀ w, v ≤ w → w ≤ H.horizon → w ∈ O → w ∈ H.stageDomain j := by
  cases j using Fin.lastCases with
  | last =>
    have hd : H.stageDomain (Fin.last H.eventCount) =
        Icc (H.time (Fin.last H.eventCount)) H.horizon := by
      simp only [ObservedHistory.stageDomain, Fin.lastCases_last]
    rw [hd] at hv ⊢
    exact ⟨univ, isOpen_univ, mem_univ _, fun w hvw hwh _ => ⟨hv.1.trans hvw, hwh⟩⟩
  | cast i =>
    have hd : H.stageDomain i.castSucc = Ico (H.time i.castSucc) (H.time i.succ) := by
      simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc]
    rw [hd] at hv ⊢
    exact ⟨Iio (H.time i.succ), isOpen_Iio, hv.2, fun w hvw _ hwO => ⟨hv.1.trans hvw, hwO⟩⟩

/-- stage domain 是序凸的。 -/
theorem stageDomain_ordConnected_C11SP (H : ObservedHistory.{u})
    (j : Fin (H.eventCount + 1)) : (H.stageDomain j).OrdConnected := by
  cases j using Fin.lastCases with
  | last =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last]
    exact ordConnected_Icc
  | cast i =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc]
    exact ordConnected_Ico

/-- **G6（SL2-b 闭窗 Gram，PROVED 目标）**：trace 公共 flow
（`exists_common_flow_with_compact_neighborhood_of_isTracedRegion` 的 `S / f / hmetric` 形）
在**闭**窗 `[a, t]` 上 chart Gram 联合光滑——内部用 `IsSolutionOn`，左端用
`activeStage a` 的 slab `smoothUpTo`，右端（正 stage age）用 `activeStage t` 的 slab `smoothUpTo`。 -/
theorem commonFlow_closedGram_C11SP (H : ObservedHistory.{u})
    {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t) (hlt : (a : ℝ) < t)
    (hpos : H.time (H.activeStage t) < t)
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M]
    (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → M → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (S : SolutionOn (I := ThreeModel) (M := M) (RealTimeInterval.closed a.val t.val hat))
    (hS : IsSolutionOn S)
    (hmetric : ∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
      ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain j.val →
        S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j))
    (x₀ : M) (i k : Fin (Module.finrank ℝ ThreeSpace)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => Tensor.Coordinates.chartGramMatrix (S.base.metric q.1) x₀ q.2 i k)
      (Icc a.val t.val ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet) := by
  classical
  set B := (trivializationAt ThreeSpace (TangentSpace ThreeModel) x₀).baseSet with hB
  have piece : ∀ jj : H.StageInterval (H.activeStage a) (H.activeStage t),
      (jj.val = Fin.last H.eventCount → H.time jj.val < H.horizon) →
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => Tensor.Coordinates.chartGramMatrix (S.base.metric q.1) x₀ q.2 i k)
        ((Icc a.val t.val ∩ H.stageDomain jj.val) ×ˢ B) := by
    intro jj hjj
    let S' : SolutionOn (I := ThreeModel) (M := (H.stage jj.val).Carrier)
        (RealTimeInterval.closed a.val t.val hat) := { base := { metric := H.stageMetric jj.val } }
    have hsm := stageMetric_smoothUpTo_C11SP H jj.val hjj
    have hpb := SolutionOn.localPullback_chartGramMatrix_joint_contMDiffOn S' (f jj) (hf jj)
      (H.stageDomain jj.val)
      (fun y₀ i' k' => chartGramMatrix_joint_contMDiffOn (H.stageMetric jj.val)
        (H.stageDomain jj.val) hsm.jointContMDiffOn y₀ i' k') x₀ i k
    refine (hpb.mono (prod_mono inter_subset_right subset_rfl)).congr ?_
    intro q hq
    change Tensor.Coordinates.chartGramMatrix (S.base.metric q.1) x₀ q.2 i k =
      Tensor.Coordinates.chartGramMatrix
        (localPullMetric (H.stageMetric jj.val q.1) (f jj) (hf jj)) x₀ q.2 i k
    rw [hmetric jj q.1 hq.1.1 hq.1.2]
  have hint : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => Tensor.Coordinates.chartGramMatrix (S.base.metric q.1) x₀ q.2 i k)
      (Ioo a.val t.val ×ˢ B) :=
    hS.smoothMetric.chartGramMatrix_contDiffOn (G := S.family) (fun _ h => h) x₀ i k
  let ja : H.StageInterval (H.activeStage a) (H.activeStage t) :=
    ⟨H.activeStage a, le_rfl, H.activeStage_mono hat⟩
  let jt : H.StageInterval (H.activeStage a) (H.activeStage t) :=
    ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩
  have hja : ja.val = Fin.last H.eventCount → H.time ja.val < H.horizon := fun _ =>
    (H.activeStage_time_le a).trans_lt (hlt.trans_le t.2.2)
  have hjt : jt.val = Fin.last H.eventCount → H.time jt.val < H.horizon := fun _ =>
    hpos.trans_le t.2.2
  intro q hq
  rcases eq_or_lt_of_le hq.1.1 with hqa | hqa
  · -- 左端：`q.1 = a`
    obtain ⟨O, hO, haO, hOsub⟩ := exists_open_right_stageDomain_C11SP H (H.activeStage a)
      (H.activeStage_mem a)
    refine ((piece ja hja) q ⟨⟨hq.1, ?_⟩, hq.2⟩).mono_of_mem_nhdsWithin ?_
    · rw [← hqa]; exact H.activeStage_mem a
    · refine mem_nhdsWithin.2 ⟨O ×ˢ univ, hO.prod isOpen_univ, ⟨hqa ▸ haO, mem_univ _⟩, ?_⟩
      rintro r ⟨⟨hrO, -⟩, hrI, hrB⟩
      exact ⟨⟨hrI, hOsub r.1 hrI.1 (hrI.2.trans t.2.2) hrO⟩, hrB⟩
  · rcases eq_or_lt_of_le hq.1.2 with hqt | hqt
    · -- 右端：`q.1 = t`
      refine ((piece jt hjt) q ⟨⟨hq.1, ?_⟩, hq.2⟩).mono_of_mem_nhdsWithin ?_
      · rw [hqt]; exact H.activeStage_mem t
      · refine mem_nhdsWithin.2 ⟨Ioi (H.time (H.activeStage t)) ×ˢ univ,
          isOpen_Ioi.prod isOpen_univ, ⟨hqt ▸ hpos, mem_univ _⟩, ?_⟩
        rintro r ⟨⟨hrO, -⟩, hrI, hrB⟩
        refine ⟨⟨hrI, ?_⟩, hrB⟩
        have hstart : H.time (H.activeStage t) ∈ H.stageDomain (H.activeStage t) := by
          have h := H.activeStage_mem (H.stageTime (H.activeStage t))
          rw [H.activeStage_stageTime] at h
          exact h
        exact (stageDomain_ordConnected_C11SP H (H.activeStage t)).out hstart
          (H.activeStage_mem t) ⟨le_of_lt hrO, hrI.2⟩
    · -- 内部
      refine (hint q ⟨⟨hqa, hqt⟩, hq.2⟩).mono_of_mem_nhdsWithin ?_
      refine mem_nhdsWithin.2 ⟨Ioo a.val t.val ×ˢ univ, isOpen_Ioo.prod isOpen_univ,
        ⟨⟨hqa, hqt⟩, mem_univ _⟩, ?_⟩
      rintro r ⟨⟨hrO, -⟩, -, hrB⟩
      exact ⟨hrO, hrB⟩

end GC.LongTime.Ch11

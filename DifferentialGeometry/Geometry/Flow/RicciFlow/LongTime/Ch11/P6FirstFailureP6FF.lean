import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalTimeControlPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefixTransport

/-!
# Slab 级首次失败（`_P6FF`，O-CH11-FIRSTFAIL G1；PROVED，无新具名 Prop / binder）

kernel 坏点的"首次失败"性质只在 **event slab 前缀**上被消费：`hanchor0_eventSlab_noJ10_P6JG3` 的
`hslabsSel`（阈值 `Cg·R n`，只覆盖坏点 slab `j n` 之前的 slab；同 slab 部分已由 `hderSel` 付）。
这里给出不需要任何闭性 / 紧性的离散版本：

* `eventSlabsDerivative_or_firstBadSlab_P6FF`：`EventSlabsDerivative Ctime q k` 要么成立，要么存在
  **最小**的坏 slab `i`（`i.castSucc < k`，其上有 `q < R` 且 `|∂ₜR| > Ctime·R²` 的点），且 `i` 之前的
  前缀干净（`EventSlabsDerivative Ctime q i.castSucc`）。证明 = `Finset.min'`（slab 指标有限）。
* `exists_cleanPrefix_badPoint_P6FF`：全局一步 descent——阈值 `Cg·R₀`（`1 ≤ Cg`）下要么前缀干净，
  要么存在更早 slab 上的 Dt 坏点 `w`，`R(w) > Cg·R₀ ≥ R₀`，且它自己的前缀在阈值 `Cg·R(w)` 下干净。
* `slab_le_of_time_le_P6FF` / `eventSlabsDerivative_inherit_P6FF`：selection 输出（时间 `s ≤ T`、
  `R(s,y) ≥ R₀`）继承 clean prefix（slab 指标单调 + 阈值单调）。
* `eventSlabsDerivative_of_hfirst_P6FF`：LOCALDT 的 ObservedHistory 形 `hfirst`（`∀ v < σ, q < R → CN`）
  的 Dt 半 ⇒ `EventSlabsDerivative Ctime q k`（`time k ≤ σ`）。
* `not_hasSpatialCanonicalTimeControl_of_slab_P6FF`：slab 内 Dt 坏点 ⇒ ObservedHistory 层
  `¬ HasSpatialCanonicalTimeControl`（可喂 selection 的 `hbad`）。

**不是**付清：kernel 坏点是 seed-localized selection 的输出，上述最小坏 slab / descent 点不 localized；
clean prefix 子句的诚实来源 = 顶层 bad-sequence 定义加 slab-first 条款（见 state-O-CH11-FIRSTFAIL）。
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable {H : RetainedCoreHistory.{u}}

/-- **前缀指标单调**：`EventSlabsDerivative` 对更短前缀 `k' ≤ k` 仍成立。 -/
theorem eventSlabsDerivative_anti_P6FF {Ctime : ℝ≥0} {q : ℝ} {k k' : Fin (H.eventCount + 1)}
    (h : H.EventSlabsDerivative Ctime q k) (hk : k' ≤ k) :
    H.EventSlabsDerivative Ctime q k' :=
  fun j hj => h j (lt_of_lt_of_le hj hk)

/-- **阈值单调**：更大阈值 `q ≤ q'` 下仍成立。 -/
theorem eventSlabsDerivative_threshold_mono_P6FF {Ctime : ℝ≥0} {q q' : ℝ}
    {k : Fin (H.eventCount + 1)} (h : H.EventSlabsDerivative Ctime q k) (hq : q ≤ q') :
    H.EventSlabsDerivative Ctime q' k :=
  fun j hj y t ht hR => h j hj y t ht (lt_of_le_of_lt hq hR)

/-- **slab 级首次失败二分（PROVED，无闭性 / 紧性）**：前缀 `k` 上 `EventSlabsDerivative Ctime q`
要么成立，要么存在最小坏 slab `i`：其内部有 `q < R`、`Ctime·R² < |∂ₜR|` 的点，且 `i` 之前前缀干净。 -/
theorem eventSlabsDerivative_or_firstBadSlab_P6FF (Ctime : ℝ≥0) (q : ℝ)
    (k : Fin (H.eventCount + 1)) :
    H.EventSlabsDerivative Ctime q k ∨
      ∃ i : Fin H.eventCount, i.castSucc < k ∧
        (∃ (y : (H.stage i.castSucc).Carrier) (t : ℝ),
          t ∈ Ioo (H.time i.castSucc) (H.time i.succ) ∧
          q < (H.toHistory.event i).incoming.flow.scalar t y ∧
          (Ctime : ℝ) * (H.toHistory.event i).incoming.flow.scalar t y ^ 2 <
            |derivWithin (fun v => (H.toHistory.event i).incoming.flow.scalar v y) (Iic t) t|) ∧
        H.EventSlabsDerivative Ctime q i.castSucc := by
  classical
  by_cases hk : H.EventSlabsDerivative Ctime q k
  · exact Or.inl hk
  · right
    let S : Finset (Fin H.eventCount) := Finset.univ.filter (fun i => i.castSucc < k ∧
      ¬ (H.toHistory.event i).incoming.DerivativeBoundBefore Ctime q (H.time i.succ))
    have hS : S.Nonempty := by
      unfold EventSlabsDerivative at hk
      push Not at hk
      obtain ⟨i, hik, hbad⟩ := hk
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hik, hbad⟩⟩
    have hmem : S.min' hS ∈ S := Finset.min'_mem S hS
    obtain ⟨hik, hbad⟩ := (Finset.mem_filter.mp hmem).2
    refine ⟨S.min' hS, hik, ?_, ?_⟩
    · unfold OrientedThreeStage.IncomingSlab.DerivativeBoundBefore at hbad
      push Not at hbad
      obtain ⟨y, t, ht, hq, hlt⟩ := hbad
      exact ⟨y, t, ht, hq, hlt⟩
    · intro j hj
      by_contra hjbad
      have hjS : j ∈ S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans hj hik, hjbad⟩
      have hle := Finset.min'_le S j hjS
      exact absurd hle (not_le.mpr (Fin.castSucc_lt_castSucc_iff.mp hj))

/-- **全局一步 descent（PROVED）**：`1 ≤ Cg`、`0 ≤ R₀`。阈值 `Cg·R₀` 下前缀 `k` 要么干净，要么存在
更早 slab `i` 上的 Dt 坏点 `(y, t)`：`R₀ < R(t,y)`、`Cg·R₀ < R(t,y)`，且 `i` 之前前缀在**它自己的**
阈值 `Cg·R(t,y)` 下干净（即"前缀干净的坏点"；无需 ceiling，slab 指标有限）。 -/
theorem exists_cleanPrefix_badPoint_P6FF (Ctime : ℝ≥0) {Cg R₀ : ℝ} (hCg : 1 ≤ Cg)
    (hR₀ : 0 ≤ R₀) (k : Fin (H.eventCount + 1)) :
    H.EventSlabsDerivative Ctime (Cg * R₀) k ∨
      ∃ i : Fin H.eventCount, i.castSucc < k ∧
        ∃ (y : (H.stage i.castSucc).Carrier) (t : ℝ),
          t ∈ Ioo (H.time i.castSucc) (H.time i.succ) ∧
          R₀ < (H.toHistory.event i).incoming.flow.scalar t y ∧
          Cg * R₀ < (H.toHistory.event i).incoming.flow.scalar t y ∧
          (Ctime : ℝ) * (H.toHistory.event i).incoming.flow.scalar t y ^ 2 <
            |derivWithin (fun v => (H.toHistory.event i).incoming.flow.scalar v y) (Iic t) t| ∧
          H.EventSlabsDerivative Ctime
            (Cg * (H.toHistory.event i).incoming.flow.scalar t y) i.castSucc := by
  rcases eventSlabsDerivative_or_firstBadSlab_P6FF Ctime (Cg * R₀) k with h | h
  · exact Or.inl h
  · right
    obtain ⟨i, hik, ⟨y, t, ht, hq, hlt⟩, hpre⟩ := h
    have hR₀le : R₀ ≤ Cg * R₀ := le_mul_of_one_le_left hR₀ hCg
    have hlt₀ : R₀ < (H.toHistory.event i).incoming.flow.scalar t y := lt_of_le_of_lt hR₀le hq
    have hCg0 : 0 ≤ Cg := le_trans zero_le_one hCg
    refine ⟨i, hik, y, t, ht, hlt₀, hq, hlt, ?_⟩
    exact eventSlabsDerivative_threshold_mono_P6FF hpre
      (mul_le_mul_of_nonneg_left hlt₀.le hCg0)

/-- **slab 指标随时间单调**：`time js⁻ < s ≤ T < time jT⁺` ⇒ `js ≤ jT`。 -/
theorem slab_le_of_time_le_P6FF {js jT : Fin H.eventCount} {s T : ℝ}
    (hs : H.time js.castSucc < s) (hT : T < H.time jT.succ) (hsT : s ≤ T) : js ≤ jT := by
  by_contra h
  have hlt : jT < js := lt_of_not_ge h
  have hsc : jT.succ ≤ js.castSucc := Fin.succ_le_castSucc_iff.mpr hlt
  have htime : H.time jT.succ ≤ H.time js.castSucc := H.time_strictMono.monotone hsc
  linarith

/-- **selection 保持 clean prefix（PROVED）**：坏点 `(T, ·)` 在 slab `jT`，前缀在阈值 `q` 下干净；
selection 输出 `(s, ·)` 在 slab `js`、`s ≤ T`，阈值 `q ≤ Q`（例如 `Q = Cg·R(s,y)`，`R(s,y) ≥ R₀`）
⇒ 输出的前缀在阈值 `Q` 下干净。 -/
theorem eventSlabsDerivative_inherit_P6FF {Ctime : ℝ≥0} {q Q : ℝ} {js jT : Fin H.eventCount}
    {s T : ℝ} (h : H.EventSlabsDerivative Ctime q jT.castSucc)
    (hs : H.time js.castSucc < s) (hT : T < H.time jT.succ) (hsT : s ≤ T) (hq : q ≤ Q) :
    H.EventSlabsDerivative Ctime Q js.castSucc :=
  eventSlabsDerivative_threshold_mono_P6FF
    (eventSlabsDerivative_anti_P6FF h
      (Fin.castSucc_le_castSucc_iff.mpr (slab_le_of_time_le_P6FF hs hT hsT))) hq

/-- slab 内部时刻的 `activeStage`。 -/
theorem activeStage_eq_castSucc_of_mem_P6FF (j : Fin H.eventCount)
    (v : Icc (0 : ℝ) H.toHistory.horizon)
    (hv : (v : ℝ) ∈ Ioo (H.time j.castSucc) (H.time j.succ)) :
    H.toHistory.activeStage v = j.castSucc := by
  refine ObservedHistory.activeStage_eq_of_maximal _ v j.castSucc hv.1.le fun k' hk' => ?_
  have hk'lt : H.time k' < H.time j.succ := lt_of_le_of_lt hk' hv.2
  have : k' < j.succ := H.time_strictMono.lt_iff_lt.mp hk'lt
  exact Fin.le_castSucc_iff.mpr this

/-- **LOCALDT `hfirst` 的 Dt 半 ⇒ `EventSlabsDerivative`（PROVED 接线）**：ObservedHistory 形
`∀ v < σ, ∀ z, q < R(v,z) → HasSpatialCanonicalTimeControl`（区域无关）⇒ `time k ≤ σ` 的前缀 `k` 上
`EventSlabsDerivative Ctime q k`。 -/
theorem eventSlabsDerivative_of_hfirst_P6FF {eps C1 C2 : ℝ} {Ctime : ℝ≥0} {q σ : ℝ}
    (hfirst : ∀ v : Icc (0 : ℝ) H.toHistory.horizon, (v : ℝ) < σ →
      ∀ z : (H.toHistory.stageAt v).Carrier,
        q < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) z →
        H.toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z)
    (k : Fin (H.eventCount + 1)) (hk : H.time k ≤ σ) :
    H.EventSlabsDerivative Ctime q k := by
  intro j hj y t ht hR
  have hsk : j.succ ≤ k := Fin.castSucc_lt_iff_succ_le.mp hj
  have htσ : t < σ :=
    lt_of_lt_of_le ht.2 ((H.time_strictMono.monotone hsk).trans hk)
  have hhor : H.time j.succ ≤ H.horizon :=
    (H.time_strictMono.monotone (Fin.le_last _)).trans H.time_le_horizon
  have ht0 : (0 : ℝ) ≤ t :=
    le_trans (ObservedHistory.time_nonneg H.toHistory j.castSucc) ht.1.le
  let v : Icc (0 : ℝ) H.toHistory.horizon := ⟨t, ht0, ht.2.le.trans hhor⟩
  have hA : H.toHistory.activeStage v = j.castSucc :=
    activeStage_eq_castSucc_of_mem_P6FF j v ht
  have h2 : ∀ z : (H.stage (H.toHistory.activeStage v)).Carrier,
      q < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) t) z →
      H.time (H.toHistory.activeStage v) < t → t < H.horizon →
      |derivWithin (fun w => metricScalarAt (H.toHistory.stageMetric
          (H.toHistory.activeStage v) w) z) (Iic t) t| ≤
        Ctime * metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) t) z ^ 2 :=
    fun z hz => (hfirst v htσ z hz).2
  rw [hA] at h2
  have h3 := h2 y (by rw [ObservedHistory.stageMetric_castSucc_apply]; exact hR) ht.1
    (lt_of_lt_of_le ht.2 hhor)
  simp only [ObservedHistory.stageMetric_castSucc_apply] at h3
  exact h3

/-- 内核：stage 指标 `a = j⁻` 处、与 `y` HEq 的点，Dt 子句不成立。 -/
theorem not_dt_clause_of_heq_P6FF {Ctime : ℝ≥0} (j : Fin H.eventCount)
    (y : (H.stage j.castSucc).Carrier) {t : ℝ} (ht : t ∈ Ioo (H.time j.castSucc) (H.time j.succ))
    (hbad : (Ctime : ℝ) * (H.toHistory.event j).incoming.flow.scalar t y ^ 2 <
      |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t|)
    (hhor : t < H.horizon) :
    ∀ (a : Fin (H.eventCount + 1)) (_ha : a = j.castSucc) (z : (H.stage a).Carrier), HEq z y →
      ¬ (H.time a < t → t < H.horizon →
        |derivWithin (fun w => metricScalarAt (H.toHistory.stageMetric a w) z) (Iic t) t| ≤
          Ctime * metricScalarAt (H.toHistory.stageMetric a t) z ^ 2) := by
  intro a ha z hz hdt
  subst ha
  have hzy : z = y := eq_of_heq hz
  subst hzy
  have h := hdt ht.1 hhor
  simp only [ObservedHistory.stageMetric_castSucc_apply] at h
  exact absurd h (not_le.mpr hbad)

/-- **slab Dt 坏点 ⇒ ObservedHistory 层 CN 失效（PROVED）**：slab `j` 内部时刻 `t`（`< horizon`）的
Dt 坏点 `y` 给出 `v : Icc 0 horizon`（`v = t`，`activeStage v = j⁻`），与 `y` HEq 的点上
`¬ HasSpatialCanonicalTimeControl`（可作 selection 的 `hbad`）。 -/
theorem not_hasSpatialCanonicalTimeControl_of_slab_P6FF {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (j : Fin H.eventCount) (y : (H.stage j.castSucc).Carrier) {t : ℝ}
    (ht : t ∈ Ioo (H.time j.castSucc) (H.time j.succ))
    (hbad : (Ctime : ℝ) * (H.toHistory.event j).incoming.flow.scalar t y ^ 2 <
      |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (Iic t) t|)
    (hhor : t < H.horizon) :
    ∃ (v : Icc (0 : ℝ) H.toHistory.horizon), (v : ℝ) = t ∧
      H.toHistory.activeStage v = j.castSucc ∧
      ∀ z : (H.toHistory.stageAt v).Carrier, HEq z y →
        ¬ H.toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z := by
  have ht0 : (0 : ℝ) ≤ t :=
    le_trans (ObservedHistory.time_nonneg H.toHistory j.castSucc) ht.1.le
  let v : Icc (0 : ℝ) H.toHistory.horizon := ⟨t, ht0, hhor.le⟩
  have hA : H.toHistory.activeStage v = j.castSucc :=
    activeStage_eq_castSucc_of_mem_P6FF j v ht
  refine ⟨v, rfl, hA, fun z hz hgood => ?_⟩
  exact not_dt_clause_of_heq_P6FF j y ht hbad hhor (H.toHistory.activeStage v) hA z hz hgood.2

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

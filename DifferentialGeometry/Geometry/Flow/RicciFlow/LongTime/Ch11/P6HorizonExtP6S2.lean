import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalTimeControlPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreTower

/-!
# (H) 视界类 G1a：严格 horizon 扩张 + 闭端点识别 + 旧坏点 ⇒ 新坏点（S-CH11-P6BND2，后缀 `_P6S2`）

R-C11-5 D-12 (i)。设 `R : (K'.restrict a).SamePresentation K`（tower 的 `successor n` 恰是此形：
`(history (n+1)).restrict n ≃ history n`）。本文件把**旧 history `K` 的视界点**识别到 `K'`：
* 下标 / stage / 终端度量 / stage 初时刻 / 标量 / 左导数（`ext_activeStage_val_P6S2`、
  `ext_stageAt_eq_P6S2`、`ext_stageMetric_heq_P6S2`、`ext_time_active_P6S2`、`ext_scalar_P6S2`、
  `ext_derivWithin_P6S2`）；点按 `HEq` 对应（`ext_exists_point_P6S2`）；
* spatial witness 存在性等价（`ext_spatial_iff_P6S2`，`v ≤ K.horizon` 含视界端点）；
* **`Good_{K'} ⇒ Good_K`**（`ext_good_of_good_ext_P6S2`，`v ≤ K.horizon`；视界点上 `K` 的时间导数分量
  空真，故只用 `K'` 的 spatial 分量）与 **`Good_K ⇒ Good_{K'}`**（`ext_good_ext_of_good_lt_P6S2`，
  仅 `v < K.horizon`：此处两边时间导数分量相同；`v = K.horizon` 在 `K'` 里多出导数条件，不可逆）；
* **旧坏点 ⇒ 新坏点**（`ext_not_good_ext_of_not_good_P6S2`、`ext_not_good_of_not_spatial_P6S2`）与
  **归约** `ext_good_of_good_interior_P6S2` / `tower_good_of_good_succ_P6S2`：对 `K'` 证「时刻 ≤ 旧视界
  处处 Good」即得 `K` 的 Good（含视界点），所以 P6 反证里 `Kh n := history (n+1)`、坏点取时刻 ≤ n
  时，selection 输出的 `σ n ≤ Tn n ≤ n < n+1`，**(H) 类根本不出现**（见 `P6HorizonSelectP6S2`）。
`a < K'.horizon`（严格扩张）只在要把旧视界点变成 `K'` 内点时用（`ext_lt_horizon_P6S2`、
`tower_ext_lt_horizon_P6S2`）。无新 def / structure / 具名 Prop。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

section Congr

/-- stage 等 + 度量 `HEq` + 点 `HEq` ⇒ 标量相等。 -/
theorem scalar_congr_heq_P6S2 {P Q : OrientedThreeStage.{u}} (hPQ : P = Q) {g : P.Metric}
    {g' : Q.Metric} (hg : HEq g g') {x : P.Carrier} {x' : Q.Carrier} (hx : HEq x x') :
    metricScalarAt g x = metricScalarAt g' x' := by
  subst hPQ
  cases eq_of_heq hg
  cases eq_of_heq hx
  rfl

/-- stage 等 + 度量 `HEq` + 点 `HEq` ⇒ spatial witness 存在性等价。 -/
theorem spatial_iff_heq_P6S2 {P Q : OrientedThreeStage.{u}} (hPQ : P = Q) {g : P.Metric}
    {g' : Q.Metric} (hg : HEq g g') {x : P.Carrier} {x' : Q.Carrier} (hx : HEq x x')
    {eps C1 C2 : ℝ} :
    (∃ W : SpatialCanonicalWitness g eps C1 C2 x, W.capTubeHasNeckChart eps) ↔
      ∃ W : SpatialCanonicalWitness g' eps C1 C2 x', W.capTubeHasNeckChart eps := by
  subst hPQ
  cases eq_of_heq hg
  cases eq_of_heq hx
  exact Iff.rfl

end Congr

section Ident

variable {K K' : ObservedHistory.{u}} {a : Icc (0 : ℝ) K'.horizon}

/-- stage 域向左（到 stage 初时刻）封闭。 -/
theorem mem_stageDomain_of_le_P6S2 (H : ObservedHistory.{u}) (k : Fin (H.eventCount + 1))
    {τ v : ℝ} (hv : v ∈ H.stageDomain k) (h1 : H.time k ≤ τ) (h2 : τ ≤ v) :
    τ ∈ H.stageDomain k := by
  cases k using Fin.lastCases with
  | last =>
    simp only [stageDomain, Fin.lastCases_last, Set.mem_Icc] at hv ⊢
    exact ⟨h1, h2.trans hv.2⟩
  | cast i =>
    simp only [stageDomain, Fin.lastCases_castSucc, Set.mem_Ico] at hv ⊢
    exact ⟨h1, h2.trans_lt hv.2⟩

/-- 度量按 stage 指标搬运（指标相等 ⇒ `HEq`）。 -/
theorem stageMetric_heq_of_idx_P6S2 (H : ObservedHistory.{u}) {i i' : Fin (H.eventCount + 1)}
    (h : i = i') (τ : ℝ) : HEq (H.stageMetric i τ) (H.stageMetric i' τ) := by
  subst h
  rfl

/-- `restrict` 视界的下标：`K'.restrict a` 的 `activeStage t` 与 `K` 的 `activeStage` 对应。 -/
theorem ext_idx_K_P6S2 (R : (K'.restrict a).SamePresentation K) (v : Icc (0 : ℝ) K.horizon)
    (t : Icc (0 : ℝ) (K'.restrict a).horizon) (hvt : (t : ℝ) = v) :
    Fin.cast (congrArg (· + 1) R.count_eq) ((K'.restrict a).activeStage t) = K.activeStage v := by
  have h := SamePresentation.activeStage (K'.restrict a) R t
  rw [h]
  congr 1
  exact Subtype.ext hvt

theorem ext_idx_K'_P6S2 (t : Icc (0 : ℝ) (K'.restrict a).horizon) (v' : Icc (0 : ℝ) K'.horizon)
    (hvt : (t : ℝ) = v') :
    Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (K'.activeStage a).isLt) 1)
      ((K'.restrict a).activeStage t) = K'.activeStage v' := by
  rw [K'.restrict_activeStage a t]
  congr 1
  exact Subtype.ext hvt

/-- 闭端点识别（下标）：`K'` 在同一实时刻的 `activeStage` 与 `K` 的 `activeStage` 同一层。 -/
theorem ext_activeStage_val_P6S2 (R : (K'.restrict a).SamePresentation K)
    (v : Icc (0 : ℝ) K.horizon) (v' : Icc (0 : ℝ) K'.horizon) (hvv : (v' : ℝ) = v) :
    (K'.activeStage v').val = (K.activeStage v).val := by
  let t : Icc (0 : ℝ) (K'.restrict a).horizon := ⟨v, v.2.1, v.2.2.trans R.horizon_eq.symm.le⟩
  have h1 := congrArg Fin.val (ext_idx_K'_P6S2 (a := a) t v' hvv.symm)
  have h2 := congrArg Fin.val (ext_idx_K_P6S2 R v t rfl)
  exact h1.symm.trans h2

/-- 闭端点识别（stage）：同一实时刻 `K` 与 `K'` 的 `stageAt` 是同一个 stage。 -/
theorem ext_stageAt_eq_P6S2 (R : (K'.restrict a).SamePresentation K)
    (v : Icc (0 : ℝ) K.horizon) (v' : Icc (0 : ℝ) K'.horizon) (hvv : (v' : ℝ) = v) :
    K.stageAt v = K'.stageAt v' := by
  let t : Icc (0 : ℝ) (K'.restrict a).horizon := ⟨v, v.2.1, v.2.2.trans R.horizon_eq.symm.le⟩
  have h1 := K'.restrict_stageAt a t
  have h2 := R.stage_eq ((K'.restrict a).activeStage t)
  have h3 := congrArg K.stage (ext_idx_K_P6S2 R v t rfl)
  have h4 : K'.stageAt ⟨t.1, t.2.1, t.2.2.trans a.2.2⟩ = K'.stageAt v' :=
    congrArg K'.stageAt (Subtype.ext hvv.symm)
  exact (h3.symm.trans h2.symm).trans (h1.trans h4)

/-- 闭端点识别（度量）：时刻 `τ ∈ [time (activeStage v), v]` 上，`K` 与 `K'` 的当前 stage 度量
`HEq`。（`τ = v` 即终端度量。） -/
theorem ext_stageMetric_heq_P6S2 (R : (K'.restrict a).SamePresentation K)
    (v : Icc (0 : ℝ) K.horizon) (v' : Icc (0 : ℝ) K'.horizon) (hvv : (v' : ℝ) = v) {τ : ℝ}
    (hτ1 : K.time (K.activeStage v) ≤ τ) (hτ2 : τ ≤ v) :
    HEq (K.stageMetric (K.activeStage v) τ) (K'.stageMetric (K'.activeStage v') τ) := by
  let t : Icc (0 : ℝ) (K'.restrict a).horizon := ⟨v, v.2.1, v.2.2.trans R.horizon_eq.symm.le⟩
  have htime : (K'.restrict a).time ((K'.restrict a).activeStage t) = K.time (K.activeStage v) := by
    rw [R.time_eq, ext_idx_K_P6S2 R v t rfl]
  have hdom : τ ∈ (K'.restrict a).stageDomain ((K'.restrict a).activeStage t) :=
    mem_stageDomain_of_le_P6S2 _ _ ((K'.restrict a).activeStage_mem t) (htime ▸ hτ1) hτ2
  have h1 := R.metric_heq _ τ hdom
  have h2 := K'.restrict_stageMetric a _ τ hdom
  have h3 := stageMetric_heq_of_idx_P6S2 K (ext_idx_K_P6S2 R v t rfl) τ
  have h4 := stageMetric_heq_of_idx_P6S2 K' (ext_idx_K'_P6S2 (a := a) t v' hvv.symm) τ
  exact (h3.symm.trans (h1.symm.trans h2)).trans h4

/-- 闭端点识别（stage 初时刻）。 -/
theorem ext_time_active_P6S2 (R : (K'.restrict a).SamePresentation K)
    (v : Icc (0 : ℝ) K.horizon) (v' : Icc (0 : ℝ) K'.horizon) (hvv : (v' : ℝ) = v) :
    K.time (K.activeStage v) = K'.time (K'.activeStage v') := by
  let t : Icc (0 : ℝ) (K'.restrict a).horizon := ⟨v, v.2.1, v.2.2.trans R.horizon_eq.symm.le⟩
  have h1 := R.time_eq ((K'.restrict a).activeStage t)
  rw [ext_idx_K_P6S2 R v t rfl] at h1
  rw [← ext_idx_K'_P6S2 (a := a) t v' hvv.symm]
  exact h1.symm

/-- 终端标量：同一实时刻、`HEq` 的点上，`K` 与 `K'` 的当前 stage 标量相等。 -/
theorem ext_scalar_P6S2 (R : (K'.restrict a).SamePresentation K)
    (v : Icc (0 : ℝ) K.horizon) (v' : Icc (0 : ℝ) K'.horizon) (hvv : (v' : ℝ) = v) {τ : ℝ}
    (hτ1 : K.time (K.activeStage v) ≤ τ) (hτ2 : τ ≤ v)
    {z : (K.stageAt v).Carrier} {z' : (K'.stageAt v').Carrier} (hz : HEq z z') :
    metricScalarAt (K.stageMetric (K.activeStage v) τ) z =
      metricScalarAt (K'.stageMetric (K'.activeStage v') τ) z' :=
  scalar_congr_heq_P6S2 (ext_stageAt_eq_P6S2 R v v' hvv)
    (ext_stageMetric_heq_P6S2 R v v' hvv hτ1 hτ2) hz

/-- 严格过去时刻（`time (activeStage v) < v`）的左导数两边相等。 -/
theorem ext_derivWithin_P6S2 (R : (K'.restrict a).SamePresentation K)
    (v : Icc (0 : ℝ) K.horizon) (v' : Icc (0 : ℝ) K'.horizon) (hvv : (v' : ℝ) = v)
    (hage : K.time (K.activeStage v) < v)
    {z : (K.stageAt v).Carrier} {z' : (K'.stageAt v').Carrier} (hz : HEq z z') :
    derivWithin (fun τ => metricScalarAt (K.stageMetric (K.activeStage v) τ) z)
        (Iic (v : ℝ)) v =
      derivWithin (fun τ => metricScalarAt (K'.stageMetric (K'.activeStage v') τ) z')
        (Iic (v' : ℝ)) v' := by
  rw [hvv]
  have hev : (fun τ => metricScalarAt (K.stageMetric (K.activeStage v) τ) z) =ᶠ[𝓝[≤] (v : ℝ)]
      (fun τ => metricScalarAt (K'.stageMetric (K'.activeStage v') τ) z') := by
    filter_upwards [Ioc_mem_nhdsLE hage] with τ hτ
    exact ext_scalar_P6S2 R v v' hvv hτ.1.le hτ.2 hz
  exact hev.derivWithin_eq (ext_scalar_P6S2 R v v' hvv hage.le le_rfl hz)

/-- **闭端点识别（spatial）**：`v ≤ K.horizon` 上，`K` 与 `K'` 的 spatial witness 存在性等价。 -/
theorem ext_spatial_iff_P6S2 (R : (K'.restrict a).SamePresentation K)
    (v : Icc (0 : ℝ) K.horizon) (v' : Icc (0 : ℝ) K'.horizon) (hvv : (v' : ℝ) = v)
    {z : (K.stageAt v).Carrier} {z' : (K'.stageAt v').Carrier} (hz : HEq z z')
    {eps C1 C2 : ℝ} :
    (∃ W : SpatialCanonicalWitness (K.stageMetric (K.activeStage v) v) eps C1 C2 z,
        W.capTubeHasNeckChart eps) ↔
      ∃ W : SpatialCanonicalWitness (K'.stageMetric (K'.activeStage v') v') eps C1 C2 z',
        W.capTubeHasNeckChart eps := by
  rw [hvv]
  exact spatial_iff_heq_P6S2 (ext_stageAt_eq_P6S2 R v v' hvv)
    (ext_stageMetric_heq_P6S2 R v v' hvv (K.activeStage_time_le v) le_rfl) hz

/-- 旧视界（`K.horizon = a`）不超过 `K'.horizon`。 -/
theorem ext_horizon_le_P6S2 (R : (K'.restrict a).SamePresentation K) :
    K.horizon ≤ K'.horizon :=
  R.horizon_eq.symm.le.trans a.2.2

/-- 严格 horizon 扩张：`a < K'.horizon` 时旧视界上的点在 `K'` 里是视界内点。 -/
theorem ext_lt_horizon_P6S2 (R : (K'.restrict a).SamePresentation K) (hext : (a : ℝ) < K'.horizon)
    (v : Icc (0 : ℝ) K.horizon) (v' : Icc (0 : ℝ) K'.horizon) (hvv : (v' : ℝ) = v) :
    (v' : ℝ) < K'.horizon := by
  rw [hvv]
  exact v.2.2.trans_lt (R.horizon_eq.symm.le.trans_lt hext)

/-- **`Good_{K'} ⇒ Good_K`**（`v ≤ K.horizon`，含视界端点）：`K'` 的完整 Good 拉回旧 history。 -/
theorem ext_good_of_good_ext_P6S2 (R : (K'.restrict a).SamePresentation K)
    (v : Icc (0 : ℝ) K.horizon) (v' : Icc (0 : ℝ) K'.horizon) (hvv : (v' : ℝ) = v)
    {z : (K.stageAt v).Carrier} {z' : (K'.stageAt v').Carrier} (hz : HEq z z')
    {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (h : K'.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v' z') :
    K.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z := by
  refine ⟨(ext_spatial_iff_P6S2 R v v' hvv hz).mpr h.1, fun hage hlt => ?_⟩
  have hlt' : (v' : ℝ) < K'.horizon := by
    rw [hvv]
    exact hlt.trans_le (ext_horizon_le_P6S2 R)
  have h2 := h.2 (by rw [hvv, ← ext_time_active_P6S2 R v v' hvv]; exact hage) hlt'
  rw [hvv] at h2
  rw [ext_derivWithin_P6S2 R v v' hvv hage hz, ext_scalar_P6S2 R v v' hvv hage.le le_rfl hz]
  rw [hvv]
  exact h2

/-- **`Good_K ⇒ Good_{K'}`**（严格 `v < K.horizon`）：视界内部时刻两边完整 Good 等价。 -/
theorem ext_good_ext_of_good_lt_P6S2 (R : (K'.restrict a).SamePresentation K)
    (v : Icc (0 : ℝ) K.horizon) (v' : Icc (0 : ℝ) K'.horizon) (hvv : (v' : ℝ) = v)
    (hlt : (v : ℝ) < K.horizon)
    {z : (K.stageAt v).Carrier} {z' : (K'.stageAt v').Carrier} (hz : HEq z z')
    {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (h : K.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z) :
    K'.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v' z' := by
  refine ⟨(ext_spatial_iff_P6S2 R v v' hvv hz).mp h.1, fun hage _ => ?_⟩
  have hage' : K.time (K.activeStage v) < v := by
    rw [ext_time_active_P6S2 R v v' hvv]
    rw [hvv] at hage
    exact hage
  have h2 := h.2 hage' hlt
  have e1 := ext_derivWithin_P6S2 R v v' hvv hage' hz
  rw [hvv] at e1
  have e2 := ext_scalar_P6S2 R v v' hvv hage'.le le_rfl hz
  rw [hvv, ← e1, ← e2]
  exact h2

/-- **hbad 搬运（闭端点）**：旧点处 `¬ spatial witness` ⇒ 扩张 history 里同一点 `¬ Good`。
（`Good_{K'} ⇒ spatial_{K'} ⇒ spatial_K`；`K` 的视界点上 `¬Good_K ⟺ ¬ spatial`，故旧视界坏点
是 `K'` 的坏点。） -/
theorem ext_not_good_of_not_spatial_P6S2 (R : (K'.restrict a).SamePresentation K)
    (v : Icc (0 : ℝ) K.horizon) (v' : Icc (0 : ℝ) K'.horizon) (hvv : (v' : ℝ) = v)
    {z : (K.stageAt v).Carrier} {z' : (K'.stageAt v').Carrier} (hz : HEq z z')
    {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hbad : ¬ ∃ W : SpatialCanonicalWitness (K.stageMetric (K.activeStage v) v) eps C1 C2 z,
        W.capTubeHasNeckChart eps) :
    ¬ K'.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v' z' :=
  fun h => hbad ((ext_spatial_iff_P6S2 R v v' hvv hz).mpr h.1)

/-- 旧点在 `K'` 里的对应点（stage 相等 ⇒ `cast`）。 -/
theorem ext_exists_point_P6S2 (R : (K'.restrict a).SamePresentation K)
    (v : Icc (0 : ℝ) K.horizon) (v' : Icc (0 : ℝ) K'.horizon) (hvv : (v' : ℝ) = v)
    (z : (K.stageAt v).Carrier) : ∃ z' : (K'.stageAt v').Carrier, HEq z z' :=
  ⟨cast (congrArg OrientedThreeStage.Carrier (ext_stageAt_eq_P6S2 R v v' hvv)) z,
    (cast_heq _ _).symm⟩

/-- **旧坏点 ⇒ 新坏点**（任意 `v ≤ K.horizon`，含视界端点）：`K` 在 `(v, z)` 不 Good ⇒ `K'` 在
同一实时刻、`HEq` 点不 Good。 -/
theorem ext_not_good_ext_of_not_good_P6S2 (R : (K'.restrict a).SamePresentation K)
    (v : Icc (0 : ℝ) K.horizon) (v' : Icc (0 : ℝ) K'.horizon) (hvv : (v' : ℝ) = v)
    {z : (K.stageAt v).Carrier} {z' : (K'.stageAt v').Carrier} (hz : HEq z z')
    {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hbad : ¬ K.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z) :
    ¬ K'.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v' z' :=
  fun h => hbad (ext_good_of_good_ext_P6S2 R v v' hvv hz h)

/-- **归约（旧视界类的消除）**：`K'` 在时刻 `≤ K.horizon` 处处 Good ⇒ `K` 处处 Good
（含 `K.horizon` 上的视界点）。故只需对 `K'` 证「内点时刻处处 Good」。 -/
theorem ext_good_of_good_interior_P6S2 (R : (K'.restrict a).SamePresentation K)
    {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hint : ∀ (v' : Icc (0 : ℝ) K'.horizon), (v' : ℝ) ≤ K.horizon → ∀ z' : (K'.stageAt v').Carrier,
      K'.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v' z')
    (v : Icc (0 : ℝ) K.horizon) (z : (K.stageAt v).Carrier) :
    K.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z := by
  let v' : Icc (0 : ℝ) K'.horizon := ⟨v, v.2.1, v.2.2.trans (ext_horizon_le_P6S2 R)⟩
  obtain ⟨z', hz⟩ := ext_exists_point_P6S2 R v v' rfl z
  exact ext_good_of_good_ext_P6S2 R v v' rfl hz (hint v' v.2.2 z')

end Ident

section Tower

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (T : RetainedCoreObservationTower P g)

/-- tower 的 `successor n` 恰是闭端点识别的输入形：`(history (n+1)).restrict n ≃ history n`，
`n < n + 1`（严格 horizon 扩张）。 -/
theorem tower_ext_lt_horizon_P6S2 (n : ℕ) :
    (n : ℝ) < (T.history (n + 1)).toHistory.horizon := by
  change (n : ℝ) < (T.history (n + 1)).horizon
  rw [T.horizon_eq]
  push_cast
  linarith

/-- **tower 归约**：`history (n+1)` 在时刻 `≤ n` 处处 Good ⇒ `history n` 处处 Good
（旧 tower 项的视界类坏点在 `history (n+1)` 里是严格内点）。 -/
theorem tower_good_of_good_succ_P6S2 (n : ℕ) {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hint : ∀ (v' : Icc (0 : ℝ) (T.history (n + 1)).toHistory.horizon), (v' : ℝ) ≤ n →
      ∀ z' : ((T.history (n + 1)).toHistory.stageAt v').Carrier,
      (T.history (n + 1)).toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v' z')
    (v : Icc (0 : ℝ) (T.history n).toHistory.horizon)
    (z : ((T.history n).toHistory.stageAt v).Carrier) :
    (T.history n).toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z :=
  ext_good_of_good_interior_P6S2 (T.successor n) (fun v' hv' z' => hint v' (by
    simpa only [RetainedCoreHistory.toHistory, T.horizon_eq] using hv') z') v z

end Tower

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BufferedTransferP6ST2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LeftBadSequenceCXST
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerInductionStep

/-!
# S-c G2：用 buffered transfer 替换 `hstab`（O-CH11-STAB2 G2，后缀 `_P6ST2`）

`P6StagePostCoverP6S2.stage_class_left_bad_P6S2` 的 `hstab`（左邻域全 Good ⇒ 同常数 post witness，D-9 判为缺
margins / footprint）在本文件被换成 **footprint binder `hfoot`**：只在实际 post 点 `y` 的 crossing 对 `(p', q)`
（`HEq y q`）上要求 `BufferedFootprintData_P6ST2`（纯 event 几何，不含左侧 Good）。左侧二分改用 **margin 版**
fine 谓词 `∃ W : SCW ηfine C1 C2, chart ∧ HasMargins m`：左邻域全 fine-margin-Good ⇒ 合同的 `fine` 字段
（`v n → s` 落入邻域，slab 内 history 度量 = event incoming 度量）⇒ G1 transfer ⇒ 目标层 witness，与
`hsel : ¬ Good_{ηout, C1out, C2out}` 矛盾；否则得任意近的左侧 fine-margin 坏点（`LeftBadAt_CXST` 形）。
精度：`hsel` 在 `ηout`，左坏点在 `ηfine ≤ neckModelTolerance (ηout/2)`（带 margins `m`）；常数 `2C1 ≤ C1out`、
`1000C2 ≤ C2out` 在 selection 之前固定。

序列版（实际高曲率 stage 序列，D-10 减弱方向）：`hfoot` 只需 `∀ᶠ n`（eventual 版）或 `∃ᶠ n`（subsequence 版，
`extraction_of_frequently_atTop` 抽子列，再接 CX-STAGE `scaled_left_bad_sequence_CXST` 得
`Qₙ(σₙ − vₙ) → 0`）。
无新 def / 具名 Prop；fine-margin 谓词逐处内联。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn

/-- fine-margin witness 存在性在 stage / 度量 / 点的 `HEq` 下不变。 -/
theorem fineMargin_iff_heq_P6ST2 {P Q : OrientedThreeStage.{u}} (hPQ : P = Q) {g : P.Metric}
    {g' : Q.Metric} (hg : HEq g g') {x : P.Carrier} {x' : Q.Carrier} (hx : HEq x x')
    {eps C1 C2 m : ℝ} :
    (∃ W : SpatialCanonicalWitness g eps C1 C2 x, W.capTubeHasNeckChart eps ∧ W.HasMargins m) ↔
      ∃ W : SpatialCanonicalWitness g' eps C1 C2 x',
        W.capTubeHasNeckChart eps ∧ W.HasMargins m := by
  subst hPQ
  cases eq_of_heq hg
  cases eq_of_heq hx
  exact Iff.rfl

namespace ObservedHistory

/-- slab 内的时刻属于 `[0, horizon]`。 -/
theorem mem_Icc_of_mem_slab_P6ST2 (H : ObservedHistory.{u}) (i : Fin H.eventCount) {t : ℝ}
    (ht : t ∈ Ioo (H.time i.castSucc) (H.time i.succ)) : t ∈ Icc (0 : ℝ) H.horizon := by
  have h0 : 0 ≤ H.time i.castSucc := by
    rw [← H.time_zero]
    exact H.time_strictMono.monotone (Fin.zero_le _)
  have h1 : H.time i.succ ≤ H.horizon :=
    (H.time_strictMono.monotone (Fin.le_last _)).trans H.time_le_horizon
  exact ⟨h0.trans ht.1.le, ht.2.le.trans h1⟩

/-- slab `[time castSucc, time succ)` 内 `activeStage = castSucc`。 -/
theorem activeStage_eq_castSucc_P6ST2 (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (t : Icc (0 : ℝ) H.horizon) (h0 : H.time i.castSucc ≤ t) (h1 : (t : ℝ) < H.time i.succ) :
    H.activeStage t = i.castSucc := by
  refine H.activeStage_eq_of_maximal t i.castSucc h0 (fun k hk => ?_)
  by_contra hlt
  have hsk : i.succ ≤ k := Fin.castSucc_lt_iff_succ_le.mp (not_le.mp hlt)
  exact absurd (lt_of_lt_of_le h1 ((H.time_strictMono.monotone hsk).trans hk)) (lt_irrefl _)

/-- **slab 换元**：slab 内时刻 `t`，history 层 fine-margin witness（`stageMetric (activeStage t) t`、点 `z`）⟺
event 层（`(event i).incoming.flow.base.metric t`、`HEq z z'`）。 -/
theorem fineMargin_slab_iff_P6ST2 {H : ObservedHistory.{u}} (i : Fin H.eventCount)
    {t : Icc (0 : ℝ) H.horizon} (h0 : H.time i.castSucc ≤ t) (h1 : (t : ℝ) < H.time i.succ)
    {z : (H.stageAt t).Carrier} {z' : (H.stage i.castSucc).Carrier} (hz : HEq z z')
    {eps C1 C2 m : ℝ} :
    (∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) eps C1 C2 z,
        W.capTubeHasNeckChart eps ∧ W.HasMargins m) ↔
      ∃ W : SpatialCanonicalWitness ((H.event i).incoming.flow.base.metric t) eps C1 C2 z',
        W.capTubeHasNeckChart eps ∧ W.HasMargins m := by
  have hact := H.activeStage_eq_castSucc_P6ST2 i t h0 h1
  have hg : HEq (H.stageMetric (H.activeStage t) t) ((H.event i).incoming.flow.base.metric t) :=
    (stageMetric_heq_of_idx_P6S2 H hact _).trans (heq_of_eq (stageMetric_castSucc_apply i _))
  exact fineMargin_iff_heq_P6ST2 (congrArg H.stage hact) hg hz

end ObservedHistory

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}

/-- **G2 主定理（`hstab` → `hfoot`）**：stage 时刻 `σ = time i.succ` 的 post 点 `y` 若
`¬ Good_{ηout, C1out, C2out}`，则 `σ` 左侧任意近处有 **fine-margin 坏点**（无 `ηfine` 精度、带 margins `m` 的
witness），`LeftBadAt_CXST` 形。输入：S-a（`hcapW`，目标层）与 `hfoot`（只在 `y` 的 crossing 对上的
`BufferedFootprintData_P6ST2`）；左邻域全 fine-margin-Good 的支经 G1 transfer 与 `hsel` 矛盾。 -/
theorem stage_class_left_bad_P6ST2 (R : GeometricCutoffRecord H i p)
    {ηfine ηout C1 C2 m C1out C2out : ℝ} {k : ℕ} {Ctime : ℝ≥0}
    (h1 : 2 * C1 ≤ C1out) (h2 : 1000 * C2 ≤ C2out) (hle : ηfine ≤ neckModelTolerance (ηout / 2))
    (hcapW : ∀ (b : (H.event i).RetainedBoundaryIndex) (x : ThreeBall),
      ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ηout C1out C2out
        ((R.static b).inclusion ((R.static b).witness.cap x)), W.capTubeHasNeckChart ηout)
    {y : (H.stageAt (H.stageTime i.succ)).Carrier}
    (hfoot : ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
      (H.event i).RegularCrossing p' q →
      Nonempty ((H.event i).BufferedFootprintData_P6ST2 p' q ηout C1 C2 m k))
    (hsel : ¬ H.HasSpatialCanonicalTimeControl ηout C1out C2out Ctime (H.stageTime i.succ) y) :
    LeftBadAt_CXST (fun v : Icc (0 : ℝ) H.horizon => (v : ℝ))
      (fun v z => ¬ ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) ηfine C1 C2 z,
        W.capTubeHasNeckChart ηfine ∧ W.HasMargins m) (H.time i.succ) := by
  have hP : H.stageAt (H.stageTime i.succ) = H.stage i.succ :=
    congrArg H.stage (H.activeStage_stageTime i.succ)
  obtain ⟨q, hq⟩ : ∃ q : (H.stage i.succ).Carrier, HEq y q :=
    ⟨cast (congrArg OrientedThreeStage.Carrier hP) y, (cast_heq _ _).symm⟩
  have hg : HEq (H.stageMetric (H.activeStage (H.stageTime i.succ)) (H.stageTime i.succ))
      (H.event i).outputMetric :=
    (ObservedHistory.stageMetric_heq_of_idx_P6S2 H (H.activeStage_stageTime i.succ) _).trans
      (heq_of_eq ((H.stageMetric_initial i.succ).trans (H.event_output i).symm))
  rcases R.postCover_P6S2 q with ⟨b, x, hbx⟩ | ⟨p', hcross⟩
  · exact (R.false_of_stage_cap_P6S2 hcapW b x (hq.trans (heq_of_eq hbx)) hsel).elim
  by_cases hbad : LeftBadAt_CXST (fun v : Icc (0 : ℝ) H.horizon => (v : ℝ))
      (fun v z => ¬ ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) ηfine C1 C2 z,
        W.capTubeHasNeckChart ηfine ∧ W.HasMargins m) (H.time i.succ)
  · exact hbad
  exfalso
  obtain ⟨δ, hδ, hgood⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ v : Icc (0 : ℝ) H.horizon,
      H.time i.succ - δ < v → (v : ℝ) < H.time i.succ → ∀ z : (H.stageAt v).Carrier,
        ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) ηfine C1 C2 z,
          W.capTubeHasNeckChart ηfine ∧ W.HasMargins m := by
    unfold LeftBadAt_CXST at hbad
    push Not at hbad
    obtain ⟨δ, hδ, h⟩ := hbad
    exact ⟨δ, hδ, fun v hv1 hv2 z => h v z hv1 hv2⟩
  obtain ⟨D⟩ := hfoot p' q hq hcross
  have hfine : ∀ᶠ n in atTop, ∃ W : SpatialCanonicalWitness
      ((H.event i).incoming.flow.base.metric (D.v n)) ηfine C1 C2 p',
        W.capTubeHasNeckChart ηfine ∧ W.HasMargins m := by
    filter_upwards [D.v_tendsto.eventually (lt_mem_nhds (sub_lt_self (H.time i.succ) hδ))]
      with n hn
    have hIcc := H.mem_Icc_of_mem_slab_P6ST2 i (D.v_mem n)
    let t : Icc (0 : ℝ) H.horizon := ⟨D.v n, hIcc⟩
    have ht0 : H.time i.castSucc ≤ t := (D.v_mem n).1.le
    have ht1 : (t : ℝ) < H.time i.succ := (D.v_mem n).2
    have hact := H.activeStage_eq_castSucc_P6ST2 i t ht0 ht1
    have hPt : H.stageAt t = H.stage i.castSucc := congrArg H.stage hact
    obtain ⟨z, hz⟩ : ∃ z : (H.stageAt t).Carrier, HEq z p' :=
      ⟨cast (congrArg OrientedThreeStage.Carrier hPt).symm p', cast_heq _ _⟩
    exact (ObservedHistory.fineMargin_slab_iff_P6ST2 i ht0 ht1 hz).mp (hgood t hn ht1 z)
  obtain ⟨W, hW⟩ := MetricCutCapEvent.spatialWitness_of_bufferedTransfer_P6ST2
    (MetricCutCapEvent.BufferedTransferData_P6ST2.ofFootprint_P6ST2 D hle hfine) h1 h2
  exact hsel ((ObservedHistory.hasSpatialCanonicalTimeControl_iff_of_boundary_P6S
    (Or.inl (H.boundary_of_stageTime_P6S i.succ))).mpr
      ((ObservedHistory.spatial_iff_heq_P6S2 hP hg hq).mpr ⟨W, hW⟩))

end GeometricCutoffRecord

namespace ObservedHistory

variable {Kh : ℕ → ObservedHistory.{u}} {i : ∀ n, Fin (Kh n).eventCount}
  {pp : ℕ → CutoffParameters}

/-- **eventual 版（实际 stage 序列）**：`hfoot` 只需 eventually（在实际 post 点 `y n` 的 crossing 对上）⇒
eventually 每个 stage 左侧有任意近的 fine-margin 坏点。 -/
theorem stage_class_left_bad_eventually_P6ST2
    (R : ∀ n, GeometricCutoffRecord (Kh n) (i n) (pp n))
    {ηfine ηout C1 C2 m C1out C2out : ℝ} {k : ℕ} {Ctime : ℝ≥0}
    (h1 : 2 * C1 ≤ C1out) (h2 : 1000 * C2 ≤ C2out) (hle : ηfine ≤ neckModelTolerance (ηout / 2))
    (hcapW : ∀ n (b : ((Kh n).event (i n)).RetainedBoundaryIndex) (x : ThreeBall),
      ∃ W : SpatialCanonicalWitness ((Kh n).event (i n)).outputMetric ηout C1out C2out
        (((R n).static b).inclusion (((R n).static b).witness.cap x)), W.capTubeHasNeckChart ηout)
    (y : ∀ n, ((Kh n).stageAt ((Kh n).stageTime (i n).succ)).Carrier)
    (hfoot : ∀ᶠ n in atTop, ∀ (p' : ((Kh n).stage (i n).castSucc).Carrier)
      (q : ((Kh n).stage (i n).succ).Carrier), HEq (y n) q →
      ((Kh n).event (i n)).RegularCrossing p' q →
      Nonempty (((Kh n).event (i n)).BufferedFootprintData_P6ST2 p' q ηout C1 C2 m k))
    (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ηout C1out C2out Ctime
      ((Kh n).stageTime (i n).succ) (y n)) :
    ∀ᶠ n in atTop, LeftBadAt_CXST (fun v : Icc (0 : ℝ) (Kh n).horizon => (v : ℝ))
      (fun v z => ¬ ∃ W : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v)
        ηfine C1 C2 z, W.capTubeHasNeckChart ηfine ∧ W.HasMargins m) ((Kh n).time (i n).succ) :=
  hfoot.mono fun n hn =>
    (R n).stage_class_left_bad_P6ST2 h1 h2 hle (hcapW n) hn (hsel n)

/-- **subsequence 版（实际高曲率 stage 序列）**：`hfoot` 只需 frequently ⇒ 抽子列 `φ`，沿子列每个 stage
有 slab 内 fine-margin 坏点 `(v n, z n)`，且对任意正尺度 `Q` 有 `Q (φ n) · (σ_{φ n} − v n) → 0`
（CX-STAGE `scaled_left_bad_sequence_CXST`）。 -/
theorem stage_class_left_bad_subseq_P6ST2
    (R : ∀ n, GeometricCutoffRecord (Kh n) (i n) (pp n))
    {ηfine ηout C1 C2 m C1out C2out : ℝ} {k : ℕ} {Ctime : ℝ≥0}
    (h1 : 2 * C1 ≤ C1out) (h2 : 1000 * C2 ≤ C2out) (hle : ηfine ≤ neckModelTolerance (ηout / 2))
    (hcapW : ∀ n (b : ((Kh n).event (i n)).RetainedBoundaryIndex) (x : ThreeBall),
      ∃ W : SpatialCanonicalWitness ((Kh n).event (i n)).outputMetric ηout C1out C2out
        (((R n).static b).inclusion (((R n).static b).witness.cap x)), W.capTubeHasNeckChart ηout)
    (y : ∀ n, ((Kh n).stageAt ((Kh n).stageTime (i n).succ)).Carrier)
    (hfoot : ∃ᶠ n in atTop, ∀ (p' : ((Kh n).stage (i n).castSucc).Carrier)
      (q : ((Kh n).stage (i n).succ).Carrier), HEq (y n) q →
      ((Kh n).event (i n)).RegularCrossing p' q →
      Nonempty (((Kh n).event (i n)).BufferedFootprintData_P6ST2 p' q ηout C1 C2 m k))
    (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ηout C1out C2out Ctime
      ((Kh n).stageTime (i n).succ) (y n)) {Q : ℕ → ℝ} (hQ : ∀ n, 0 < Q n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (v : ∀ n, Icc (0 : ℝ) (Kh (φ n)).horizon) (z : ∀ n, ((Kh (φ n)).stageAt (v n)).Carrier),
        (∀ n, (Kh (φ n)).time (i (φ n)).castSucc < (v n : ℝ) ∧
          (v n : ℝ) < (Kh (φ n)).time (i (φ n)).succ ∧
          ¬ ∃ W : SpatialCanonicalWitness ((Kh (φ n)).stageMetric ((Kh (φ n)).activeStage (v n))
            (v n)) ηfine C1 C2 (z n), W.capTubeHasNeckChart ηfine ∧ W.HasMargins m) ∧
        Tendsto (fun n => Q (φ n) * ((Kh (φ n)).time (i (φ n)).succ - (v n : ℝ))) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hfoot
  refine ⟨φ, hφ, ?_⟩
  exact scaled_left_bad_sequence_CXST
    (fun n => (R (φ n)).stage_class_left_bad_P6ST2 h1 h2 hle (hcapW (φ n)) (hφP n) (hsel (φ n)))
    (fun n => (Kh (φ n)).time_strictMono (Fin.castSucc_lt_succ (i := i (φ n))))
    (fun n => hQ (φ n))

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

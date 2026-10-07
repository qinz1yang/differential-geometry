import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventRetainedInterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BoundaryCasesP6S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HorizonExtP6S2

/-!
# (S) stage 时刻类 G2：post-cover 二分 + 左侧逻辑二分 + S-a / S-b / S-c（S-CH11-P6BND2，后缀 `_P6S2`）

R-C11-5 D-13。坏点 `σ n = time (i n).succ`（stage 初时刻）、post 点 `y n`（stage `i.succ`），`hsel : ¬ Good`
——在该点 `Good ⟺ spatial witness`（时间导数分量空真，`P6BoundaryCasesP6S`）。

* **post-cover**（纯拓扑，`MetricCutCapEvent.post_cover_event_P6S2`）：post 点 `q` 要么在某个 cap 的像里
  （`presentation (cap b x) = inl q`，含 cap 边界球面 = collar 与 cap 的交），要么在 `interior (range oldOutput)`
  （⇒ 某个 `RegularCrossing` 的新侧像，`exists_regularCrossing_of_mem_interior_oldOutput`）。覆盖来自
  `Capping.exhaustive` + cap 像闭（有限个紧集）+ `old = retainedCore`；collar / transition 区的点要么是
  `old` 的内点要么落在 cap 的闭像里，不会漏。records 版 `GeometricCutoffRecord.postCover_P6S2`：cap 支 =
  `(static b).inclusion ((static b).witness.cap x)`（retained cap 的标准帽模型点，`static b` 带完整定量
  witness 与 `inclusion_metric`；`retainedBoundary_of_cap_P6S2`：cap 像里有 `Q` 的点 ⇒ 该 cap 是 retained）。
* **左侧逻辑二分**：`left_dichotomy_P6S2`（实数层）/ `left_dichotomy_good_P6S2`（history 层）：`σ` 左侧要么任意
  近处有坏点，要么某个左邻域处处 Good。
* **S-a**（records 的 cap-model witness 收口）：`spatial_of_post_cap_P6S2` / `false_of_stage_cap_P6S2`：
  `hcapW`（records 输出的**完整定量 witness，含 `capTubeHasNeckChart`**）⇒ cap-model 支的 post 点有 spatial
  witness，与 `hsel` 矛盾。
* **S-b**（左移重跑的参数）：`leftShift_params_P6S2`（算术：阈值系数 `8`——`4R ≤ 8R'`；`L' = L/2`；
  `σ − σ' + L'²/R' ≤ L²/R`；`L'/√R' ≤ (3/4)·L/√R` 留 `L/(4√R)` 吸收种子中心位移）、`eventually_half_le_P6S2`
  （`R'/R → 1` ⇒ eventually `R/2 ≤ R'`）、`rerun_dist_le_P6S2`、**`leftShift_rerun_P6S2`**（`hgood` 形：
  原 selection Good 区 ⇒ 重跑所需的 `hgood`，窗口 `σ' − L'²/R'`、距离 `d_{σ'} + L'/√R'`、阈值 `8R'`）。
* **S-c** 留显式 binder `hstab`（stability contract，D-13 原文形）：**不证**。共同 footprint 与 pre/post `C^k`
  收敛已在 event 数据里（`terminal.converges`、`old_metric_eq`）；OPEN 的是「左 Good ⇒ 同常数极限 witness」
  需要的带 domain 余量的更细 witness（见 R-C11-5 Q4(b-S)）。
* **装配 / consumer**：`stage_class_left_bad_P6S2`（S-a + 二分 + S-c binder ⇒ 左侧任意近处有坏点）与
  `left_bad_sequence_of_stage_class_P6S2`（stage 类序列 ⇒ 左侧 event 内部坏点序列
  `v n ∈ (time castSucc, time succ)`、`time succ − v n < 1/(n+1)`，event 内部主形的输入形）。
无新 def / structure / 具名 Prop。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

/-- **post-cover（event 层，纯拓扑）**：post 点 `q` 要么在某个 cap 的像里（`presentation (cap b x) = inl q`，
含 cap 边界球面 = collar 与 cap 的交），要么在 `interior (range oldOutput)`（于是由
`exists_regularCrossing_of_mem_interior_oldOutput` 是某个 `RegularCrossing` 的新侧像）。覆盖由
`Capping.exhaustive` + cap 像闭（有限个紧集）+ `old = retainedCore` 给出。 -/
theorem post_cover_event_P6S2 (hold : E.old = E.transition.trace.retainedCore) (q : Q.Carrier) :
    (∃ (b : E.transition.trace.tubes.Boundary) (x : ThreeBall),
        E.transition.trace.presentation (E.transition.trace.capping.cap b x) = Sum.inl q) ∨
      ∃ p : P.Carrier, E.RegularCrossing p q := by
  classical
  by_cases hcap : ∃ (b : E.transition.trace.tubes.Boundary) (x : ThreeBall),
      E.transition.trace.presentation (E.transition.trace.capping.cap b x) = Sum.inl q
  · exact Or.inl hcap
  right
  refine E.exists_regularCrossing_of_mem_interior_oldOutput q ?_
  have : CompactSpace ThreeBall := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let T := E.transition.trace
  let g : Q.Carrier → E.capped.Carrier := fun q' => T.presentation.symm (Sum.inl q')
  have hg : Continuous g := T.presentation.symm.continuous.comp continuous_inl
  let C : Set E.capped.Carrier := ⋃ b : T.tubes.Boundary, range (T.capping.cap b)
  have hC : IsClosed C :=
    isClosed_iUnion_of_finite fun b => (isCompact_range (T.capping.cap b).continuous).isClosed
  have hqV : q ∈ g ⁻¹' Cᶜ := by
    intro hq
    obtain ⟨b, x, hx⟩ := mem_iUnion.1 hq
    exact hcap ⟨b, x, by rw [hx]; exact T.presentation.apply_symm_apply _⟩
  refine mem_interior.2 ⟨g ⁻¹' Cᶜ, ?_, hC.isOpen_compl.preimage hg, hqV⟩
  intro q' hq'
  have hmem : g q' ∈ range T.capping.coreInclusion ∪ C := by
    rw [T.capping.exhaustive]
    exact mem_univ _
  rcases hmem with ⟨c, hc⟩ | hC'
  · have hpres : T.presentation (T.capping.coreInclusion c) = Sum.inl q' := by
      rw [hc]
      exact T.presentation.apply_symm_apply _
    have hcold : c ∈ E.old := by
      rw [hold]
      exact ⟨q', hpres⟩
    refine ⟨⟨c, hcold⟩, ?_⟩
    have h2 := E.oldOutput_eq ⟨c, hcold⟩
    exact (Sum.inl_injective (h2.symm.trans hpres))
  · exact absurd hC' hq'

/-- cap 像里有 `Q` 的点 ⇒ 该 cap 的边界球面在 `retainedCore`（`ThreeBall` 连通 + `inl` 的像 clopen）。 -/
theorem retainedBoundary_of_cap_P6S2 {b : E.transition.trace.tubes.Boundary} {x : ThreeBall}
    {q : Q.Carrier}
    (h : E.transition.trace.presentation (E.transition.trace.capping.cap b x) = Sum.inl q) :
    E.RetainedBoundary b := by
  intro y
  let T := E.transition.trace
  have hpc : PreconnectedSpace ThreeBall :=
    Subtype.preconnectedSpace (convex_closedBall (0 : ThreeSpace) 1).isPreconnected
  have hconn : IsPreconnected (range fun z : ThreeBall =>
      T.presentation (T.capping.cap b z)) :=
    isPreconnected_range (T.presentation.continuous.comp (T.capping.cap b).continuous)
  have hbd := T.capping.boundary_eq b ((T.capping.attaching b).symm y)
  rw [Homeomorph.apply_symm_apply] at hbd
  have hmem : T.presentation (T.capping.coreInclusion (T.tubes.coreBoundarySphere b y)) ∈
      connectedComponent (Sum.inl q : Q.Carrier ⊕ E.discarded.Carrier) := by
    have h1 : (Sum.inl q : Q.Carrier ⊕ E.discarded.Carrier) ∈
        range fun z : ThreeBall => T.presentation (T.capping.cap b z) := ⟨x, h⟩
    have h2 : T.presentation (T.capping.coreInclusion (T.tubes.coreBoundarySphere b y)) ∈
        range fun z : ThreeBall => T.presentation (T.capping.cap b z) :=
      ⟨sphereToThreeBall ((T.capping.attaching b).symm y), congrArg T.presentation hbd⟩
    exact hconn.subset_connectedComponent h1 h2
  obtain ⟨q', hq'⟩ := isClopen_range_inl.connectedComponent_subset (mem_range_self q) hmem
  exact ⟨q', hq'.symm⟩

end MetricCutCapEvent

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}

/-- **post-cover（records 版）**：post 点 `q` 要么是某个 retained cap 的标准帽模型点
`(static b).inclusion ((static b).witness.cap x)`（cap-model 支，`static b` 带完整定量 witness 与
`inclusion_metric`），要么是某个 `RegularCrossing` 的新侧像（含 collar / transition 区）。 -/
theorem postCover_P6S2 (R : GeometricCutoffRecord H i p) (q : (H.stage i.succ).Carrier) :
    (∃ (b : (H.event i).RetainedBoundaryIndex) (x : ThreeBall),
        q = (R.static b).inclusion ((R.static b).witness.cap x)) ∨
      ∃ p' : (H.stage i.castSucc).Carrier, (H.event i).RegularCrossing p' q := by
  rcases (H.event i).post_cover_event_P6S2 R.old_eq_retained q with ⟨b, x, h⟩ | h
  · left
    have hb := (H.event i).retainedBoundary_of_cap_P6S2 h
    refine ⟨⟨b, hb⟩, x, ?_⟩
    exact Sum.inl_injective (h.symm.trans ((R.static ⟨b, hb⟩).cap_eq x))
  · exact Or.inr h

end GeometricCutoffRecord


/-- **左侧逻辑二分（实数层）**：要么任意近处（`σ` 左侧 `δ`-邻域内）都有 `B` 点，要么某个左邻域内无 `B` 点。 -/
theorem left_dichotomy_P6S2 (B : ℝ → Prop) (σ : ℝ) :
    (∀ δ : ℝ, 0 < δ → ∃ v : ℝ, σ - δ < v ∧ v < σ ∧ B v) ∨
      ∃ δ : ℝ, 0 < δ ∧ ∀ v : ℝ, σ - δ < v → v < σ → ¬ B v := by
  by_cases h : ∀ δ : ℝ, 0 < δ → ∃ v : ℝ, σ - δ < v ∧ v < σ ∧ B v
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨δ, hδ, h⟩ := h
    exact ⟨δ, hδ, h⟩

namespace ObservedHistory

/-- **左侧逻辑二分（history 层）**：`σ` 左侧要么任意近处有坏点（某个 `v ∈ (σ − δ, σ)`、某点不 Good），
要么某个左邻域内处处 Good。 -/
theorem left_dichotomy_good_P6S2 (H : ObservedHistory.{u}) {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (σ : ℝ) :
    (∀ δ : ℝ, 0 < δ → ∃ v : Icc (0 : ℝ) H.horizon, σ - δ < v ∧ (v : ℝ) < σ ∧
      ∃ z : (H.stageAt v).Carrier, ¬ H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z) ∨
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : Icc (0 : ℝ) H.horizon, σ - δ < v → (v : ℝ) < σ →
      ∀ z : (H.stageAt v).Carrier, H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z := by
  rcases left_dichotomy_P6S2 (fun v => ∃ hv : 0 ≤ v ∧ v ≤ H.horizon,
      ∃ z : (H.stageAt ⟨v, hv⟩).Carrier,
        ¬ H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime ⟨v, hv⟩ z) σ with h | ⟨δ, hδ, h⟩
  · refine Or.inl fun δ hδ => ?_
    obtain ⟨v, h1, h2, hv, z, hz⟩ := h δ hδ
    exact ⟨⟨v, hv⟩, h1, h2, z, hz⟩
  · refine Or.inr ⟨δ, hδ, fun v h1 h2 z => ?_⟩
    by_contra hz
    exact h v h1 h2 ⟨⟨v.2.1, v.2.2⟩, z, hz⟩

end ObservedHistory

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}

/-- **S-a（records 的 cap-model witness 收口）**：post 点 `y`（stage `i.succ` 的起始时刻）若是 retained cap
的标准帽模型点，且 records 给出该点处输出度量的**完整定量 witness（含 `capTubeHasNeckChart`）**
（`hcapW`，records 须输出目标常数 / 精度下的 witness，不是"接近标准帽"一句），则 `y` 处 spatial witness
存在（stage 初时刻 = 边界点，时间导数分量空真）。 -/
theorem spatial_of_post_cap_P6S2 (R : GeometricCutoffRecord H i p) {eps C1 C2 : ℝ}
    (hcapW : ∀ (b : (H.event i).RetainedBoundaryIndex) (x : ThreeBall),
      ∃ W : SpatialCanonicalWitness (H.event i).outputMetric eps C1 C2
        ((R.static b).inclusion ((R.static b).witness.cap x)), W.capTubeHasNeckChart eps)
    (b : (H.event i).RetainedBoundaryIndex) (x : ThreeBall)
    {y : (H.stageAt (H.stageTime i.succ)).Carrier}
    (hy : HEq y ((R.static b).inclusion ((R.static b).witness.cap x))) :
    ∃ W : SpatialCanonicalWitness
      (H.stageMetric (H.activeStage (H.stageTime i.succ)) (H.stageTime i.succ)) eps C1 C2 y,
        W.capTubeHasNeckChart eps := by
  have hP : H.stageAt (H.stageTime i.succ) = H.stage i.succ :=
    congrArg H.stage (H.activeStage_stageTime i.succ)
  have hg : HEq (H.stageMetric (H.activeStage (H.stageTime i.succ)) (H.stageTime i.succ))
      (H.event i).outputMetric :=
    (ObservedHistory.stageMetric_heq_of_idx_P6S2 H (H.activeStage_stageTime i.succ) _).trans
      (heq_of_eq ((H.stageMetric_initial i.succ).trans (H.event_output i).symm))
  exact (ObservedHistory.spatial_iff_heq_P6S2 hP hg hy).mpr (hcapW b x)

/-- **S-a 收口**：stage 时刻类的坏点 `y` 若是 cap-model 点，则与 `hsel : ¬ Good` 矛盾。 -/
theorem false_of_stage_cap_P6S2 (R : GeometricCutoffRecord H i p) {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hcapW : ∀ (b : (H.event i).RetainedBoundaryIndex) (x : ThreeBall),
      ∃ W : SpatialCanonicalWitness (H.event i).outputMetric eps C1 C2
        ((R.static b).inclusion ((R.static b).witness.cap x)), W.capTubeHasNeckChart eps)
    (b : (H.event i).RetainedBoundaryIndex) (x : ThreeBall)
    {y : (H.stageAt (H.stageTime i.succ)).Carrier}
    (hy : HEq y ((R.static b).inclusion ((R.static b).witness.cap x)))
    (hsel : ¬ H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime (H.stageTime i.succ) y) :
    False :=
  hsel ((ObservedHistory.hasSpatialCanonicalTimeControl_iff_of_boundary_P6S
    (Or.inl (H.boundary_of_stageTime_P6S i.succ))).mpr
      (R.spatial_of_post_cap_P6S2 hcapW b x hy))

/-- **(S) 类装配（S-a + 二分 + S-c binder）**：stage 时刻 `σ = time i.succ` 处 post 点 `y` 的
`hsel : ¬ Good` ⇒ 左侧任意近处有坏点。证明：post-cover 二分——cap-model 支由 S-a（`hcapW`）与 `hsel`
矛盾；`RegularCrossing` 新侧像支再对左侧作逻辑二分：任意近处有坏点（结论）或某左邻域处处 Good，
后者由 **S-c stability contract `hstab`**（显式 binder，D-13 原文形，不证）给出 `y` 处 spatial witness，
又与 `hsel` 矛盾。`hstab` 的内容：共同 footprint（`RegularCrossing` 的 `old` 邻域）与 pre/post `C^k`
收敛已在 event 数据里（`terminal.converges` + `old_metric_eq`），其余带 domain 余量的更细 witness
（左 Good ⇒ 同常数极限 witness）是 S-c 的 OPEN 部分。 -/
theorem stage_class_left_bad_P6S2 (R : GeometricCutoffRecord H i p) {eps C1 C2 : ℝ}
    {Ctime : ℝ≥0}
    (hcapW : ∀ (b : (H.event i).RetainedBoundaryIndex) (x : ThreeBall),
      ∃ W : SpatialCanonicalWitness (H.event i).outputMetric eps C1 C2
        ((R.static b).inclusion ((R.static b).witness.cap x)), W.capTubeHasNeckChart eps)
    (hstab : ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier),
      (H.event i).RegularCrossing p' q →
      (∃ δ : ℝ, 0 < δ ∧ ∀ v : Icc (0 : ℝ) H.horizon, H.time i.succ - δ < v →
        (v : ℝ) < H.time i.succ → ∀ z : (H.stageAt v).Carrier,
          H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z) →
      ∃ W : SpatialCanonicalWitness (H.event i).outputMetric eps C1 C2 q,
        W.capTubeHasNeckChart eps)
    {y : (H.stageAt (H.stageTime i.succ)).Carrier}
    (hsel : ¬ H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime (H.stageTime i.succ) y) :
    ∀ δ : ℝ, 0 < δ → ∃ v : Icc (0 : ℝ) H.horizon, H.time i.succ - δ < v ∧
      (v : ℝ) < H.time i.succ ∧
      ∃ z : (H.stageAt v).Carrier, ¬ H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z := by
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
  · rcases ObservedHistory.left_dichotomy_good_P6S2 H (eps := eps) (C1 := C1) (C2 := C2)
        (Ctime := Ctime) (H.time i.succ) with h | h
    · exact h
    · exact (hsel ((ObservedHistory.hasSpatialCanonicalTimeControl_iff_of_boundary_P6S
        (Or.inl (H.boundary_of_stageTime_P6S i.succ))).mpr
          ((ObservedHistory.spatial_iff_heq_P6S2 hP hg hq).mpr (hstab p' q hcross h)))).elim

end GeometricCutoffRecord

namespace ObservedHistory

/-- **S-b 参数引理（算术）**：左移重跑的余量设计。`R'/R → 1` 时 eventually `R/2 ≤ R'`；取
`L' = L/2`、左移 `σ − σ' ≤ L²/(2R)`：
(1) 阈值：原 Good 区阈值 `4R ≤ 8R'`（新调用须允许系数 `8`）；
(2) 时间窗：`σ − L²/R ≤ σ' − L'²/R'`（`σ − σ' + L'²/R' ≤ L²/R`）；
(3) 距离：`L'/√R' ≤ (3/4)·L/√R`——留出 `L/(4√R)` 吸收种子中心项的位移。 -/
theorem leftShift_params_P6S2 {R R' L σ σ' : ℝ} (hR : 0 < R) (hRR' : R / 2 ≤ R') (hL : 0 ≤ L)
    (hshift : σ - σ' ≤ L ^ 2 / (2 * R)) :
    4 * R ≤ 8 * R' ∧ σ - L ^ 2 / R ≤ σ' - (L / 2) ^ 2 / R' ∧
      (L / 2) / Real.sqrt R' ≤ (3 / 4) * (L / Real.sqrt R) := by
  have hR' : 0 < R' := lt_of_lt_of_le (by positivity) hRR'
  have h1 : 4 * R ≤ 8 * R' := by linarith
  have h2 : (L / 2) ^ 2 / R' ≤ L ^ 2 / (2 * R) := by
    rw [div_le_div_iff₀ hR' (by positivity)]
    nlinarith [sq_nonneg L]
  have h3 : L ^ 2 / R = L ^ 2 / (2 * R) + L ^ 2 / (2 * R) := by
    field_simp
    ring
  have ha : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hb : 0 < Real.sqrt R' := Real.sqrt_pos.mpr hR'
  have hb' : (2 / 3) * Real.sqrt R ≤ Real.sqrt R' := by
    by_contra hlt
    push Not at hlt
    have := pow_lt_pow_left₀ hlt hb.le (two_ne_zero)
    rw [Real.sq_sqrt hR'.le, mul_pow, Real.sq_sqrt hR.le] at this
    nlinarith
  have h4 : (2 / 3 : ℝ) ≤ Real.sqrt R' / Real.sqrt R := (le_div_iff₀ ha).mpr hb'
  refine ⟨h1, by linarith, ?_⟩
  rw [div_le_iff₀ hb]
  have : (3 / 4) * (L / Real.sqrt R) * Real.sqrt R' =
      (3 / 4) * L * (Real.sqrt R' / Real.sqrt R) := by
    field_simp
  rw [this]
  nlinarith

/-- 序列侧：`R'ₙ / Rₙ → 1` ⇒ eventually `Rₙ / 2 ≤ R'ₙ`。 -/
theorem eventually_half_le_P6S2 {R R' : ℕ → ℝ} (hR : ∀ n, 0 < R n)
    (h : Tendsto (fun n => R' n / R n) atTop (𝓝 1)) : ∀ᶠ n in atTop, R n / 2 ≤ R' n := by
  filter_upwards [h.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with n hn
  have := (lt_div_iff₀ (hR n)).1 hn
  linarith

/-- S-b 的距离部分：新调用的距离阈值 `D₁ + L'/√R'` 落在原 Good 区的 `D₀ + L/√R` 内，前提是种子中心项
位移 `D₁ ≤ D₀ + L/(4√R)`。 -/
theorem rerun_dist_le_P6S2 {R R' L : ℝ} (hR : 0 < R) (hL : 0 ≤ L) (hRR' : R / 2 ≤ R')
    {D0 D1 d : ℝ≥0∞} (hcen : D1 ≤ D0 + ENNReal.ofReal (L / (4 * Real.sqrt R)))
    (hd : d ≤ D1 + ENNReal.ofReal ((L / 2) / Real.sqrt R')) :
    d ≤ D0 + ENNReal.ofReal (L / Real.sqrt R) := by
  obtain ⟨-, -, h3⟩ := leftShift_params_P6S2 (σ := 0) (σ' := 0) hR hRR' hL
    (by simp only [sub_self]; positivity)
  have ha : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  refine hd.trans ((add_le_add hcen le_rfl).trans ?_)
  rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)
  have : L / (4 * Real.sqrt R) = (1 / 4) * (L / Real.sqrt R) := by field_simp
  rw [this]
  linarith

/-- **S-b `leftShift_rerun_P6S2`（`hgood` 形）**：selection 在 `(σ, y)`（标量 `R`、窗口参数 `L`、阈值 `4R`）
给出 Good 区；左移到 `σ' ≤ σ`（`σ − σ' ≤ L²/(2R)`）、`R/2 ≤ R'`、`L' = L/2`，种子中心项位移
`d_{σ'}(O, y') ≤ d_σ(O, y) + L/(4√R)` ⇒ 重跑的 Good 区（窗口 `σ' − L'²/R' ≤ v`、距离
`d_{σ'}(O, y') + L'/√R'`、**阈值 `8R'`**）落在原 Good 区内，故重跑所需的 `hgood`（`L' = L/2`、`R'`、
阈值系数 `8`）成立。新调用须允许阈值系数 `8`（P6D 级 binder `qs n ≤ Cs * R n` 取 `Cs = 8`，如
`false_of_rerun_decoupled_P6P`），或经重标度 adapter。 -/
theorem leftShift_rerun_P6S2 {H : ObservedHistory.{u}} {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T aSeed σ σ' : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ T) (hsT : σ ≤ T) (has : aSeed ≤ σ)
    (hσσ : σ' ≤ σ) (has' : aSeed ≤ σ') {pT : (H.stageAt T).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage T)
      (H.activeStage_mono haT) pT)
    (y : (H.stageAt σ).Carrier) (y' : (H.stageAt σ').Carrier) {R R' L : ℝ}
    (hR : 0 < R) (hRR' : R / 2 ≤ R') (hL : 0 ≤ L)
    (hshift : (σ : ℝ) - σ' ≤ L ^ 2 / (2 * R))
    (hcen : riemannianEDistOf (H.stageMetric (H.activeStage σ') σ')
        (seedTrace.point (H.activeStage σ') (H.activeStage_mono has')
          (H.activeStage_mono (hσσ.trans hsT))) y' ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
        (seedTrace.point (H.activeStage σ) (H.activeStage_mono has) (H.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / (4 * Real.sqrt R)))
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        4 * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ'),
      (σ' : ℝ) - (L / 2) ^ 2 / R' ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans (hσσ.trans hsT)))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ') σ')
              (seedTrace.point (H.activeStage σ') (H.activeStage_mono has')
                (H.activeStage_mono (hσσ.trans hsT))) y' +
            ENNReal.ofReal ((L / 2) / Real.sqrt R') →
        8 * R' ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z := by
  intro v hav hvs hwin z hd hq
  obtain ⟨h4, hw, -⟩ := leftShift_params_P6S2 (σ := (σ : ℝ)) (σ' := (σ' : ℝ)) hR hRR' hL hshift
  exact hgood v hav (hvs.trans hσσ) (hw.trans hwin) z
    (rerun_dist_le_P6S2 hR hL hRR' hcen hd) (h4.trans hq)

/-- **consumer（(S) 类 ⇒ event 内部类）**：stage 时刻类坏点序列（`σ n = time (i n).succ`、post 点 `y n`、
`hsel : ¬ Good`），经 S-a（`hcapW`）与 S-c binder（`hstab`），给出**左侧 event slab 内部**的坏点序列
`v n ∈ (time (i n).castSucc, time (i n).succ)`、`time (i n).succ − v n < 1/(n+1)`——正是 event 内部主形
（`false_of_selection_eventSlab_Kdata_ctrl_noRt_P6S` 的 `hjt` / `htj`）的输入形；其后经 `leftShift_rerun_P6S2`
重选 / 重跑。 -/
theorem left_bad_sequence_of_stage_class_P6S2 {Kh : ℕ → ObservedHistory.{u}}
    {eps C1 C2 : ℝ} {Ctime : ℝ≥0} {i : ∀ n, Fin (Kh n).eventCount} {pp : ℕ → CutoffParameters}
    (R : ∀ n, GeometricCutoffRecord (Kh n) (i n) (pp n))
    (hcapW : ∀ n (b : ((Kh n).event (i n)).RetainedBoundaryIndex) (x : ThreeBall),
      ∃ W : SpatialCanonicalWitness ((Kh n).event (i n)).outputMetric eps C1 C2
        (((R n).static b).inclusion (((R n).static b).witness.cap x)), W.capTubeHasNeckChart eps)
    (hstab : ∀ n (p' : ((Kh n).stage (i n).castSucc).Carrier)
      (q : ((Kh n).stage (i n).succ).Carrier), ((Kh n).event (i n)).RegularCrossing p' q →
      (∃ δ : ℝ, 0 < δ ∧ ∀ v : Icc (0 : ℝ) (Kh n).horizon, (Kh n).time (i n).succ - δ < v →
        (v : ℝ) < (Kh n).time (i n).succ → ∀ z : ((Kh n).stageAt v).Carrier,
          (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z) →
      ∃ W : SpatialCanonicalWitness ((Kh n).event (i n)).outputMetric eps C1 C2 q,
        W.capTubeHasNeckChart eps)
    (y : ∀ n, ((Kh n).stageAt ((Kh n).stageTime (i n).succ)).Carrier)
    (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime
      ((Kh n).stageTime (i n).succ) (y n)) :
    ∃ (v : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (z : ∀ n, ((Kh n).stageAt (v n)).Carrier),
      (∀ n, (Kh n).time (i n).castSucc < (v n : ℝ) ∧ (v n : ℝ) < (Kh n).time (i n).succ ∧
        (Kh n).time (i n).succ - (v n : ℝ) < 1 / ((n : ℝ) + 1)) ∧
      ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime (v n) (z n) := by
  have key : ∀ n, ∃ (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      ((Kh n).time (i n).castSucc < (v : ℝ) ∧ (v : ℝ) < (Kh n).time (i n).succ ∧
        (Kh n).time (i n).succ - (v : ℝ) < 1 / ((n : ℝ) + 1)) ∧
      ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z := by
    intro n
    have hlt : (Kh n).time (i n).castSucc < (Kh n).time (i n).succ :=
      (Kh n).time_strictMono (Fin.castSucc_lt_succ (i := i n))
    have hδ : 0 < min (1 / ((n : ℝ) + 1)) ((Kh n).time (i n).succ - (Kh n).time (i n).castSucc) :=
      lt_min (by positivity) (sub_pos.mpr hlt)
    obtain ⟨v, h1, h2, z, hz⟩ := (R n).stage_class_left_bad_P6S2 (hcapW n) (hstab n)
      (hsel n) _ hδ
    have hm1 := min_le_left (1 / ((n : ℝ) + 1))
      ((Kh n).time (i n).succ - (Kh n).time (i n).castSucc)
    have hm2 := min_le_right (1 / ((n : ℝ) + 1))
      ((Kh n).time (i n).succ - (Kh n).time (i n).castSucc)
    exact ⟨v, z, ⟨by linarith, h2, by linarith⟩, hz⟩
  choose v z hvz hbad using key
  exact ⟨v, z, hvz, hbad⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

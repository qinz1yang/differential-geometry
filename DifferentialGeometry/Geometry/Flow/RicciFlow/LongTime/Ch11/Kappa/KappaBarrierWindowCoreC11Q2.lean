import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RegularMinimizerEndpointBarrier

/-!
# K3 窗口化：树内 surgery action barrier 的局部版（O-CH11-KAPPA2 G1 核心，后缀 `_C11Q2`）

树内屏障 `exists_uniform_regularMinimizerEndpoint_of_regularizedCost_lt`
（`Surgery/Topology/RegularMinimizerEndpointBarrier:22`）对**所有** event 要 `δ(time j.succ) ≤ δ₀`、
`neckRadius ≤ ρ`（`hasCanonicalCutoffRecords` 的全局形），并对 `t` 之前**所有** stage 要标量时间导数
控制 `HistoryScalarDerivativeBoundBefore`。本文件把整条 wrapper 链
（`…inserted_cap_birth…` → `…nonregular_node…` → `…regularCrossing_of_sum…` →
`…minimizer_of_regularizedCost_lt…` → 顶层）逐条重写成**窗口形**：只对时钟窗口
`[t − E², t]` 内的 event / stage 要求
* `δ(time j.succ) ≤ δ₀`、`neckRadius(time j.succ) ≤ ρ`（`t − E² ≤ time j.succ ≤ t`）；
* 标量时间导数控制（stage 起点 `time j ≥ t − E²`）。

关键事实（读证明得出，不是新数学）：最内层 `exists_uniform_canonical_cap_birth_action_lower_bound`
（`CapWindowAction:1537`）本来就只对坏 event `i` **之后**、`activeStage t` 之前的 event / stage 取
`δ` 与导数控制，而坏 event `i` 被曲线在时钟 `[0, v] ⊆ [0, E]` 内穿过，故
`t − E² ≤ t − v² ≤ time i.succ < t`——所以窗口化只改 wrapper，证明逐字照搬
（`hδ j` / `hρp j` / `hderiv` 处补上窗口成员证明）。常数 `(δ₀, ε₀, R₀, m₀)` 与树内完全相同
（同一组 `obtain`），依赖 `(A, E, r₀, qcan, Λ, ρ, Ctime)` 与初始数据的 `a₀`——**绝对尺度**；
尺度一致性见 `KappaBarrierWindowC11Q2.lean`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-- 窗口内 stage 的标量导数控制 ⇒ 闭端点（`s ≤ t`）版本（`abs_derivWithin_stageScalar_le_of_le_…`
的窗口形）。 -/
theorem abs_derivWithin_stageScalar_le_of_window_C11Q2 (H : ObservedHistory.{u})
    {C : ℝ≥0} {q t w : ℝ}
    (hderiv : ∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier), w ≤ H.time j →
      ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s < t →
        q < metricScalarAt (H.stageMetric j s) y →
          |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
            C * metricScalarAt (H.stageMetric j s) y ^ 2)
    (j : Fin (H.eventCount + 1)) (hw : w ≤ H.time j) (y : (H.stage j).Carrier)
    (s : ℝ) (hs : s ∈ Ioo (H.time j) (H.stageEndTime j)) (hst : s ≤ t)
    (hq : q < metricScalarAt (H.stageMetric j s) y) :
    |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
      C * metricScalarAt (H.stageMetric j s) y ^ 2 := by
  rcases hst.lt_or_eq with hlt | heq
  · exact hderiv j y hw s hs hlt hq
  · exact H.abs_derivWithin_stageScalar_le_of_forall_Ioo j hs y
      (fun r hr hqr => hderiv j y hw r ⟨hr.1, hr.2.trans hs.2⟩ (hr.2.trans_eq heq) hqr) hq

/-- 窗口成员：`time i.succ ≤ time j.castSucc` 与 `j.succ ≤ activeStage t` ⇒ `time j.succ` 在
`[time i.succ, t]` 内。 -/
theorem time_succ_mem_window_C11Q2 (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    {w : ℝ} (i j : Fin H.eventCount) (hw : w ≤ H.time i.succ) (hij : i.succ ≤ j.castSucc)
    (hj : j.succ ≤ H.activeStage t) :
    w ≤ H.time j.succ ∧ H.time j.succ ≤ t.val :=
  ⟨hw.trans ((H.time_strictMono.monotone hij).trans
      (H.time_strictMono.monotone j.castSucc_lt_succ.le)),
    (H.time_strictMono.monotone hj).trans (H.activeStage_time_le t)⟩

/-- **窗口形 inserted-cap-birth 下界**（`…_of_inserted_cap_birth_of_derivative_before` 的局部版）：
`δ` / `neckRadius` / 导数控制只在时钟窗口 `[t − E², t]` 内要求。常数与树内同一组。 -/
theorem exists_window_sum_action_gt_of_inserted_cap_birth_C11Q2
    (A B E rTerm qDeriv a₀ c ρ : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, 0 < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ → parameters.recenterConstant ≤ c →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      ∀ (t : Icc (0 : ℝ) H.horizon),
      (∀ j : Fin H.eventCount, t.val - E ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, t.val - E ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.neckRadius (H.time j.succ) ≤ ρ) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier), t.val - E ^ 2 ≤ H.time j →
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s < t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (i : Fin H.eventCount) (b : (H.event i).RetainedBoundaryIndex),
      ((records i).static b).hasCanonicalWindow →
      ∀ (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTerm →
      ∀ (first : Fin (H.eventCount + 1)) (hfirst : first ≤ i.succ)
        (hbirth : H.time i.succ < t.val) (v : ℝ),
      0 ≤ v → v ≤ E → t.val - v ^ 2 ∈ H.stageDomain first →
      t.val - v ^ 2 ≤ H.time i.succ →
      ∀ alpha : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t (alpha j)) volume
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) →
      (∀ j, ∀ s ∈ Ioo
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val),
        -B ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) (alpha j s)) →
      alpha ⟨H.activeStage t, hfirst.trans (H.le_activeStage t i.succ hbirth.le), le_rfl⟩ 0 = p →
      (∀ (j : Fin H.eventCount) (hi : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = alpha ⟨j.castSucc, hi, j.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = alpha ⟨j.succ, hi.trans j.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      ∀ z : ThreeBall,
      alpha ⟨i.succ, hfirst, H.le_activeStage t i.succ hbirth.le⟩
        (Real.sqrt (t.val - H.time i.succ)) =
          ((records i).static b).inclusion (((records i).static b).witness.cap z) →
      A < ∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t (alpha j)
          (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val) := by
  obtain ⟨qmin, Cbirth, R, hqmin, hCbirth, hR, m₀, hm₀, ε₀, δ₀, hε₀, hεhalf, hδ₀, haction⟩ :=
    exists_uniform_canonical_cap_birth_action_lower_bound.{u}
      A B E rTerm Cderiv hB hE hrTerm
  let Qmin := max qmin (max (qDeriv / Cbirth) (1 / a₀))
  have hQmin : 0 < Qmin := (one_div_pos.mpr ha₀).trans_le
    ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨δscale, hδscale, hscale⟩ :=
    exists_uniform_static_cap_scale_lower_bound c ρ Qmin hc hρ hQmin
  refine ⟨m₀, R, ε₀, min δ₀ δscale, StandardCap.transitionEnd_pos.trans hR,
    hε₀, lt_min hδ₀ hδscale, ?_⟩
  intro H parameters hm hmodelRadius herror hpc records hfixed hscalarInitial t hδ hρp hderiv
    i b hcanonical p hball first hfirst hbirth v hv hvE hlower hstart
    alpha halpha hint hscalar hrecent hnode z hpast
  have hwin : t.val - E ^ 2 ≤ H.time i.succ := by
    have hv2 : v ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ hv hvE 2
    linarith
  let cap := (records i).static b
  let q := cap.neck.scale
  have hcapScale := hscale H i parameters hpc
    ((hδ i hwin hbirth.le).trans (min_le_right _ _)) (hρp i hwin hbirth.le) (records i) b
  have hqminq : qmin ≤ q := (le_max_left _ _).trans hcapScale.le
  have hd : qDeriv / Cbirth ≤ q :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hcapScale.le
  have ha : 1 / a₀ ≤ q :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hcapScale.le
  have hqDerivQ : qDeriv ≤ Cbirth * q := by
    simpa only [mul_comm] using (div_le_iff₀ hCbirth).mp hd
  have haq : 1 ≤ a₀ * q := by simpa only [mul_comm] using (div_le_iff₀ ha₀).mp ha
  exact haction H i t (H.le_activeStage t i.succ hbirth.le) parameters records b hcanonical
    hmodelRadius hm herror qDeriv a₀ hqDeriv hqDerivQ haq hfixed hscalarInitial
    (fun j hij hj z => ((records j).delta_le z).trans
      ((hδ j (H.time_succ_mem_window_C11Q2 t i j hwin hij hj).1
        (H.time_succ_mem_window_C11Q2 t i j hwin hij hj).2).trans (min_le_left _ _)))
    (fun j hij _ x s hs hst hq => H.abs_derivWithin_stageScalar_le_of_window_C11Q2 hderiv j
      (hwin.trans (H.time_strictMono.monotone hij)) x s hs hst hq)
    hqminq p hball first hfirst v hv hvE hlower hstart
    alpha halpha hint hscalar hrecent hnode z hpast

/-- **窗口形 non-regular node 下界**（`…_of_nonregular_node_of_derivative_before` 的局部版）。 -/
theorem exists_window_sum_action_gt_of_nonregular_node_C11Q2
    (A B E rTerm qDeriv a₀ c ρ : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, 0 < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ → parameters.recenterConstant ≤ c →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      ∀ (t : Icc (0 : ℝ) H.horizon),
      (∀ j : Fin H.eventCount, t.val - E ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, t.val - E ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.neckRadius (H.time j.succ) ≤ ρ) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier), t.val - E ^ 2 ≤ H.time j →
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s < t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTerm →
      ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 ≤ v → v ≤ E → t.val - v ^ 2 ∈ H.stageDomain first →
      ∀ alpha : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (alpha j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t (alpha j)) volume
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) →
      (∀ j, ∀ s ∈ Ioo
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val),
        -B ≤ metricScalarAt (H.stageMetric j.val (t.val - s ^ 2)) (alpha j s)) →
      alpha ⟨H.activeStage t, hle, le_rfl⟩ 0 = p →
      (∀ (j : Fin H.eventCount) (hi : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∃ z : (H.event j).old,
          z.val.val = alpha ⟨j.castSucc, hi, j.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (t.val - H.time j.succ)) ∧
          (H.event j).oldOutput z = alpha ⟨j.succ, hi.trans j.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (t.val - H.time j.succ))) →
      ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
      (∀ b : (H.event i).RetainedBoundaryIndex, ((records i).static b).hasCanonicalWindow) →
      ¬ (H.event i).RegularCrossing
        (alpha ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (t.val - H.time i.succ)))
        (alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (t.val - H.time i.succ))) →
      A < ∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t (alpha j)
          (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val) := by
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, haction⟩ :=
    exists_window_sum_action_gt_of_inserted_cap_birth_C11Q2.{u}
      A B E rTerm qDeriv a₀ c ρ Cderiv hB hE hrTerm hqDeriv ha₀ hc hρ
  refine ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, ?_⟩
  intro H parameters hm hmodelRadius herror hpc records hfixed hscalarInitial
    t hδ hρp hderiv p hball first hle v hv hvE hlower alpha halpha hint hscalar hterminal hnode
    i hf hl hcanonical hbad
  have hbirth : H.time i.succ < t.val := by
    apply lt_of_le_of_ne ((H.time_strictMono.monotone hl).trans (H.activeStage_time_le t))
    intro he
    have hi : H.activeStage t = i.succ := by
      apply le_antisymm _ hl
      apply H.time_strictMono.le_iff_le.mp
      simpa only [he] using H.activeStage_time_le t
    have hindex :
        (⟨H.activeStage t, hle, le_rfl⟩ : H.StageInterval first (H.activeStage t)) =
        ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ := Subtype.ext hi
    have halphaPoint : HEq (alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ 0) p := by
      have hpair := congrArg
        (fun j : H.StageInterval first (H.activeStage t) =>
          (⟨j, alpha j 0⟩ : Sigma fun j : H.StageInterval first (H.activeStage t) =>
            (H.stage j.val).Carrier)) hindex
      exact (Sigma.mk.inj_iff.mp hpair).2.symm.trans (heq_of_eq hterminal)
    have hpoint : alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ 0 =
        Eq.rec (motive := fun j _ => (H.stage j).Carrier) p hi :=
      eq_of_heq (halphaPoint.trans (eqRec_heq (φ := fun j => (H.stage j).Carrier) hi p).symm)
    have hclock : Real.sqrt (t.val - H.time i.succ) = 0 := by
      rw [he, sub_self, Real.sqrt_zero]
    obtain ⟨z, hzold, hznew⟩ := hnode i hf hl
    rw [hclock] at hzold hznew hbad
    apply hbad
    rw [← hzold, hpoint]
    exact hball.regularCrossing_of_oldOutput_at_event_time H i he.symm z (hznew.trans hpoint)
  have hstart : t.val - v ^ 2 < H.time i.succ := by
    let start : Icc (0 : ℝ) H.horizon :=
      ⟨t.val - v ^ 2, H.stageDomain_subset first hlower⟩
    have hactive : H.activeStage start = first := (H.mem_stageDomain_iff start first).mp hlower
    by_contra hn
    have hi : i.succ ≤ first := by
      simpa only [hactive] using H.le_activeStage start i.succ (not_lt.mp hn)
    exact (not_le_of_gt (hf.trans_lt i.castSucc_lt_succ)) hi
  obtain ⟨b, z, hbirthLabel⟩ : ∃ (b : (H.event i).RetainedBoundaryIndex) (z : ThreeBall),
      alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
        (Real.sqrt (t.val - H.time i.succ)) =
          ((records i).static b).inclusion (((records i).static b).witness.cap z) := by
    rcases (H.event i).regularCrossing_or_cap_of_admissible_node
        (records i).old_eq_retained (hnode i hf hl) with hregular | ⟨b, z, hcap⟩
    · exact (hbad hregular).elim
    · exact ⟨b, z, Sum.inl_injective (hcap.symm.trans (((records i).static b).cap_eq z))⟩
  exact haction H parameters hm hmodelRadius herror hpc records
    hfixed hscalarInitial t hδ hρp hderiv i b (hcanonical b) p hball first
    (hf.trans i.castSucc_lt_succ.le) hbirth v hv hvE hlower hstart.le
    alpha halpha hint hscalar hterminal hnode z hbirthLabel

open private exists_contMDiff_family_action_lt from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowAction

/-- **窗口形 regular crossing**（`…regularCrossing_of_sum_stageRegularizedAction_lt…` 的局部版）。 -/
theorem exists_window_regularCrossing_of_sum_action_lt_C11Q2
    (A B E rTerm qDeriv a₀ c ρ : ℝ) (Cderiv : ℝ≥0)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, 0 < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ → parameters.recenterConstant ≤ c →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      ∀ (t : Icc (0 : ℝ) H.horizon),
      (∀ j : Fin H.eventCount, t.val - E ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, t.val - E ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.neckRadius (H.time j.succ) ≤ ρ) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier), t.val - E ^ 2 ≤ H.time j →
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s < t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTerm →
      ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      0 ≤ v → v ≤ E → t.val - v ^ 2 ∈ H.stageDomain first →
      (∀ j : H.StageInterval first (H.activeStage t),
        ∀ r ∈ Ioo (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val),
        ∀ x : (H.stage j.val).Carrier,
          -B ≤ metricScalarAt (H.stageMetric j.val (t.val - r ^ 2)) x) →
      ∀ alpha : (j : H.StageInterval first (H.activeStage t)) → ℝ → (H.stage j.val).Carrier,
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (alpha j)
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val t (alpha j)) volume
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) →
      alpha ⟨H.activeStage t, hle, le_rfl⟩ 0 = p →
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
        ∃ z : (H.event i).old,
          z.val.val = alpha ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (t.val - H.time i.succ)) ∧
          (H.event i).oldOutput z = alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (t.val - H.time i.succ))) →
      (∑ j : H.StageInterval first (H.activeStage t),
        H.stageRegularizedAction j.val t (alpha j)
          (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) < A →
      ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
      (∀ b : (H.event i).RetainedBoundaryIndex, ((records i).static b).hasCanonicalWindow) →
      (H.event i).RegularCrossing
        (alpha ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (t.val - H.time i.succ)))
        (alpha ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (t.val - H.time i.succ))) := by
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, hbarrier⟩ :=
    exists_window_sum_action_gt_of_nonregular_node_C11Q2.{u}
      A B E rTerm qDeriv a₀ c ρ Cderiv hB hE hrTerm hqDeriv ha₀ hc hρ
  refine ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, ?_⟩
  intro H parameters hm hmodelRadius herror hpc records hfixed hscalarInitial
    t hδ hρp hderiv p hball first hle v hv hvE hpast hscalar alpha halpha hint hterminal hnode
    hsmall
  have hupper : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain (H.activeStage t) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using H.activeStage_mem t
  have hupperIcc : t.val - (0 : ℝ) ^ 2 ∈
      Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  let S := ∑ j : H.StageInterval first (H.activeStage t),
    H.stageRegularizedAction j.val t (alpha j)
      (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)
  have hepsilon : 0 < (A - S) / 2 := half_pos (sub_pos.mpr hsmall)
  obtain ⟨beta, hbeta, hbetaStart, hbetaEnd, hbetaInt, hbetaAction⟩ :=
    exists_contMDiff_family_action_lt H hle (le_refl 0) hv hupper hpast
      alpha halpha hint hnode hepsilon
  have hbetaSmall : (∑ j : H.StageInterval first (H.activeStage t),
      H.stageRegularizedAction j.val t (beta j)
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) < A := by
    change _ < S + (A - S) / 2 at hbetaAction
    linarith only [hbetaAction, hsmall]
  have hbetaTerminal : beta ⟨H.activeStage t, hle, le_rfl⟩ 0 = p := by
    have hs := hbetaStart ⟨H.activeStage t, hle, le_rfl⟩
    rw [H.regularizedStageStart_eq_of_mem_Icc (le_refl 0) hupperIcc] at hs
    exact hs.trans hterminal
  have hbetaNode (i : Fin H.eventCount) (hf : first ≤ i.castSucc)
      (hl : i.succ ≤ H.activeStage t) :
      ∃ z : (H.event i).old,
        z.val.val = beta ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (t.val - H.time i.succ)) ∧
        (H.event i).oldOutput z = beta ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (t.val - H.time i.succ)) := by
    obtain ⟨z, hzold, hznew⟩ := hnode i hf hl
    have ho := hbetaStart ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
    have hn := hbetaEnd ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
    rw [H.regularizedStageStart_castSucc_eq_event_clock hupperIcc i hl] at ho
    rw [H.regularizedStageEnd_succ_eq_event_clock hpast i hf] at hn
    exact ⟨z, hzold.trans ho.symm, hznew.trans hn.symm⟩
  intro i hf hl hcanonical
  by_contra hbad
  have ho := hbetaStart ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
  have hn := hbetaEnd ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
  rw [H.regularizedStageStart_castSucc_eq_event_clock hupperIcc i hl] at ho
  rw [H.regularizedStageEnd_succ_eq_event_clock hpast i hf] at hn
  have hlarge := hbarrier H parameters hm hmodelRadius herror hpc records
    hfixed hscalarInitial t hδ hρp hderiv p hball first hle v hv hvE hpast beta hbeta hbetaInt
    (fun j r hr => hscalar j r hr (beta j r)) hbetaTerminal hbetaNode i hf hl hcanonical
    (by simpa only [ho, hn] using hbad)
  exact (not_lt_of_ge hbetaSmall.le) hlarge

/-- **窗口形极小曲线 regular crossing**（`…minimizer_of_regularizedCost_lt_of_derivative_before` 的
局部版）：`regularizedCost < A` ⇒ 极小曲线存在且每个 event 是 regular crossing。 -/
theorem exists_window_regularCrossing_minimizer_C11Q2
    (A E rTerm qDeriv a₀ c ρ : ℝ) (Cderiv : ℝ≥0)
    (hE : 0 ≤ E) (hrTerm : 0 < rTerm) (hqDeriv : 0 < qDeriv)
    (ha₀ : 0 < a₀) (hc : 0 < c) (hρ : 0 < ρ) :
    ∃ m₀ : ℕ, ∃ R₀ ε₀ δ₀ : ℝ, 0 < R₀ ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ → parameters.recenterConstant ≤ c →
      ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      ∀ (t : Icc (0 : ℝ) H.horizon),
      (∀ j : Fin H.eventCount, t.val - E ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, t.val - E ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.neckRadius (H.time j.succ) ≤ ρ) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier), t.val - E ^ 2 ≤ H.time j →
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s < t.val →
          qDeriv < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Cderiv * metricScalarAt (H.stageMetric j s) y ^ 2) →
      ∀ (p : (H.stageAt t).Carrier),
      H.isParabolicallyRmControlledBall t p rTerm →
      ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ),
      v ≤ E →
      (∀ (i : Fin H.eventCount), first ≤ i.castSucc → i.succ ≤ H.activeStage t →
        ∀ b : (H.event i).RetainedBoundaryIndex, ((records i).static b).hasCanonicalWindow) →
      ∀ q : (H.stage first).Carrier,
      H.regularizedCost first (H.activeStage t) hle t (3 / a₀) 0 v p q < (A : WithTop ℝ) →
      q ∈ H.regularMinimizerEndpoints first (H.activeStage t) hle t (3 / a₀) v p := by
  have hB : 0 ≤ 3 / a₀ := (div_pos (by norm_num : (0 : ℝ) < 3) ha₀).le
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, hregular⟩ :=
    exists_window_regularCrossing_of_sum_action_lt_C11Q2.{u}
      A (3 / a₀) E rTerm qDeriv a₀ c ρ Cderiv hB hE hrTerm hqDeriv ha₀ hc hρ
  refine ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, ?_⟩
  intro H parameters hm hmodelRadius herror hpc records hfixed hscalarInitial
    t hδ hρp hderiv p hball first hle v hvE hcanonical q hcost
  have hfinite : H.regularizedCost first (H.activeStage t) hle t (3 / a₀) 0 v p q ≠ ⊤ := by
    intro htop
    rw [htop] at hcost
    exact not_lt_of_ge le_top hcost
  have hne : (H.regularizedActionValues first (H.activeStage t) hle t (3 / a₀) 0 v p q).Nonempty
      := by
    by_contra hn
    exact hfinite (H.regularizedCost_eq_top_of_no_competitor first (H.activeStage t) hle
      t (3 / a₀) 0 v p q (Set.not_nonempty_iff_eq_empty.mp hn))
  obtain ⟨value, hvalue⟩ := hne
  have hv : 0 ≤ v := hvalue.2.1
  have hpast : t.val - v ^ 2 ∈ H.stageDomain first := hvalue.2.2.2.1
  have hupper : t.val - (0 : ℝ) ^ 2 ∈ H.stageDomain (H.activeStage t) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using H.activeStage_mem t
  have hupperIcc : t.val - (0 : ℝ) ^ 2 ∈
      Icc (H.time (H.activeStage t)) (H.stageEndTime (H.activeStage t)) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have hpreserve := H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hfixed hscalarInitial
  have hscalar (j : H.StageInterval first (H.activeStage t))
      (r : ℝ) (hr : r ∈ Ioo (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val))
      (x : (H.stage j.val).Carrier) :
      -(3 / a₀) ≤ metricScalarAt (H.stageMetric j.val (t.val - r ^ 2)) x := by
    have hdomain := H.mapsTo_regularizedStage_Ioo t 0 v j.val hr
    have htime : 0 ≤ t.val - r ^ 2 := (H.stageDomain_subset j.val hdomain).1
    have hratio : 3 / (a₀ + (t.val - r ^ 2)) ≤ 3 / a₀ :=
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) ha₀
        (le_add_of_nonneg_right htime)
    have hlower : -(3 / a₀) ≤ -3 / (a₀ + (t.val - r ^ 2)) := by
      simpa only [neg_div] using neg_le_neg hratio
    exact hlower.trans (hpreserve.1 j.val (t.val - r ^ 2) hdomain x).2
  obtain ⟨gamma, hgamma, hint, hrecent, hold, hnode, hmin⟩ :=
    H.exists_regularizedCost_minimizer_of_ne_top first (H.activeStage t) hle
      t (3 / a₀) 0 v hB hupper hscalar p q hfinite
  have hext := H.regularizedExtendedAction_eq_sum_action first (H.activeStage t)
    (le_refl 0) hv hupperIcc hpast gamma hint (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hscalar j r hr (gamma j r))
  have hsmall : (∑ j : H.StageInterval first (H.activeStage t),
      H.stageRegularizedAction j.val t (gamma j)
        (H.regularizedStageStart t 0 j.val) (H.regularizedStageEnd t v j.val)) < A := by
    apply WithTop.coe_lt_coe.mp
    rw [← hext, hmin]
    exact hcost
  refine ⟨gamma, hgamma, hrecent, hold, ?_, hmin⟩
  intro i hf hl
  exact hregular H parameters hm hmodelRadius herror hpc records
    hfixed hscalarInitial t hδ hρp hderiv p hball first hle v hv hvE hpast hscalar
    gamma hgamma hint hrecent hnode hsmall i hf hl (hcanonical i hf hl)

/-- **窗口形顶层屏障**（`exists_uniform_regularMinimizerEndpoint_of_regularizedCost_lt` 的局部版）：
`a₀` 由初始数据 `(P₀, g₀)` 取（`exists_pos_fixedHamiltonIveyRegion_for_identified_histories`）；
对 `(E, A, r₀, qcan, Λ, ρ, Ctime)` 给 `(δ₀, ε₀, R₀, m₀)`；records / 参数显式给出（不经全局
`hasCanonicalCutoffRecords`）；`δ ≤ δ₀`、`neckRadius ≤ ρ` 只对窗口 `[t − E², t]` 内 event，导数控制
只对起点 `≥ t − E²` 的 stage。 -/
theorem exists_window_regularMinimizerEndpoint_C11Q2
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ (E A r₀ qcan Λ ρ : ℝ) (Ctime : ℝ≥0), 0 ≤ E → 0 < r₀ → 0 < qcan → 0 < Λ → 0 < ρ →
    ∃ (δ₀ ε₀ R₀ : ℝ) (m₀ : ℕ), 0 < δ₀ ∧ 0 < ε₀ ∧ 0 < R₀ ∧
    ∀ (H : ObservedHistory.{u}), Nonempty (InitialIdentification P₀ g₀ H) →
    ∀ (parameters : CutoffParameters),
      m₀ ≤ parameters.modelOrder → R₀ ≤ parameters.modelRadius →
      parameters.modelAccuracy ≤ ε₀ → parameters.recenterConstant ≤ Λ →
    ∀ records : ∀ j, GeometricCutoffRecord H j parameters,
      (∀ i b, ((records i).static b).hasCanonicalWindow) →
    ∀ (t : Icc (0 : ℝ) H.horizon),
      (∀ j : Fin H.eventCount, t.val - E ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.delta (H.time j.succ) ≤ δ₀) →
      (∀ j : Fin H.eventCount, t.val - E ^ 2 ≤ H.time j.succ → H.time j.succ ≤ t.val →
        parameters.neckRadius (H.time j.succ) ≤ ρ) →
      (∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier), t.val - E ^ 2 ≤ H.time j →
        ∀ s ∈ Ioo (H.time j) (H.stageEndTime j), s < t.val →
          qcan < metricScalarAt (H.stageMetric j s) y →
            |derivWithin (fun z => metricScalarAt (H.stageMetric j z) y) (Iic s) s| ≤
              Ctime * metricScalarAt (H.stageMetric j s) y ^ 2) →
    ∀ (p : (H.stageAt t).Carrier), H.isParabolicallyRmControlledBall t p r₀ →
    ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) (v : ℝ), v ≤ E →
    ∀ q : (H.stage first).Carrier,
      H.regularizedCost first (H.activeStage t) hle t (3 / a₀) 0 v p q < (A : WithTop ℝ) →
      q ∈ H.regularMinimizerEndpoints first (H.activeStage t) hle t (3 / a₀) v p := by
  obtain ⟨a₀, ha₀, hinitial⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀
  refine ⟨a₀, ha₀, ?_⟩
  intro E A r₀ qcan Λ ρ Ctime hE hr₀ hqcan hΛ hρ
  obtain ⟨m₀, R₀, ε₀, δ₀, hR₀, hε₀, hδ₀, hbarrier⟩ :=
    exists_window_regularCrossing_minimizer_C11Q2.{u}
      A E r₀ qcan a₀ Λ ρ Ctime hE hr₀ hqcan ha₀ hΛ hρ
  refine ⟨δ₀, ε₀, R₀, m₀, hδ₀, hε₀, hR₀, ?_⟩
  intro H hid parameters hm hradius haccuracy hrecenter records hcanonical t hδ hρp hderiv
    p hball first hle v hvE q hcost
  obtain ⟨identification⟩ := hid
  have hstart := hinitial H identification
  exact hbarrier H parameters hm hradius haccuracy hrecenter records hstart.1 hstart.2 t hδ hρp
    hderiv p hball first hle v hvE (fun i _ _ b => hcanonical i b) q hcost

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

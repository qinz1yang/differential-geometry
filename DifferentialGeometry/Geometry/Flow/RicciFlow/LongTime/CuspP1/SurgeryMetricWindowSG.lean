import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryStaticSG
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryMetricAbstractSG
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorWindowStage
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PostStageGeneralST
import DifferentialGeometry.Geometry.Metric.Family.Measurable

/-!
# 窗口上的度量连续性（G4b，S-A14-SURGERY）

`windowQuad_SG t x u := (postMetric t).inner (ι_t x) (dι_t u) (dι_t u)`（`D` 上的 "拉回度量族"
`G(t) = ι_t^* postMetric t` 的二次型）。本文件把它翻译成固定 history 的 `stageMetric`，并证
`t → τ₀`（τ₀ 可以是 event 时刻）时在紧集 `K ⊆ D` 上与 `G(τ₀)` 的双向 `e^ε` 接近：

* `windowQuad_eq_SG`：`postMetric` ↔ `stageMetric (activeStage t) t`（S-A14-STATIC G5 的 HEq）；
* `stageMetric_quad_continuousOn_SG`：每个 stage 的 slab 上二次型联合连续
  （`IsSolutionOn.smoothMetric` + `MetricFamilySmoothOn.metricQuadratic_continuousOn_carrier`）；
* event 左侧：`TerminalMetricConverges`（`j = 0`）+ `inner_bounds_of_metricDerivNorm_le`。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold Bundle DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

section Bridge

/-- stage 等式 + metric `HEq` 下，沿 `carrierHomeo` 复合的拉回二次型不变。 -/
theorem inner_comp_carrierHomeo_SG {A B : OrientedThreeStage.{u}} (h : A = B)
    {gA : A.Metric} {gB : B.Metric} (hg : HEq gA gB) {X : Type*} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] (f : X → A.Carrier) (x : X)
    (v w : TangentSpace ThreeModel x) :
    gB.inner (carrierHomeo_CPD2 h (f x))
        (mfderiv ThreeModel ThreeModel (fun y => carrierHomeo_CPD2 h (f y)) x v)
        (mfderiv ThreeModel ThreeModel (fun y => carrierHomeo_CPD2 h (f y)) x w) =
      gA.inner (f x) (mfderiv ThreeModel ThreeModel f x v)
        (mfderiv ThreeModel ThreeModel f x w) := by
  subst h
  rw [eq_of_heq hg]
  rfl

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- `D` 上拉回度量族 `G(t) = ι_t^* postMetric t` 的二次型。 -/
def windowQuad_SG (T : ObservationTower P g) (N : ℕ)
    (Fs Ls : Fin ((T.history N).eventCount + 1)) (hFL : Fs ≤ Ls) (J : Set ℝ)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (T.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (T.history N).horizon), t ∈ J →
      Fs ≤ (T.history N).activeStage ⟨t, h0, h1⟩ ∧ (T.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)
    (t : ℝ) (ht : t ∈ J) (x : (T.history N).backwardSurvivorDomain Fs Ls hFL)
    (u : TangentSpace (𝓡 3) x) : ℝ :=
  (postMetric T t).inner (windowEmbed_SG T N Fs Ls hFL J hJh hst t ht x)
    (mfderiv (𝓡 3) (𝓡 3) (windowEmbed_SG T N Fs Ls hFL J hJh hst t ht) x u)
    (mfderiv (𝓡 3) (𝓡 3) (windowEmbed_SG T N Fs Ls hFL J hJh hst t ht) x u)

/-- `windowQuad` = 固定 history 的 `stageMetric (activeStage t) t` 经 survivor map 的拉回。 -/
theorem windowQuad_eq_SG (T : ObservationTower P g) (N : ℕ)
    (Fs Ls : Fin ((T.history N).eventCount + 1)) (hFL : Fs ≤ Ls) (J : Set ℝ)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (T.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (T.history N).horizon), t ∈ J →
      Fs ≤ (T.history N).activeStage ⟨t, h0, h1⟩ ∧ (T.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)
    (t : ℝ) (ht : t ∈ J) (x : (T.history N).backwardSurvivorDomain Fs Ls hFL)
    (u : TangentSpace (𝓡 3) x) :
    windowQuad_SG T N Fs Ls hFL J hJh hst t ht x u =
      ((T.history N).stageMetric
          ((T.history N).activeStage ⟨t, (hJh t ht).1, (hJh t ht).2⟩) t).inner
        ((T.history N).backwardSurvivorMap Fs Ls hFL
          ((T.history N).activeStage ⟨t, (hJh t ht).1, (hJh t ht).2⟩)
          (hst t (hJh t ht).1 (hJh t ht).2 ht).1 (hst t (hJh t ht).1 (hJh t ht).2 ht).2 x)
        (mfderiv (𝓡 3) (𝓡 3) ((T.history N).backwardSurvivorMap Fs Ls hFL
          ((T.history N).activeStage ⟨t, (hJh t ht).1, (hJh t ht).2⟩)
          (hst t (hJh t ht).1 (hJh t ht).2 ht).1 (hst t (hJh t ht).1 (hJh t ht).2 ht).2) x u)
        (mfderiv (𝓡 3) (𝓡 3) ((T.history N).backwardSurvivorMap Fs Ls hFL
          ((T.history N).activeStage ⟨t, (hJh t ht).1, (hJh t ht).2⟩)
          (hst t (hJh t ht).1 (hJh t ht).2 ht).1 (hst t (hJh t ht).1 (hJh t ht).2 ht).2) x u) :=
  inner_comp_carrierHomeo_SG
    (postStage_eq_stage_active_CPD2 T N ⟨t, (hJh t ht).1, (hJh t ht).2⟩).symm
    (postMetric_heq_stageMetric_ST T N ⟨t, (hJh t ht).1, (hJh t ht).2⟩).symm _ x u u

end Bridge

section Slab

/-- 每个 stage 的 slab（`stageDomain j ⊆ A`）上度量二次型联合连续。 -/
theorem stageMetric_quad_continuousOn_SG (H : ObservedHistory.{u})
    (j : Fin (H.eventCount + 1)) :
    ∃ A : Set ℝ, H.stageDomain j ⊆ A ∧
      ContinuousOn (fun p : ℝ × TangentBundle ThreeModel (H.stage j).Carrier =>
        (H.stageMetric j p.1).inner p.2.proj p.2.2 p.2.2) (A ×ˢ univ) := by
  cases j using Fin.lastCases with
  | last =>
    by_cases hlt : H.time (Fin.last H.eventCount) < H.horizon
    · refine ⟨Icc (H.time (Fin.last H.eventCount)) H.horizon, ?_, ?_⟩
      · simp only [ObservedHistory.stageDomain, Fin.lastCases_last]
        exact subset_rfl
      · have h := (H.finalSlab hlt).equation.smoothMetric.metricQuadratic_continuousOn_carrier
        simp only [ObservedHistory.stageMetric, Fin.lastCases_last, hlt, ↓reduceDIte]
        exact h
    · refine ⟨univ, subset_univ _, ?_⟩
      simp only [ObservedHistory.stageMetric, Fin.lastCases_last, hlt, ↓reduceDIte]
      exact ((metricQuad_cont (H.initialMetric (Fin.last H.eventCount))).comp
        continuous_snd).continuousOn
  | cast i =>
    refine ⟨Ico (H.time i.castSucc) (H.time i.succ), ?_, ?_⟩
    · simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc]
      exact subset_rfl
    · have h := (H.event i).incoming.equation.smoothMetric.metricQuadratic_continuousOn_carrier
      simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]
      exact h

end Slab

section Terminal

/-- event 左侧：`t ↑ s` 时 pre 侧 flow 的度量在 `terminalRegularOpen` 的紧集上与
`terminal.metric` 双向 `e^ε` 接近（`TerminalMetricConverges`，`j = 0`）。 -/
theorem terminal_close_SG (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {K : Set (H.event i).incoming.terminalRegularOpen} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ), ∀ t ∈ Ioo d (H.time i.succ), ∀ x ∈ K,
      ∀ v : TangentSpace ThreeModel x,
        ((H.event i).incoming.flow.base.metric t).inner x.1 v v ≤
            Real.exp ε * (H.event i).terminal.metric.inner x v v ∧
          (H.event i).terminal.metric.inner x v v ≤
            Real.exp ε * ((H.event i).incoming.flow.base.metric t).inner x.1 v v := by
  have hexp : Real.exp (-ε) < 1 := by
    have := Real.exp_lt_exp.mpr (show -ε < 0 by linarith)
    simpa using this
  obtain ⟨d, hd, hdd⟩ := (H.event i).terminal.converges K hK 0 (1 - Real.exp (-ε))
    (by linarith)
  refine ⟨d, hd, fun t ht x hx v => ?_⟩
  have hb := DifferentialGeometry.Geometry.Metric.inner_bounds_of_metricDerivNorm_le
    (H.event i).terminal.metric
    (((H.event i).incoming.flow.base.metric t).restrictOpen
      (H.event i).incoming.terminalRegularOpen) x (hdd t ht x hx).le v
  obtain ⟨hb1, hb2⟩ := hb
  have hnn : 0 ≤ (H.event i).terminal.metric.inner x v v := metric_inner_self_nonneg _ x v
  have h1 : 1 - (1 - Real.exp (-ε)) = Real.exp (-ε) := by ring
  rw [h1] at hb1
  change Real.exp (-ε) * (H.event i).terminal.metric.inner x v v ≤
    ((H.event i).incoming.flow.base.metric t).inner x.1 v v at hb1
  change ((H.event i).incoming.flow.base.metric t).inner x.1 v v ≤
    (1 + (1 - Real.exp (-ε))) * (H.event i).terminal.metric.inner x v v at hb2
  have h2 : 1 + (1 - Real.exp (-ε)) ≤ Real.exp ε := by
    have e1 := Real.add_one_le_exp ε
    have e2 := Real.add_one_le_exp (-ε)
    linarith
  have h3 : Real.exp ε * Real.exp (-ε) = 1 := by rw [← Real.exp_add]; simp
  constructor
  · calc _ ≤ (1 + (1 - Real.exp (-ε))) * (H.event i).terminal.metric.inner x v v := hb2
      _ ≤ Real.exp ε * (H.event i).terminal.metric.inner x v v :=
        mul_le_mul_of_nonneg_right h2 hnn
  · have := mul_le_mul_of_nonneg_left hb1 (Real.exp_pos ε).le
    calc (H.event i).terminal.metric.inner x v v
        = Real.exp ε * Real.exp (-ε) * (H.event i).terminal.metric.inner x v v := by
          rw [h3, one_mul]
      _ = Real.exp ε * (Real.exp (-ε) * (H.event i).terminal.metric.inner x v v) := by ring
      _ ≤ _ := this

/-- event 前一个 stage 的 survivor map（`Φ_{i.castSucc}`）。 -/
abbrev survPre_SG (H : ObservedHistory.{u}) (Fs Ls : Fin (H.eventCount + 1)) (hFL : Fs ≤ Ls)
    (i : Fin H.eventCount) (hf : Fs ≤ i.castSucc) (hl : i.succ ≤ Ls) :
    H.backwardSurvivorDomain Fs Ls hFL → (H.stage i.castSucc).Carrier :=
  H.backwardSurvivorMap Fs Ls hFL i.castSucc hf (i.castSucc_lt_succ.le.trans hl)

/-- event 后一个 stage 的 survivor map（`Φ_{i.succ}`）。 -/
abbrev survPost_SG (H : ObservedHistory.{u}) (Fs Ls : Fin (H.eventCount + 1)) (hFL : Fs ≤ Ls)
    (i : Fin H.eventCount) (hf : Fs ≤ i.castSucc) (hl : i.succ ≤ Ls) :
    H.backwardSurvivorDomain Fs Ls hFL → (H.stage i.succ).Carrier :=
  H.backwardSurvivorMap Fs Ls hFL i.succ (hf.trans i.castSucc_lt_succ.le) hl

/-- event 左侧在 survivor domain `D` 的坐标里：`t ↑ time i.succ` 时 pre-stage 度量经
`Φ_{i.castSucc}` 的拉回与 post-stage `initialMetric i.succ` 经 `Φ_{i.succ}` 的拉回在紧集上
双向 `e^ε` 接近（`backwardSurvivorMap_metric_crossing` + `terminal_close_SG`）。 -/
theorem left_event_close_SG (H : ObservedHistory.{u}) (Fs Ls : Fin (H.eventCount + 1))
    (hFL : Fs ≤ Ls) (i : Fin H.eventCount) (hf : Fs ≤ i.castSucc) (hl : i.succ ≤ Ls)
    {K : Set (H.backwardSurvivorDomain Fs Ls hFL)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ d ∈ Ico (H.time i.castSucc) (H.time i.succ), ∀ t ∈ Ioo d (H.time i.succ), ∀ x ∈ K,
      ∀ u : TangentSpace ThreeModel x,
        ((H.event i).incoming.flow.base.metric t).inner (survPre_SG H Fs Ls hFL i hf hl x)
            (mfderiv ThreeModel ThreeModel (survPre_SG H Fs Ls hFL i hf hl) x u)
            (mfderiv ThreeModel ThreeModel (survPre_SG H Fs Ls hFL i hf hl) x u) ≤
          Real.exp ε * (H.initialMetric i.succ).inner (survPost_SG H Fs Ls hFL i hf hl x)
            (mfderiv ThreeModel ThreeModel (survPost_SG H Fs Ls hFL i hf hl) x u)
            (mfderiv ThreeModel ThreeModel (survPost_SG H Fs Ls hFL i hf hl) x u) ∧
        (H.initialMetric i.succ).inner (survPost_SG H Fs Ls hFL i hf hl x)
            (mfderiv ThreeModel ThreeModel (survPost_SG H Fs Ls hFL i hf hl) x u)
            (mfderiv ThreeModel ThreeModel (survPost_SG H Fs Ls hFL i hf hl) x u) ≤
          Real.exp ε * ((H.event i).incoming.flow.base.metric t).inner
            (survPre_SG H Fs Ls hFL i hf hl x)
            (mfderiv ThreeModel ThreeModel (survPre_SG H Fs Ls hFL i hf hl) x u)
            (mfderiv ThreeModel ThreeModel (survPre_SG H Fs Ls hFL i hf hl) x u) := by
  let T := H.backwardSurvivorTerminalMap Fs Ls hFL i hf hl
  have hTc : Continuous T :=
    (H.backwardSurvivorTerminalMap_isSmoothEmbedding Fs Ls hFL i hf hl).isEmbedding.continuous
  obtain ⟨d, hd, hdd⟩ := terminal_close_SG H i (hK.image hTc) hε
  refine ⟨d, hd, fun t ht x hx u => ?_⟩
  have hTs : ContMDiff ThreeModel ThreeModel ∞ T :=
    (H.backwardSurvivorTerminalMap_isSmoothEmbedding Fs Ls hFL i hf hl).contMDiff
  have hmet := H.backwardSurvivorMap_metric_crossing Fs Ls hFL i hf hl x u u
  have hpre : mfderiv ThreeModel ThreeModel (survPre_SG H Fs Ls hFL i hf hl) x u =
      mfderiv ThreeModel ThreeModel T x u := by
    have hcomp : mfderiv ThreeModel ThreeModel (fun y => (T y).1) x =
        (mfderiv ThreeModel ThreeModel (Subtype.val :
          (H.event i).incoming.terminalRegularOpen → (H.stage i.castSucc).Carrier) (T x)).comp
          (mfderiv ThreeModel ThreeModel T x) :=
      mfderiv_comp x (hasMFDerivAt_subtype_val (I := ThreeModel) _ (T x)).mdifferentiableAt
        ((hTs x).mdifferentiableAt (by simp))
    change mfderiv ThreeModel ThreeModel (fun y => (T y).1) x u = _
    rw [hcomp, ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]
  have hb := hdd t ht (T x) ⟨x, hx, rfl⟩ (mfderiv ThreeModel ThreeModel T x u)
  rw [hmet, hpre]
  exact hb

end Terminal

section SameStage

/-- 同一个 stage `j` 里、`τ₀ ∈ stageDomain j`：`t → τ₀`（`t ∈ stageDomain j`）时在 `D` 的紧集上
`stageMetric j t` 经 `Φ_j` 的拉回与 `stageMetric j τ₀` 的拉回双向 `e^ε` 接近。 -/
theorem same_stage_close_SG (H : ObservedHistory.{u}) (Fs Ls : Fin (H.eventCount + 1))
    (hFL : Fs ≤ Ls) (j : Fin (H.eventCount + 1)) (hfj : Fs ≤ j) (hjl : j ≤ Ls) {τ₀ : ℝ}
    (hτ : τ₀ ∈ H.stageDomain j) {K : Set (H.backwardSurvivorDomain Fs Ls hFL)}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ H.stageDomain j, |t - τ₀| < δ → ∀ x ∈ K, ∀ u : TangentSpace ThreeModel x,
      (H.stageMetric j t).inner (H.backwardSurvivorMap Fs Ls hFL j hfj hjl x)
          (mfderiv ThreeModel ThreeModel (H.backwardSurvivorMap Fs Ls hFL j hfj hjl) x u)
          (mfderiv ThreeModel ThreeModel (H.backwardSurvivorMap Fs Ls hFL j hfj hjl) x u) ≤
        Real.exp ε * (H.stageMetric j τ₀).inner (H.backwardSurvivorMap Fs Ls hFL j hfj hjl x)
          (mfderiv ThreeModel ThreeModel (H.backwardSurvivorMap Fs Ls hFL j hfj hjl) x u)
          (mfderiv ThreeModel ThreeModel (H.backwardSurvivorMap Fs Ls hFL j hfj hjl) x u) ∧
      (H.stageMetric j τ₀).inner (H.backwardSurvivorMap Fs Ls hFL j hfj hjl x)
          (mfderiv ThreeModel ThreeModel (H.backwardSurvivorMap Fs Ls hFL j hfj hjl) x u)
          (mfderiv ThreeModel ThreeModel (H.backwardSurvivorMap Fs Ls hFL j hfj hjl) x u) ≤
        Real.exp ε * (H.stageMetric j t).inner (H.backwardSurvivorMap Fs Ls hFL j hfj hjl x)
          (mfderiv ThreeModel ThreeModel (H.backwardSurvivorMap Fs Ls hFL j hfj hjl) x u)
          (mfderiv ThreeModel ThreeModel (H.backwardSurvivorMap Fs Ls hFL j hfj hjl) x u) := by
  obtain ⟨A, hA, hcont⟩ := stageMetric_quad_continuousOn_SG H j
  have hΦc : Continuous (H.backwardSurvivorMap Fs Ls hFL j hfj hjl) :=
    (H.backwardSurvivorMap_isLocalDiffeomorph Fs Ls hFL j hfj hjl).contMDiff.continuous
  obtain ⟨δ, hδ, hclose⟩ := exists_quadratic_close_SG (H.stageMetric j) A τ₀ (hA hτ) hcont
    (hK.image hΦc) hε
  exact ⟨δ, hδ, fun t ht hdt x hx u => hclose t (hA ht) hdt _ ⟨x, hx, rfl⟩ _⟩

end SameStage

section Active

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- active stage 已知等于 `j` 时的 `windowQuad`（`windowQuad_eq_SG` 的 `subst` 版）。 -/
theorem windowQuad_eq_of_active_SG (T : ObservationTower P g) (N : ℕ)
    (Fs Ls : Fin ((T.history N).eventCount + 1)) (hFL : Fs ≤ Ls) (J : Set ℝ)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (T.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (T.history N).horizon), t ∈ J →
      Fs ≤ (T.history N).activeStage ⟨t, h0, h1⟩ ∧ (T.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)
    (t : ℝ) (ht : t ∈ J) (x : (T.history N).backwardSurvivorDomain Fs Ls hFL)
    (u : TangentSpace (𝓡 3) x) (j : Fin ((T.history N).eventCount + 1))
    (hact : (T.history N).activeStage ⟨t, (hJh t ht).1, (hJh t ht).2⟩ = j)
    (hfj : Fs ≤ j) (hjl : j ≤ Ls) :
    windowQuad_SG T N Fs Ls hFL J hJh hst t ht x u =
      ((T.history N).stageMetric j t).inner
        ((T.history N).backwardSurvivorMap Fs Ls hFL j hfj hjl x)
        (mfderiv (𝓡 3) (𝓡 3) ((T.history N).backwardSurvivorMap Fs Ls hFL j hfj hjl) x u)
        (mfderiv (𝓡 3) (𝓡 3) ((T.history N).backwardSurvivorMap Fs Ls hFL j hfj hjl) x u) := by
  subst hact
  exact windowQuad_eq_SG T N Fs Ls hFL J hJh hst t ht x u

/-- 右侧（含 `t = τ₀`）：`τ₀ ≤ t`、`|t - τ₀|` 小时与 `G(τ₀)` 在 `D` 的紧集上双向 `e^ε` 接近。 -/
theorem window_quad_right_close_SG (T : ObservationTower P g) (N : ℕ)
    (Fs Ls : Fin ((T.history N).eventCount + 1)) (hFL : Fs ≤ Ls) (J : Set ℝ)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (T.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (T.history N).horizon), t ∈ J →
      Fs ≤ (T.history N).activeStage ⟨t, h0, h1⟩ ∧ (T.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)
    {τ₀ : ℝ} (hτ : τ₀ ∈ J) {K : Set ((T.history N).backwardSurvivorDomain Fs Ls hFL)}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t (ht : t ∈ J), τ₀ ≤ t → |t - τ₀| < δ → ∀ x ∈ K, ∀ u : TangentSpace (𝓡 3) x,
      windowQuad_SG T N Fs Ls hFL J hJh hst t ht x u ≤
          Real.exp ε * windowQuad_SG T N Fs Ls hFL J hJh hst τ₀ hτ x u ∧
        windowQuad_SG T N Fs Ls hFL J hJh hst τ₀ hτ x u ≤
          Real.exp ε * windowQuad_SG T N Fs Ls hFL J hJh hst t ht x u := by
  have h0 := (hJh τ₀ hτ).1
  have h1 := (hJh τ₀ hτ).2
  have hstτ := hst τ₀ h0 h1 hτ
  have hmemτ : τ₀ ∈ (T.history N).stageDomain ((T.history N).activeStage ⟨τ₀, h0, h1⟩) :=
    (T.history N).activeStage_mem ⟨τ₀, h0, h1⟩
  obtain ⟨δR, hδR, hR⟩ := exists_right_const_activeStage_CPD7 (T.history N) h0 h1
  obtain ⟨δ1, hδ1, hc⟩ := same_stage_close_SG (T.history N) Fs Ls hFL
    ((T.history N).activeStage ⟨τ₀, h0, h1⟩) hstτ.1 hstτ.2 hmemτ hK hε
  refine ⟨min δR δ1, lt_min hδR hδ1, fun t ht hle hdt x hx u => ?_⟩
  have h0' := (hJh t ht).1
  have h1' := (hJh t ht).2
  have hact : (T.history N).activeStage ⟨t, h0', h1'⟩ =
      (T.history N).activeStage ⟨τ₀, h0, h1⟩ := by
    apply hR t h0' h1' hle
    have := (abs_lt.mp hdt).2
    have := min_le_left δR δ1
    linarith
  have htmem : t ∈ (T.history N).stageDomain ((T.history N).activeStage ⟨τ₀, h0, h1⟩) := by
    have := (T.history N).activeStage_mem ⟨t, h0', h1'⟩
    rwa [hact] at this
  rw [windowQuad_eq_of_active_SG T N Fs Ls hFL J hJh hst t ht x u _ hact hstτ.1 hstτ.2,
    windowQuad_eq_of_active_SG T N Fs Ls hFL J hJh hst τ₀ hτ x u _ rfl hstτ.1 hstτ.2]
  exact hc t htmem (lt_of_lt_of_le hdt (min_le_right _ _)) x hx u

/-- `stageMetric (castSucc i)` 就是 pre-stage 的 incoming flow 的度量。 -/
theorem stageMetric_castSucc_SG (H : ObservedHistory.{u}) (i : Fin H.eventCount) :
    H.stageMetric i.castSucc = (H.event i).incoming.flow.base.metric := by
  simp [ObservedHistory.stageMetric]

/-- event 时刻 `time i.succ` 左侧一小段上 active stage 是 `i.castSucc`。 -/
theorem activeStage_left_event_SG (H : ObservedHistory.{u}) (i : Fin H.eventCount) (t : ℝ)
    (h0 : 0 ≤ t) (h1 : t ≤ H.horizon) (ha : H.time i.castSucc < t) (hb : t < H.time i.succ) :
    H.activeStage ⟨t, h0, h1⟩ = i.castSucc := by
  apply le_antisymm
  · by_contra hcon
    have hlt : i.castSucc < H.activeStage ⟨t, h0, h1⟩ := lt_of_not_ge hcon
    have hsucc : i.succ ≤ H.activeStage ⟨t, h0, h1⟩ := Fin.castSucc_lt_iff_succ_le.mp hlt
    have h2 := H.time_strictMono.monotone hsucc
    have h3 := H.activeStage_time_le ⟨t, h0, h1⟩
    simp only at h3
    linarith
  · exact H.le_activeStage ⟨t, h0, h1⟩ i.castSucc ha.le

/-- 左侧（`t < τ₀`）：`|t - τ₀|` 小时与 `G(τ₀)` 在 `D` 的紧集上双向 `e^ε` 接近；
`τ₀` 是 event 时刻时用 `TerminalMetricConverges`。 -/
theorem window_quad_left_close_SG (T : ObservationTower P g) (N : ℕ)
    (Fs Ls : Fin ((T.history N).eventCount + 1)) (hFL : Fs ≤ Ls) (J : Set ℝ)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (T.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (T.history N).horizon), t ∈ J →
      Fs ≤ (T.history N).activeStage ⟨t, h0, h1⟩ ∧ (T.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)
    {τ₀ : ℝ} (hτ0 : 0 < τ₀) (hτ : τ₀ ∈ J) (hJo : IsOpen J)
    {K : Set ((T.history N).backwardSurvivorDomain Fs Ls hFL)}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t (ht : t ∈ J), t < τ₀ → |t - τ₀| < δ → ∀ x ∈ K, ∀ u : TangentSpace (𝓡 3) x,
      windowQuad_SG T N Fs Ls hFL J hJh hst t ht x u ≤
          Real.exp ε * windowQuad_SG T N Fs Ls hFL J hJh hst τ₀ hτ x u ∧
        windowQuad_SG T N Fs Ls hFL J hJh hst τ₀ hτ x u ≤
          Real.exp ε * windowQuad_SG T N Fs Ls hFL J hJh hst t ht x u := by
  have h0 := (hJh τ₀ hτ).1
  have h1 := (hJh τ₀ hτ).2
  have hstτ := hst τ₀ h0 h1 hτ
  have hmemτ : τ₀ ∈ (T.history N).stageDomain ((T.history N).activeStage ⟨τ₀, h0, h1⟩) :=
    (T.history N).activeStage_mem ⟨τ₀, h0, h1⟩
  have htime : (T.history N).time ((T.history N).activeStage ⟨τ₀, h0, h1⟩) ≤ τ₀ :=
    (T.history N).activeStage_time_le ⟨τ₀, h0, h1⟩
  obtain ⟨δJ, hδJ, hball⟩ := Metric.isOpen_iff.mp hJo τ₀ hτ
  by_cases hB : (T.history N).time ((T.history N).activeStage ⟨τ₀, h0, h1⟩) = τ₀
  · -- event 时刻：左侧是前一个 stage
    have hj0 : (T.history N).activeStage ⟨τ₀, h0, h1⟩ ≠ 0 := by
      intro hz
      rw [hz, (T.history N).time_zero] at hB
      linarith
    obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr hj0
    have hactτ : (T.history N).activeStage ⟨τ₀, h0, h1⟩ = i.succ := hi.symm
    have hBi : (T.history N).time i.succ = τ₀ := by rw [← hactτ]; exact hB
    have hl : i.succ ≤ Ls := hactτ ▸ hstτ.2
    have hlt : (T.history N).time i.castSucc < τ₀ := by
      rw [← hBi]; exact (T.history N).time_strictMono i.castSucc_lt_succ
    -- 左侧存在 `J` 里的点，推出 `Fs ≤ i.castSucc`
    have hf : Fs ≤ i.castSucc := by
      set t₁ : ℝ := max (τ₀ - δJ / 2) (((T.history N).time i.castSucc + τ₀) / 2) with ht₁
      have ht1a : (T.history N).time i.castSucc < t₁ :=
        lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have ht1b : t₁ < τ₀ := max_lt (by linarith) (by linarith)
      have ht1J : t₁ ∈ J := hball (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor
        · have := le_max_left (τ₀ - δJ / 2) (((T.history N).time i.castSucc + τ₀) / 2)
          linarith
        · linarith)
      have hh := hst t₁ (hJh t₁ ht1J).1 (hJh t₁ ht1J).2 ht1J
      rw [activeStage_left_event_SG (T.history N) i t₁ (hJh t₁ ht1J).1 (hJh t₁ ht1J).2 ht1a
        (hBi ▸ ht1b)] at hh
      exact hh.1
    have hlc : i.castSucc ≤ Ls := i.castSucc_lt_succ.le.trans hl
    obtain ⟨d, hd, hdd⟩ := left_event_close_SG (T.history N) Fs Ls hFL i hf hl hK hε
    have hdlt : d < τ₀ := by rw [← hBi]; exact hd.2
    refine ⟨τ₀ - d, by linarith, fun t ht hlt' hdt x hx u => ?_⟩
    have htd : d < t := by have := (abs_lt.mp hdt).1; linarith
    have htmem : t ∈ Ioo d ((T.history N).time i.succ) := ⟨htd, hBi ▸ hlt'⟩
    have hact : (T.history N).activeStage ⟨t, (hJh t ht).1, (hJh t ht).2⟩ = i.castSucc :=
      activeStage_left_event_SG (T.history N) i t (hJh t ht).1 (hJh t ht).2
        (lt_of_le_of_lt hd.1 htd) htmem.2
    rw [windowQuad_eq_of_active_SG T N Fs Ls hFL J hJh hst t ht x u _ hact hf hlc,
      windowQuad_eq_of_active_SG T N Fs Ls hFL J hJh hst τ₀ hτ x u _ hactτ
        (hf.trans i.castSucc_lt_succ.le) hl]
    have e : (T.history N).stageMetric i.succ τ₀ = (T.history N).initialMetric i.succ := by
      have := stageMetric_time_ST (T.history N) i.succ
      rwa [hBi] at this
    rw [e, stageMetric_castSucc_SG]
    exact hdd t htmem x hx u
  · have hlt : (T.history N).time ((T.history N).activeStage ⟨τ₀, h0, h1⟩) < τ₀ :=
      lt_of_le_of_ne htime hB
    obtain ⟨δ1, hδ1, hc⟩ := same_stage_close_SG (T.history N) Fs Ls hFL
      ((T.history N).activeStage ⟨τ₀, h0, h1⟩) hstτ.1 hstτ.2 hmemτ hK hε
    refine ⟨min δ1 (τ₀ - (T.history N).time ((T.history N).activeStage ⟨τ₀, h0, h1⟩)),
      lt_min hδ1 (by linarith), fun t ht hlt' hdt x hx u => ?_⟩
    have h0' := (hJh t ht).1
    have h1' := (hJh t ht).2
    have hta : (T.history N).time ((T.history N).activeStage ⟨τ₀, h0, h1⟩) < t := by
      have := (abs_lt.mp hdt).1
      have := min_le_right δ1 (τ₀ - (T.history N).time ((T.history N).activeStage ⟨τ₀, h0, h1⟩))
      linarith
    have hact : (T.history N).activeStage ⟨t, h0', h1'⟩ =
        (T.history N).activeStage ⟨τ₀, h0, h1⟩ :=
      le_antisymm ((T.history N).activeStage_mono (a := ⟨t, h0', h1'⟩) (b := ⟨τ₀, h0, h1⟩)
        hlt'.le) ((T.history N).le_activeStage ⟨t, h0', h1'⟩ _ hta.le)
    have htmem : t ∈ (T.history N).stageDomain ((T.history N).activeStage ⟨τ₀, h0, h1⟩) := by
      have := (T.history N).activeStage_mem ⟨t, h0', h1'⟩
      rwa [hact] at this
    rw [windowQuad_eq_of_active_SG T N Fs Ls hFL J hJh hst t ht x u _ hact hstτ.1 hstτ.2,
      windowQuad_eq_of_active_SG T N Fs Ls hFL J hJh hst τ₀ hτ x u _ rfl hstτ.1 hstτ.2]
    exact hc t htmem (lt_of_lt_of_le hdt (min_le_left _ _)) x hx u

/-- 两侧合并（`δ` 取 min）。 -/
theorem window_quad_close_SG (T : ObservationTower P g) (N : ℕ)
    (Fs Ls : Fin ((T.history N).eventCount + 1)) (hFL : Fs ≤ Ls) (J : Set ℝ)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (T.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (T.history N).horizon), t ∈ J →
      Fs ≤ (T.history N).activeStage ⟨t, h0, h1⟩ ∧ (T.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)
    {τ₀ : ℝ} (hτ0 : 0 < τ₀) (hτ : τ₀ ∈ J) (hJo : IsOpen J)
    {K : Set ((T.history N).backwardSurvivorDomain Fs Ls hFL)}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t (ht : t ∈ J), |t - τ₀| < δ → ∀ x ∈ K, ∀ u : TangentSpace (𝓡 3) x,
      windowQuad_SG T N Fs Ls hFL J hJh hst t ht x u ≤
          Real.exp ε * windowQuad_SG T N Fs Ls hFL J hJh hst τ₀ hτ x u ∧
        windowQuad_SG T N Fs Ls hFL J hJh hst τ₀ hτ x u ≤
          Real.exp ε * windowQuad_SG T N Fs Ls hFL J hJh hst t ht x u := by
  obtain ⟨δL, hδL, hL⟩ := window_quad_left_close_SG T N Fs Ls hFL J hJh hst hτ0 hτ hJo hK hε
  obtain ⟨δR, hδR, hR⟩ := window_quad_right_close_SG T N Fs Ls hFL J hJh hst hτ hK hε
  refine ⟨min δL δR, lt_min hδL hδR, fun t ht hdt x hx u => ?_⟩
  rcases lt_or_ge t τ₀ with hlt | hge
  · exact hL t ht hlt (lt_of_lt_of_le hdt (min_le_left _ _)) x hx u
  · exact hR t ht hge (lt_of_lt_of_le hdt (min_le_right _ _)) x hx u

end Active

end GC.LongTime.CuspP1

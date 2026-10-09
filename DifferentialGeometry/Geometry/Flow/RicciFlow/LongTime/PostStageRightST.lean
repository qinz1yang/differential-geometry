import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PostStageGeneralST
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PostMetricSmoothST
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureContinuity

/-!
# 右端点识别：`[a, b)` 上的 `postStage` / `postMetric`（lane S-A14-STATIC，G7a）

G1/G5 的 metric 识别要求 `time (activeStage t) < t`（或只给任意 `t` 的 HEq，没有 flow）。
手术时刻 `t₀`（`t₀ = time i.succ`）的 barrier / HT-R 用 post-surgery stage，那里 stage 恰于 `t₀` 开始，
所以 `Ioo` 版本的 G1/G2 不够。本文件给出右端点版本（`a` 允许是 event 时刻，只要求
`∀ s ∈ O.eventTimes, s ∉ Ioo a b`）：

* `postMetric_heq_outgoing_initial_ST`、`postStage_eq_outgoing_ST`、`postMetric_heq_outputMetric_ST`：
  `postMetric O (time i.succ)` 就是 outgoing stage `i.succ` 的 `initialMetric`
  （= `(event i).outputMetric`）；
* `postStage_eq_of_no_event_right_ST`：`Ico a b` 上 `postStage` 不变；
* `exists_stageFlow_right_of_no_event_ST`：`Ico a b ⊆ D.carrier`、`Ioo a b ⊆ D.regular` 的
  stage flow `S`，
  `MetricFamilySmoothOn D S.base.metric`（`[a, b)` 上，含端点 `a` 的单侧光滑）、
  `S.base.metric a = postMetric O a`、`(a, b)` 上 `∂ₜ g = -2 Ric` 的 `HasDerivAt`，以及 **`a` 处的
  右导数** `HasDerivWithinAt … (Ici a) a`（`hasDerivWithinAt_ricci_right_ST`：光滑延拓 `F` 的导数连续
  + `IsSolutionOn.continuousOn_ricciTensor` 的右连续 ⇒ 极限相等）；
* `exists_noEvent_right_interval_ST`：每个 `t₀`（可以是 event 时刻）右边都有无新事件的 `Ioo t₀ b`。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace GC.LongTime

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- 右端点版：`Ico a b` 内无事件（允许 `a` 本身是事件时刻）⇒ `activeStage` 常值。 -/
theorem activeStage_eq_of_no_event_right_ST (O : ObservationTower P g) (n : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t t' : ℝ}
    (ht : t ∈ Ico a b) (ht' : t' ∈ Ico a b) (htt : t ≤ t') (ht0 : 0 ≤ t) (ht'0 : 0 ≤ t')
    (htn : t ≤ n) (ht'n : t' ≤ n) :
    (O.history n).activeStage (timeIn_ST O n ht0 htn) =
      (O.history n).activeStage (timeIn_ST O n ht'0 ht'n) := by
  refine le_antisymm ((O.history n).activeStage_mono htt) ?_
  refine (O.history n).le_activeStage _ _ ?_
  by_contra hlt
  rw [not_le] at hlt
  have hj := (O.history n).activeStage_time_le (timeIn_ST O n ht'0 ht'n)
  generalize (O.history n).activeStage (timeIn_ST O n ht'0 ht'n) = j at hlt hj
  cases j using Fin.cases with
  | zero =>
    rw [(O.history n).time_zero] at hlt
    exact absurd (ha.trans ht.1) (not_le.mpr hlt)
  | succ i =>
    have hmem : (O.history n).time i.succ ∈ O.eventTimes := Set.mem_iUnion.2 ⟨n, i, rfl⟩
    exact hno _ hmem ⟨ht.1.trans_lt hlt, hj.trans_lt ht'.2⟩

/-- `Ico a b` 上 `postStage` 不变（`a` 可以是 event 时刻）。 -/
theorem postStage_eq_of_no_event_right_ST (O : ObservationTower P g) {a b : ℝ} (ha : 0 ≤ a)
    (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t t' : ℝ} (ht : t ∈ Ico a b)
    (ht' : t' ∈ Ico a b) : postStage O t = postStage O t' := by
  have key : ∀ {t t' : ℝ}, t ∈ Ico a b → t' ∈ Ico a b → t ≤ t' →
      postStage O t = postStage O t' := by
    intro t t' ht ht' htt
    have ht0 : 0 ≤ t := ha.trans ht.1
    have ht'0 : 0 ≤ t' := ha.trans ht'.1
    have htn : t ≤ (⌈b⌉₊ : ℕ) := ht.2.le.trans (Nat.le_ceil b)
    have ht'n : t' ≤ (⌈b⌉₊ : ℕ) := ht'.2.le.trans (Nat.le_ceil b)
    rw [postStage_eq_history_ST O ⌈b⌉₊ ht0 htn, postStage_eq_history_ST O ⌈b⌉₊ ht'0 ht'n,
      activeStage_eq_of_no_event_right_ST O ⌈b⌉₊ ha hno ht ht' htt ht0 ht'0 htn ht'n]
  rcases le_total t t' with h | h
  · exact key ht ht' h
  · exact (key ht' ht h).symm

/-- event 时刻 `time i.succ` 的 `postStage` 是 outgoing stage `i.succ`。 -/
theorem postStage_eq_outgoing_ST (O : ObservationTower P g) (n : ℕ)
    (i : Fin (O.history n).eventCount)
    (hn : (O.history n).time i.succ ≤ (O.history n).horizon) :
    postStage O ((O.history n).time i.succ) = (O.history n).stage i.succ := by
  have h := postStage_eq_activeStage_ST O n
    ⟨(O.history n).time i.succ, (O.history n).time_nonneg _, hn⟩
  exact h.trans (congrArg (O.history n).stage ((O.history n).activeStage_at_time i.succ))

/-- **G7**：`postMetric O (time i.succ)` 是 outgoing stage 的 `initialMetric`（`HEq`）。 -/
theorem postMetric_heq_outgoing_initial_ST (O : ObservationTower P g) (n : ℕ)
    (i : Fin (O.history n).eventCount)
    (hn : (O.history n).time i.succ ≤ (O.history n).horizon) :
    HEq (postMetric O ((O.history n).time i.succ)) ((O.history n).initialMetric i.succ) := by
  have h := postMetric_heq_stageMetric_ST O n
    ⟨(O.history n).time i.succ, (O.history n).time_nonneg _, hn⟩
  have hact := (O.history n).activeStage_at_time i.succ
  have key : ∀ j : Fin ((O.history n).eventCount + 1), j = i.succ →
      HEq ((O.history n).stageMetric j ((O.history n).time i.succ))
        ((O.history n).initialMetric i.succ) := by
    intro j hj
    subst hj
    exact heq_of_eq (stageMetric_time_ST (O.history n) _)
  exact h.trans (key _ hact)

/-- `postMetric O (time i.succ)` 就是 `(event i).outputMetric`（`HEq`）。 -/
theorem postMetric_heq_outputMetric_ST (O : ObservationTower P g) (n : ℕ)
    (i : Fin (O.history n).eventCount)
    (hn : (O.history n).time i.succ ≤ (O.history n).horizon) :
    HEq (postMetric O ((O.history n).time i.succ)) ((O.history n).event i).outputMetric := by
  rw [(O.history n).event_output i]
  exact postMetric_heq_outgoing_initial_ST O n i hn

/-- `MetricSmoothUpTo m J`、`t₁ ∈ J`（不要求内点）：`s ↦ (m s).inner x v w` 在 `J` 上等于某个
`t₁` 处 `C^∞` 的函数 `F`（chart frame 系数的光滑延拓）。 -/
theorem exists_contDiffAt_ext_inner_ST (Q : OrientedThreeStage.{u}) (m : ℝ → Q.Metric)
    (J : Set ℝ) (hsm : Q.MetricSmoothUpTo m J) {t₁ : ℝ} (ht₁ : t₁ ∈ J) (x : Q.Carrier)
    (v w : TangentSpace ThreeModel x) :
    ∃ F : ℝ → ℝ, ContDiffAt ℝ ∞ F t₁ ∧ ∀ᶠ s in 𝓝 t₁, s ∈ J → (m s).inner x v w = F s := by
  obtain ⟨U, hU, hxU, hbase, V, hV, ht₁V, A, hA, heq⟩ := hsm x t₁ ht₁
  have hA' : ∀ i j : Fin 3, ContDiffAt ℝ ∞ (fun s : ℝ => A (s, x) i j) t₁ := by
    intro i j
    have h1 : ContMDiffAt (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞ (fun z => A z i j) (t₁, x) :=
      (hA i j).contMDiffAt ((hV.prod hU).mem_nhds ⟨ht₁V, hxU⟩)
    have h2 : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod ThreeModel) ∞ (fun s : ℝ => (s, x)) t₁ :=
      contMDiffAt_id.prodMk contMDiffAt_const
    exact contMDiffAt_iff_contDiffAt.mp (h1.comp t₁ h2)
  refine ⟨fun s : ℝ => ∑ i : Fin 3, ∑ j : Fin 3,
      ((trivializationAt ThreeSpace (TangentSpace ThreeModel) x).continuousLinearMapAt ℝ x v i) *
      ((trivializationAt ThreeSpace (TangentSpace ThreeModel) x).continuousLinearMapAt ℝ x w j) *
        A (s, x) i j,
    ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => contDiffAt_const.mul (hA' i j), ?_⟩
  filter_upwards [hV.mem_nhds ht₁V] with s hs hsJ
  rw [inner_eq_sum_chartVector_ST Q x x (hbase hxU) (m s) v w]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [heq s ⟨hs, hsJ⟩ x hxU i j]

/-- 右端点版 Ricci flow 方程：`[a, b)` 落在 flow 的时间区间里、`(a, b)` 是 regular 时间时，
`∂ₜ g(x; A, B)` 在 `a` 处的右导数是 `-2 Ric_{g a}(x; A, B)`。 -/
theorem hasDerivWithinAt_ricci_right_ST {Q : OrientedThreeStage.{u}} {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := Q.Carrier) D) (hS : IsSolutionOn S)
    (hsm : Q.MetricSmoothUpTo S.base.metric D.carrier) {a b : ℝ} (hab : a < b)
    (hcar : Ico a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular) (x : Q.Carrier)
    (A B : TangentSpace ThreeModel x) :
    HasDerivWithinAt (fun r : ℝ => (S.base.metric r).inner x A B)
      (-2 * ricciTensor (I := ThreeModel) (S.base.metric a) x A B) (Ici a) a := by
  have haD : a ∈ D.carrier := hcar ⟨le_rfl, hab⟩
  obtain ⟨F, hF, hev⟩ := exists_contDiffAt_ext_inner_ST Q S.base.metric D.carrier hsm haD x A B
  have hFd : HasDerivAt F (deriv F a) a := (hF.differentiableAt (by simp)).hasDerivAt
  have hIco : Ico a b ∈ 𝓝[Ici a] a := Ico_mem_nhdsGE hab
  have hevw : (fun r : ℝ => (S.base.metric r).inner x A B) =ᶠ[𝓝[Ici a] a] F := by
    have h1 : ∀ᶠ s in 𝓝[Ici a] a, s ∈ D.carrier → (S.base.metric s).inner x A B = F s :=
      nhdsWithin_le_nhds hev
    filter_upwards [h1, hIco] with s hs hsI using hs (hcar hsI)
  have hfa : (S.base.metric a).inner x A B = F a := hev.self_of_nhds haD
  have h2 : deriv F a = -2 * ricciTensor (I := ThreeModel) (S.base.metric a) x A B := by
    have hcontF : ContinuousAt (deriv F) a := (hF.derivWithin (m := 0) (by simp)).continuousAt
    have T1 : Tendsto (deriv F) (𝓝[>] a) (𝓝 (deriv F a)) :=
      hcontF.tendsto.mono_left nhdsWithin_le_nhds
    have hRic := (hS.continuousOn_ricciTensor x A B).continuousWithinAt haD
    have hIoo : Ioo a b ∈ 𝓝[>] a := Ioo_mem_nhdsGT hab
    have hsub : 𝓝[>] a ≤ 𝓝[D.carrier] a :=
      nhdsWithin_le_iff.2 (mem_of_superset hIoo fun s hs => hcar ⟨hs.1.le, hs.2⟩)
    have T2 : Tendsto (fun s => -2 * ricciTensor (I := ThreeModel) (S.base.metric s) x A B)
        (𝓝[>] a) (𝓝 (-2 * ricciTensor (I := ThreeModel) (S.base.metric a) x A B)) :=
      (hRic.tendsto.const_mul (-2)).mono_left hsub
    obtain ⟨O, hOsub, hOo, haO⟩ := mem_nhds_iff.1 hev
    have T3 : ∀ᶠ s in 𝓝[>] a,
        deriv F s = -2 * ricciTensor (I := ThreeModel) (S.base.metric s) x A B := by
      filter_upwards [hIoo, mem_nhdsWithin_of_mem_nhds (hOo.mem_nhds haO)] with s hs hsO
      have hd := (hS.equation ⟨s, hreg hs⟩ x A B).hasDerivAt
        (D.regular_mem_nhds (hreg hs))
      have hric : RicciAtFamily.toTensorField (I := ThreeModel) S.ricciAt s x A B =
          ricciTensor (I := ThreeModel) (S.base.metric s) x A B :=
        DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor (I := ThreeModel) _ x A B
      rw [hric] at hd
      have hFe : F =ᶠ[𝓝 s] fun r : ℝ => (S.base.metric r).inner x A B := by
        filter_upwards [(hOo.inter isOpen_Ioo).mem_nhds (show s ∈ O ∩ Ioo a b from ⟨hsO, hs⟩)]
          with r hr
        exact (hOsub hr.1 (hcar ⟨hr.2.1.le, hr.2.2⟩)).symm
      exact (hd.congr_of_eventuallyEq hFe).deriv
    exact tendsto_nhds_unique T1 (T2.congr' (T3.mono fun s hs => hs.symm))
  rw [← h2]
  exact hFd.hasDerivWithinAt.congr_of_eventuallyEq hevw hfa

/-- 单个 stage `j` 上的右端点版本：`[a, b)` 落在该 stage 的时间区间里（`time j ≤ a`），
`(a, b)` 是 regular 时间。 -/
theorem exists_stage_flow_right_ST (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1))
    {a b : ℝ} (hab : a < b) (hj : H.time j ≤ a)
    (hnext : ∀ i : Fin H.eventCount, j = i.castSucc → b ≤ H.time i.succ)
    (hlast : j = Fin.last H.eventCount → b ≤ H.horizon) :
    ∃ (D : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := (H.stage j).Carrier) D),
      IsSolutionOn S ∧ (H.stage j).MetricSmoothUpTo S.base.metric D.carrier ∧
        Ico a b ⊆ D.carrier ∧ Ioo a b ⊆ D.regular ∧
        ∀ s ∈ Ico a b, S.base.metric s = H.stageMetric j s := by
  cases j using Fin.lastCases with
  | last =>
    have h : H.time (Fin.last H.eventCount) < H.horizon :=
      lt_of_le_of_lt hj (lt_of_lt_of_le hab (hlast rfl))
    refine ⟨RealTimeInterval.closed _ _ h.le, (H.finalSlab h).flow, (H.finalSlab h).equation,
      (H.finalSlab h).smoothUpTo, ?_, ?_, ?_⟩
    · intro s hs
      exact ⟨hj.trans hs.1, hs.2.le.trans (hlast rfl)⟩
    · intro s hs
      exact ⟨hj.trans_lt hs.1, hs.2.trans_le (hlast rfl)⟩
    · intro s _
      simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_left h]
  | cast i =>
    refine ⟨RealTimeInterval.closedOpen _ _ (H.time_strictMono (Fin.castSucc_lt_succ (i := i))),
      (H.event i).incoming.flow, (H.event i).incoming.equation, (H.event i).incoming.smoothUpTo,
      ?_, ?_, ?_⟩
    · intro s hs
      exact ⟨hj.trans hs.1, hs.2.trans_le (hnext i rfl)⟩
    · intro s hs
      exact ⟨hj.trans_lt hs.1, hs.2.trans_le (hnext i rfl)⟩
    · intro s _
      simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]

/-- 沿 `Q = Q'` 搬运 flow 存在性（右端点版）。 -/
theorem exists_flow_transfer_right_ST {Q Q' : OrientedThreeStage.{u}} (e : Q = Q')
    (J R : Set ℝ) (m : ℝ → Q.Metric) (m' : ℝ → Q'.Metric) (hm : ∀ s ∈ J, HEq (m s) (m' s)) :
    (∃ (D : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := Q'.Carrier) D),
      IsSolutionOn S ∧ Q'.MetricSmoothUpTo S.base.metric D.carrier ∧ J ⊆ D.carrier ∧
        R ⊆ D.regular ∧ ∀ s ∈ J, S.base.metric s = m' s) →
    (∃ (D : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := Q.Carrier) D),
      IsSolutionOn S ∧ Q.MetricSmoothUpTo S.base.metric D.carrier ∧ J ⊆ D.carrier ∧
        R ⊆ D.regular ∧ ∀ s ∈ J, S.base.metric s = m s) := by
  subst e
  rintro ⟨D, S, hS, hsm, hJ, hR, hmeq⟩
  exact ⟨D, S, hS, hsm, hJ, hR, fun s hs => (hmeq s hs).trans (eq_of_heq (hm s hs)).symm⟩

/-- **G7 主定理（flow 版）**：`Ico a b`（`a` 可以是 event 时刻）上 `postStage O a` 的 Ricci flow 解。 -/
theorem exists_stageFlow_right_of_no_event_ST (O : ObservationTower P g) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) :
    ∃ (D : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := (postStage O a).Carrier) D),
      IsSolutionOn S ∧ MetricFamilySmoothOn D S.base.metric ∧
      (postStage O a).MetricSmoothUpTo S.base.metric D.carrier ∧
      Ico a b ⊆ D.carrier ∧ Ioo a b ⊆ D.regular ∧
      (∀ s ∈ Ico a b, S.base.metric s = postMetricAt_ST O a s) ∧
      S.base.metric a = postMetric O a ∧
      (∀ s ∈ Ioo a b, ∀ (x : (postStage O a).Carrier) (A B : TangentSpace ThreeModel x),
        HasDerivAt (fun r : ℝ => (S.base.metric r).inner x A B)
          (-2 * ricciTensor (I := ThreeModel) (S.base.metric s) x A B) s) ∧
      (∀ (x : (postStage O a).Carrier) (A B : TangentSpace ThreeModel x),
        HasDerivWithinAt (fun r : ℝ => (S.base.metric r).inner x A B)
          (-2 * ricciTensor (I := ThreeModel) (S.base.metric a) x A B) (Ici a) a) := by
  have han : a ≤ (⌈b⌉₊ : ℕ) := hab.le.trans (Nat.le_ceil b)
  set j₀ := (O.history ⌈b⌉₊).activeStage (timeIn_ST O ⌈b⌉₊ ha han) with hj₀
  have hpost : postStage O a = (O.history ⌈b⌉₊).stage j₀ :=
    postStage_eq_history_ST O ⌈b⌉₊ ha han
  have hj : (O.history ⌈b⌉₊).time j₀ ≤ a :=
    (O.history ⌈b⌉₊).activeStage_time_le (timeIn_ST O ⌈b⌉₊ ha han)
  have hnext : ∀ i : Fin (O.history ⌈b⌉₊).eventCount, j₀ = i.castSucc →
      b ≤ (O.history ⌈b⌉₊).time i.succ := by
    intro i hi
    by_contra hlt
    rw [not_le] at hlt
    by_cases hle : (O.history ⌈b⌉₊).time i.succ ≤ a
    · have h1 : i.succ ≤ j₀ :=
        (O.history ⌈b⌉₊).le_activeStage (timeIn_ST O ⌈b⌉₊ ha han) i.succ hle
      rw [hi] at h1
      exact absurd h1 (not_le.mpr (Fin.castSucc_lt_succ (i := i)))
    · exact hno _ (Set.mem_iUnion.2 ⟨⌈b⌉₊, i, rfl⟩) ⟨not_le.mp hle, hlt⟩
  have hlast : j₀ = Fin.last (O.history ⌈b⌉₊).eventCount → b ≤ (O.history ⌈b⌉₊).horizon := by
    intro _
    rw [O.horizon_eq]
    exact Nat.le_ceil b
  have hflow := exists_stage_flow_right_ST (O.history ⌈b⌉₊) j₀ hab hj hnext hlast
  obtain ⟨D, S, hS, hsm, hcar, hreg, hmeq⟩ :=
    exists_flow_transfer_right_ST hpost (Ico a b) (Ioo a b) (postMetricAt_ST O a)
      (fun s => (O.history ⌈b⌉₊).stageMetric j₀ s)
      (fun s hs => by
        have hps : postStage O a = postStage O s :=
          postStage_eq_of_no_event_right_ST O ha hno ⟨le_rfl, hab⟩ hs
        have h := postMetric_heq_history_gen_ST O ⌈b⌉₊ (ha.trans hs.1)
          (hs.2.le.trans (Nat.le_ceil b))
        have hact := activeStage_eq_of_no_event_right_ST O ⌈b⌉₊ ha hno ⟨le_rfl, hab⟩ hs hs.1
          ha (ha.trans hs.1) han (hs.2.le.trans (Nat.le_ceil b))
        rw [← hact] at h
        exact (heq_postMetricAt_ST O hps).trans h) hflow
  refine ⟨D, S, hS, hS.smoothMetric, hsm, hcar, hreg, hmeq,
    (hmeq a ⟨le_rfl, hab⟩).trans (postMetricAt_ST_self O a), ?_, ?_⟩
  · intro s hs x A B
    have hd := (hS.equation ⟨s, hreg hs⟩ x A B).hasDerivAt (D.regular_mem_nhds (hreg hs))
    have hric : RicciAtFamily.toTensorField (I := ThreeModel) S.ricciAt s x A B =
        ricciTensor (I := ThreeModel) (S.base.metric s) x A B :=
      DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor (I := ThreeModel) _ x A B
    rw [hric] at hd
    exact hd
  · intro x A B
    exact hasDerivWithinAt_ricci_right_ST S hS hsm hab hcar hreg x A B

/-- 每个时刻 `t₀`（可以是 event 时刻）右边有一个无新事件的区间 `Ioo t₀ b`。 -/
theorem exists_noEvent_right_interval_ST (O : ObservationTower P g) (t₀ : ℝ) :
    ∃ b : ℝ, t₀ < b ∧ ∀ s ∈ O.eventTimes, s ∉ Ioo t₀ b := by
  have hfin : ((O.eventTimes ∩ Icc t₀ (t₀ + 1)) \ {t₀}).Finite :=
    (O.eventTimes_finite_Icc t₀ (t₀ + 1)).subset Set.sdiff_subset
  have ht₀ : t₀ ∈ ((O.eventTimes ∩ Icc t₀ (t₀ + 1)) \ {t₀})ᶜ := fun h => h.2 rfl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hfin.isClosed.isOpen_compl t₀ ht₀
  refine ⟨t₀ + min ε 1, by linarith [lt_min hε one_pos], ?_⟩
  intro s hs hI
  have hd : dist s t₀ < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hI.1, hI.2, min_le_left ε 1]
  exact hball hd ⟨⟨hs, hI.1.le, by linarith [hI.2, min_le_right ε 1]⟩, fun h => hI.1.ne' h⟩

end GC.LongTime

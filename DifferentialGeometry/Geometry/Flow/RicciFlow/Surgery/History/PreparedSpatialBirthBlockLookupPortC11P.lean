import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialQualitySurgery

/-!
# S-CH11-FIX11 port of astra `PreparedSpatialBirthBlockLookup`（`PortC11P`）

来源：donor `PreparedSpatialBirthBlockLookup.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补
（no statement / definition / proof idea altered；不加 `set_option`）：
* `hzero` 里 `rw [S.initial_history]` 之后的 `rfl`：本树 `rw` 已用 `rfl` 关掉目标，多余的收尾
  tactic 报 "No goals to be solved"（FIX6 坑 xiii）→ 删掉；
* `S.quality_state_count …` / `S.quality_state_prefix …` / `S.quality_native_birth_block …`
  点记号：这三个是 `PreparedSpatialQualityTransport` 里 `namespace PreparedSpatialChain` 的
  private 定理，`open private … from` 只开放全名 → `PreparedSpatialChain.quality_… S …`
  （同 `PreparedSpatialQualitySurgery`、FIX9 G5）；
* `hObserved` 里 `simpa only [hindexH] using hLater`：`H.toHistory.event iH` 的类型依赖 `iH`
  （`stage iH.castSucc` 等），simp 进不了 → 一般引理 `hgen : ∀ a b, a = b → (H.toHistory.event a).
  SamePresentation X → (H.toHistory.event b).SamePresentation X`（`subst` 后 `exact id`）；
* 1 处因全名变长的行折行（≤ 100 列）。

原路径 `PreparedSpatialBirthBlockLookup` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.GeneralFlow
universe u

open private PreparedSpatialChain.quality_state_prefix
  PreparedSpatialChain.quality_state_count
  PreparedSpatialChain.quality_native_birth_block from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialQualityTransport
open private event_samePresentation_of_prefix from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepDerivative

private theorem retained_event_samePresentation_of_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : RetainedCoreEvent P Q a s} {E' : RetainedCoreEvent P' Q' a' s'}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (hE : HEq E E') : E.toMetricCutCapEvent.SamePresentation E'.toMetricCutCapEvent := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact MetricCutCapEvent.SamePresentation.refl _

/-- Locate an arbitrary event of the actual observation in its original native
birth block. Later prefixes preserve the event presentation; only the affine
construction supplies equality with the translated native event. -/
theorem PreparedSpatialChain.exists_native_birth_block_of_observation_event
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (hoffset : ∀ k : ℕ, (S.state (k + 1)).offset = (S.state k).history.eventCount)
    {F : GC.Interface.RawSurgery P g} (hTower : F.tower = S.tower)
    (n : ℕ) (j : Fin (F.tower.history n).eventCount) :
    ∃ m : ℕ, m ≤ n ∧
      ∃ i : Fin (S.state (m + 1)).native.eventCount,
        (S.state m).history.eventCount ≤ j.val ∧
        j.val < (S.state (m + 1)).history.eventCount ∧
        j.val = ((S.state (m + 1)).affine.eventIndex i).val ∧
        (F.tower.history n).time j.succ =
          (S.state (m + 1)).native.time i.succ + (S.state (m + 1)).shift ∧
        (F.tower.history n).time j.succ ∈
          Ioc (preparedSpatialHorizon m) ((3 : ℝ) ^ m) ∧
        (F.tower.history n).time j.succ ≤ (n : ℝ) ∧
        ((translate_retained_event ((S.state (m + 1)).native.coreEvent i)
          (S.state (m + 1)).shift).toMetricCutCapEvent).SamePresentation
            ((F.tower.history n).toHistory.event j) := by
  classical
  revert j
  rw [hTower]
  intro j
  let H := (S.state (n + 1)).history
  let a := S.observationTime n
  let count : ℕ → ℕ := fun k => (S.state k).history.eventCount
  have hcut : (S.tower.history n).eventCount ≤ H.eventCount := by
    change (H.toHistory.activeStage a).val ≤ H.eventCount
    exact Nat.le_of_lt_succ (H.toHistory.activeStage a).isLt
  have hjH : j.val < count (n + 1) := lt_of_lt_of_le j.isLt hcut
  have hzero : count 0 = 0 := by
    change (S.state 0).history.eventCount = 0
    rw [S.initial_history]
  have hex : ∃ k : ℕ, j.val < count k := ⟨n + 1, hjH⟩
  cases hfind : Nat.find hex with
  | zero =>
    have hh := Nat.find_spec hex
    rw [hfind, hzero] at hh
    omega
  | succ m =>
    have hmn : m ≤ n := by
      by_contra hnot
      have hh := Nat.find_min hex (show n + 1 < Nat.find hex by rw [hfind]; omega)
      exact hh hjH
    have hprev : count m ≤ j.val :=
      Nat.le_of_not_gt (Nat.find_min hex (show m < Nat.find hex by rw [hfind]; omega))
    have hnext : j.val < count (m + 1) := by
      simpa only [hfind] using Nat.find_spec hex
    let R := S.state (m + 1)
    have hoff : R.offset = count m := hoffset m
    have hcount : R.history.eventCount = count m + R.native.eventCount := by
      have hh := R.affine.count_eq
      change R.history.eventCount = R.offset + R.native.eventCount at hh
      rwa [hoff] at hh
    let i : Fin R.native.eventCount := ⟨j.val - count m, by
      change j.val < R.history.eventCount at hnext
      omega⟩
    have hindex : j.val = (R.affine.eventIndex i).val := by
      change j.val = R.offset + (j.val - count m)
      rw [hoff]
      omega
    let iFull := R.affine.eventIndex i
    have hcountNext : R.history.eventCount ≤ H.eventCount :=
      PreparedSpatialChain.quality_state_count S (Nat.succ_le_succ hmn)
    let iH : Fin H.eventCount := iFull.castLE hcountNext
    let jH : Fin H.eventCount := j.castLE hcut
    have hindexH : iH = jH := Fin.ext hindex.symm
    have hLater := event_samePresentation_of_prefix
      (PreparedSpatialChain.quality_state_prefix S (m + 1) (n + 1) (Nat.succ_le_succ hmn))
      hcountNext iFull
    change (H.toHistory.event iH).SamePresentation (R.history.toHistory.event iFull) at hLater
    have hObserved : ((S.tower.history n).toHistory.event j).SamePresentation
        (R.history.toHistory.event iFull) := by
      change (H.toHistory.event jH).SamePresentation (R.history.toHistory.event iFull)
      have hgen : ∀ a b : Fin H.eventCount, a = b →
          (H.toHistory.event a).SamePresentation (R.history.toHistory.event iFull) →
          (H.toHistory.event b).SamePresentation (R.history.toHistory.event iFull) := by
        intro a b hab
        subst hab
        exact id
      exact hgen iH jH hindexH hLater
    have hAffine : (R.history.toHistory.event iFull).SamePresentation
        ((translate_retained_event (R.native.coreEvent i) R.shift).toMetricCutCapEvent) := by
      apply retained_event_samePresentation_of_heq
      · simpa only [AffineEventPrefix.stageIndex_castSucc] using
          R.affine.stageIndex_stage i.castSucc
      · simpa only [AffineEventPrefix.stageIndex_succ] using
          R.affine.stageIndex_stage i.succ
      · simpa only [AffineEventPrefix.stageIndex_castSucc] using
          R.affine.stageIndex_time i.castSucc
      · simpa only [AffineEventPrefix.stageIndex_succ] using
          R.affine.stageIndex_time i.succ
      · exact R.affine.event_heq i
    have hPresent := (hObserved.trans hAffine).symm
    have htime : (S.tower.history n).time j.succ =
        R.native.time i.succ + R.shift := hPresent.eventTime_eq.symm
    have hblock := PreparedSpatialChain.quality_native_birth_block S hoffset m i
    refine ⟨m, hmn, i, hprev, hnext, hindex, htime, ?_, ?_, hPresent⟩
    · rw [htime]
      exact hblock
    · exact ((S.tower.history n).toHistory.time_le_horizon_at j.succ).trans_eq
        (S.tower.horizon_eq n)

end GC.GeneralFlow

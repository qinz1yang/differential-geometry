import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.RecentCutoffTailC11RC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SurgerySuppliesC11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecentCutoffRadius

set_option autoImplicit false

/-!
# S-CH11-REPROVE-C (G3)：S9 `recent_cutoff_smallness` 的树内重证

目标陈述（`SurgerySuppliesC11S.lean` 冻结，逐字不改）：
`RecentCutoffSupply_C11S records`，即对任意 `ε > 0` 存在 `T`，使 `t ≥ T`、
`(F.tower.history n).time i.succ ∈ [t/2, t]` 时每个 selected nominal 半径
`(records n i).nominalRadius h ≤ ε · q.neckRadius t`。

reference：astra `SH/PreparedSpatialRecentCutoff.lean:167`（`recent_cutoff_decay`）与
`SH/PreparedSpatialSurgeryDecay.lean:128–148`（tuple 最后一个合取项）。astra 把它挂在
`PreparedSpatialChain` 上；那条链的 gating 文件在我们树里永久 reference-only，所以这里按三层
重证，**所有输入都是性质型显式 binder，没有新结构**：

1. `recentCutoffSupply_of_tailBound_C11RC`（F 层）：只要有正数列 `r`，使 `q.neckRadius` 在第 `k` 个
   activation band 内恒等于 `r (k+1)`（`hband`），且 flow 的每个 history `n` 里晚于 `h_k` 的事件有
   `nominalRadius ≤ (1/(k+2))·r (k+1)`（`hrec`），就得 S9。这是 `recent_cutoff_decay` 的算术核。
2. `observationTail_of_fullTail_C11RC`：`hrec` 由 full-state 族上的 `recent_records` +
   prefix 保持（G2 的 `tail_records_bound_C11RC`）与「观察 history 的每个事件由某个 full-state 事件实现」
   的桥 `hbridge` 推出（astra：observation = `restrict` 的 full history，`restrictRecords` 保持
   selected records）。
3. `recentCutoffSupply_of_chain_C11RC`：chain 级总装（`hband` 再由参数侧 `hbefore / hafter / hq`
   经 G2 的 `neckRadius_band_of_compat_C11RC` 推出）。

另有参数级的第二条路线 `recentCutoffSupply_of_accuracy_C11RC`：若 flow 的参数满足
`δ(u)²ρ(u) < ρ(2u)/(u+1)` 且 `ρ` antitone（common-profile 型 δ，见 B3 落地的
`exists_decaying_commonProfile_sq_mul_lt_and_diagonal`），S9 直接由 record 的 `nominal_small` 与
B3 落地的 `nominalRadius_lt_mul_of_accuracy_bound` 推出（`T = 2/ε`），不需要 chain。

留给 outer tuple 的前提（未在树内造出）：`Hs / ps / recs / r` 这条递归链本身、`hrecent`（每一步
新事件的 reserve，即 `PreparedSpatialSuccessor.recent_records`）与 `hbridge`。它们都是 astra
PreparedSpatialPhysicalVolumeEvent 递归构造的直接产出，不是新的几何假设。
-/

noncomputable section

open Set DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

universe u

/-- **F 层 S9**：band 内 `neckRadius = r (k+1)`（`hband`）+ 晚于 `h_k` 的事件有
`nominalRadius ≤ (1/(k+2))·r (k+1)`（`hrec`）⇒ `RecentCutoffSupply_C11S records`。 -/
theorem recentCutoffSupply_of_tailBound_C11RC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : CutoffRecords_C11S F q) (r : ℕ → ℝ) (hr_pos : ∀ k, 0 < r k)
    (hband : ∀ (k : ℕ) (t : ℝ), activation_C11RC k < t → t ≤ activation_C11RC (k + 1) →
      q.neckRadius t = r (k + 1))
    (hrec : ∀ (k n : ℕ) (i : Fin (F.tower.history n).eventCount),
      fullHorizon_C11RC k < (F.tower.history n).time i.succ →
      ∀ h, (records n i).nominalRadius h ≤ (1 / ((k : ℝ) + 2)) * r (k + 1)) :
    RecentCutoffSupply_C11S records := by
  intro η hη
  refine ⟨activation_C11RC (Nat.ceil η⁻¹ + 1), activation_pos_C11RC _, ?_⟩
  intro t ht n i hi h
  obtain ⟨k, hNk, hleft, hright⟩ := exists_activation_band_C11RC (Nat.ceil η⁻¹) t ht
  have hafter : fullHorizon_C11RC k < (F.tower.history n).time i.succ := by
    have hhalf : activation_C11RC k / 2 < t / 2 := by linarith
    exact ((fullHorizon_lt_half_activation_C11RC k).trans hhalf).trans_le hi.1
  calc (records n i).nominalRadius h ≤ (1 / ((k : ℝ) + 2)) * r (k + 1) := hrec k n i hafter h
    _ ≤ η * r (k + 1) :=
        mul_le_mul_of_nonneg_right (cutoffFactor_le_of_ceil_le_C11RC hη hNk) (hr_pos _).le
    _ = η * q.neckRadius t := by rw [hband k t hleft hright]

/-- **观察层 tail**：full-state 族上的 `recent_records` + prefix 保持（G2 `tail_records_bound`），
加上「观察 history `n` 的每个事件由 `Hs (n+1)` 的某个事件实现（同一 presentation、同一 nominal-radius
函数）」的桥，推出 F 层的 `hrec`（对**所有** `n` 成立，不需要 `t ≤ n`）。 -/
theorem observationTail_of_fullTail_C11RC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : CutoffRecords_C11S F q)
    (Hs : ℕ → ObservedHistory.{u}) {ps : ℕ → CutoffParameters}
    (recs : ∀ m (i : Fin (Hs m).eventCount), GeometricCutoffRecord (Hs m) i (ps m))
    (r : ℕ → ℝ) (hr_nonneg : ∀ m, 0 ≤ r m) (hr_anti : Antitone r)
    (hhor : ∀ m, (Hs m).horizon = fullHorizon_C11RC m)
    (hpref : ∀ m, (Hs m).IsPrefixOf (Hs (m + 1)))
    (hpres : ∀ m (i : Fin (Hs m).eventCount),
      HEq (recs (m + 1) (i.castLE (eventCount_le_of_isPrefixOf_C11RC (hpref m)))).nominalRadius
        (recs m i).nominalRadius)
    (hrecent : ∀ k (i : Fin (Hs (k + 1)).eventCount),
      (Hs k).horizon < (Hs (k + 1)).time i.succ →
      ∀ h, (recs (k + 1) i).nominalRadius h ≤ (1 / ((k : ℝ) + 2)) * r (k + 1))
    (hbridge : ∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount),
      ∃ j : Fin (Hs (n + 1)).eventCount,
        ((F.tower.history n).toHistory.event i).SamePresentation ((Hs (n + 1)).event j) ∧
        HEq (records n i).nominalRadius (recs (n + 1) j).nominalRadius)
    (k n : ℕ) (i : Fin (F.tower.history n).eventCount)
    (hafter : fullHorizon_C11RC k < (F.tower.history n).time i.succ) :
    ∀ h, (records n i).nominalRadius h ≤ (1 / ((k : ℝ) + 2)) * r (k + 1) := by
  obtain ⟨j, R, hnom⟩ := hbridge n i
  have htime : (F.tower.history n).time i.succ = (Hs (n + 1)).time j.succ := R.eventTime_eq
  have htn : (F.tower.history n).time i.succ ≤ (n : ℝ) := by
    have h1 := (F.tower.history n).time_strictMono.monotone (Fin.le_last i.succ)
    have h2 := (F.tower.history n).time_le_horizon
    rw [F.tower.horizon_eq n] at h2
    exact h1.trans h2
  have hkn : k ≤ n := by
    have hk1 := nat_le_fullHorizon_add_one_C11RC k
    have hlt : (k : ℝ) < (n : ℝ) + 1 := by linarith
    have : k < n + 1 := by exact_mod_cast hlt
    omega
  have hfull := tail_records_bound_C11RC recs r hr_nonneg hr_anti hpref hpres hrecent k (n + 1)
    (Nat.succ_le_succ hkn) j (by rw [hhor k, ← htime]; exact hafter)
  exact nominal_bound_of_samePresentation_C11RC R _ _ hnom hfull

/-- `restrict` 之后的第 `i` 个事件与原 history 的对应事件是同一个 presentation。 -/
theorem restrict_event_samePresentation_C11RC (K : ObservedHistory.{u})
    (a : Icc (0 : ℝ) K.horizon) (i : Fin (K.restrict a).eventCount) :
    ((K.restrict a).event i).SamePresentation
      (K.event (Fin.castLE (Nat.le_of_lt_succ (K.activeStage a).isLt) i)) :=
  MetricCutCapEvent.SamePresentation.refl _

/-- `hbridge` 的 presentation 分量：观察 history 与 `K.restrict a` 同一 presentation（如
`RetainedCoreObservationTower.successor` / astra `observation` 的定义）时，每个事件都由 `K` 的
某个事件实现。record 分量（`HEq` 的 nominal-radius 函数）才是 `restrictRecords` 保持性的内容。 -/
theorem exists_event_samePresentation_of_restrict_C11RC {H K : ObservedHistory.{u}}
    (a : Icc (0 : ℝ) K.horizon) (hsame : H.SamePresentation (K.restrict a))
    (i : Fin H.eventCount) :
    ∃ j : Fin K.eventCount, (H.event i).SamePresentation (K.event j) :=
  ⟨Fin.castLE (Nat.le_of_lt_succ (K.activeStage a).isLt) (Fin.cast hsame.count_eq i),
    (hsame.event_eq i).trans (restrict_event_samePresentation_C11RC K a _)⟩

/-- **S9（参数级路线）**：`ρ` antitone + common-profile 型的 `δ(u)²ρ(u) < ρ(2u)/(u+1)` ⇒ S9
（B3 落地的 `GeometricCutoffRecord.nominalRadius_lt_mul_of_accuracy_bound`，`T = 2/ε`）。
与 chain 路线互补：这条只要 `q` 满足比较式，不看 history。 -/
theorem recentCutoffSupply_of_accuracy_C11RC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : CutoffRecords_C11S F q) (hranti : AntitoneOn q.neckRadius (Ici 0))
    (haccuracy : ∀ u : ℝ, 0 ≤ u →
      q.delta u ^ 2 * q.neckRadius u < q.neckRadius (2 * u) / (u + 1)) :
    RecentCutoffSupply_C11S records := fun ε hε =>
  ⟨2 / ε, by positivity, fun _ ht n i hi h =>
    ((records n i).nominalRadius_lt_mul_of_accuracy_bound hranti haccuracy hε ht hi.1 h).le⟩

/-- **S9（chain 级重证）**：full-state 链 `(Hs, ps, recs, r)` 满足
相邻 prefix（`hpref`）、旧 record 的 nominal 半径被保持（`hpres`）、每步新事件的 reserve
`≤ (1/(k+2))·r (k+1)`（`hrecent`，astra `recent_records`）、`r` 递减（`hr_succ`，`radius_le`）、
参数在 activation 之前不变 / 之后取新 radius（`hbefore / hafter`），且 flow 的 `q` 与
`ps (n+1)` 在 `[0, n]` 上相容（`hq`，astra tuple 的 `hpref` 条款）、观察 record 由 full-state
record 实现（`hbridge`）⇒ `RecentCutoffSupply_C11S records`。 -/
theorem recentCutoffSupply_of_chain_C11RC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : CutoffRecords_C11S F q)
    (Hs : ℕ → ObservedHistory.{u}) (ps : ℕ → CutoffParameters)
    (recs : ∀ m (i : Fin (Hs m).eventCount), GeometricCutoffRecord (Hs m) i (ps m))
    (r : ℕ → ℝ) (hr_pos : ∀ k, 0 < r k) (hr_succ : ∀ m, r (m + 1) ≤ r m)
    (hhor : ∀ m, (Hs m).horizon = fullHorizon_C11RC m)
    (hpref : ∀ m, (Hs m).IsPrefixOf (Hs (m + 1)))
    (hpres : ∀ m (i : Fin (Hs m).eventCount),
      HEq (recs (m + 1) (i.castLE (eventCount_le_of_isPrefixOf_C11RC (hpref m)))).nominalRadius
        (recs m i).nominalRadius)
    (hrecent : ∀ k (i : Fin (Hs (k + 1)).eventCount),
      (Hs k).horizon < (Hs (k + 1)).time i.succ →
      ∀ h, (recs (k + 1) i).nominalRadius h ≤ (1 / ((k : ℝ) + 2)) * r (k + 1))
    (hbefore : ∀ m t, t ≤ activation_C11RC m →
      (ps (m + 1)).neckRadius t = (ps m).neckRadius t)
    (hafter : ∀ m t, activation_C11RC m < t → (ps (m + 1)).neckRadius t = r (m + 1))
    (hq : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ), q.neckRadius t = (ps (n + 1)).neckRadius t)
    (hbridge : ∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount),
      ∃ j : Fin (Hs (n + 1)).eventCount,
        ((F.tower.history n).toHistory.event i).SamePresentation ((Hs (n + 1)).event j) ∧
        HEq (records n i).nominalRadius (recs (n + 1) j).nominalRadius) :
    RecentCutoffSupply_C11S records :=
  recentCutoffSupply_of_tailBound_C11RC records r hr_pos
    (fun k _ hl hr => neckRadius_band_of_compat_C11RC q ps r hbefore hafter hq k hl hr)
    (fun k n i hk => observationTail_of_fullTail_C11RC records Hs recs r
      (fun m => (hr_pos m).le) (antitone_nat_of_succ_le hr_succ) hhor hpref hpres hrecent
      hbridge k n i hk)

end GC.LongTime.Ch11

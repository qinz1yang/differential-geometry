import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.RecentCutoffArithC11RC
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction

set_option autoImplicit false

/-!
# S-CH11-REPROVE-C (G2)：S9 的 prefix 传递与 tail induction

reference：astra `SH/PreparedSpatialRecentCutoff.lean:49–95`（`nominal_bound_of_samePresentation`、
`record_bound_of_prefix`）、`:104–128`（`tail_records_bound`、`radius_eq_on_activation_band`）与
`SH/PreparedSpatialSurgeryDecay.lean:17–40`（`event_samePresentation_of_prefix`）。astra 的版本
都挂在 `PreparedSpatialChain S` 上（gating 文件永久 reference-only）；这里改成**对任意 full-state
族**的显式 binder 引理：

* `Hs : ℕ → ObservedHistory`（full histories）、`ps : ℕ → CutoffParameters`、
  `recs m i : GeometricCutoffRecord (Hs m) i (ps m)`；
* `hpref`（相邻 full history 互为 prefix）、`hpres`（旧事件的 selected nominal-radius 函数被
  保留，只用 `nominalRadius` 一个分量）、`hrecent`（第 `k+1` 个 state 上晚于 `Hs k` horizon 的新
  事件有 `nominalRadius ≤ (1/(k+2))·r (k+1)`，即 astra `PreparedSpatialSuccessor.recent_records`）、
  `r` 的单调性（`radius_le`）——都是性质，不是新结构。

结论 `tail_records_bound_C11RC`：对所有 `m ≥ k+1`，`Hs m` 里晚于 `Hs k` horizon 的事件仍有同一
上界 `(1/(k+2))·r (k+1)`。`neckRadius_band_C11RC` 是参数侧的对偶：activation band 内后继参数的
`neckRadius` 都等于 `r (k+1)`。
-/

noncomputable section

open Set DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

universe u

/-- presentation 先确定真正的 nonempty-tubes witness 的定义域，再用 nominal-radius 函数的 `HEq`。 -/
theorem nominal_bound_of_samePresentation_C11RC
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' bound : ℝ}
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (R : E.SamePresentation F)
    (f : Nonempty E.transition.trace.tubes.Index → ℝ)
    (f' : Nonempty F.transition.trace.tubes.Index → ℝ)
    (hf : HEq f f') (hbound : ∀ h, f' h ≤ bound) :
    ∀ h, f h ≤ bound := by
  cases R.incomingStage_eq
  cases R.outgoingStage_eq
  cases R.leftTime_eq
  cases R.eventTime_eq
  cases E
  cases F
  cases R.discarded_eq
  cases R.capped_eq
  cases eq_of_heq R.transition_heq
  cases eq_of_heq hf
  exact hbound

/-- prefix 关系保持事件数。 -/
theorem eventCount_le_of_isPrefixOf_C11RC {H J : ObservedHistory.{u}}
    (hp : H.IsPrefixOf J) : H.eventCount ≤ J.eventCount := by
  rw [← hp.presentation.count_eq]
  exact Nat.le_of_lt_succ (J.activeStage _).isLt

/-- prefix 按真实 index 与 presentation 识别被保留的事件。 -/
theorem event_samePresentation_of_prefix_C11RC
    {H J : ObservedHistory.{u}} (hp : H.IsPrefixOf J)
    (hn : H.eventCount ≤ J.eventCount) (i : Fin H.eventCount) :
    (J.event (i.castLE hn)).SamePresentation (H.event i) := by
  let a : Icc (0 : ℝ) J.horizon := ⟨H.horizon, H.horizon_nonneg, hp.horizon_le⟩
  let iR : Fin (J.restrict a).eventCount := Fin.cast hp.presentation.count_eq.symm i
  have hi : Fin.cast hp.presentation.count_eq iR = i := Fin.ext rfl
  have hE := hp.presentation.event_eq iR
  change (J.event (i.castLE hn)).SamePresentation
    (H.event (Fin.cast hp.presentation.count_eq iR)) at hE
  have key : ∀ j : Fin H.eventCount, j = i →
      (J.event (i.castLE hn)).SamePresentation (H.event j) →
      (J.event (i.castLE hn)).SamePresentation (H.event i) := by
    intro j hj h
    subst hj
    exact h
  exact key _ hi hE

/-- 在旧 horizon 之前到达的事件就是真实的旧事件，带有同一个 selected nominal-radius 函数。 -/
theorem record_bound_of_prefix_C11RC
    {H J : ObservedHistory.{u}} {pH pJ : CutoffParameters}
    (old : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i pH)
    (records : ∀ i : Fin J.eventCount, GeometricCutoffRecord J i pJ)
    (hp : H.IsPrefixOf J) (hn : H.eventCount ≤ J.eventCount)
    (hrecords : ∀ i : Fin H.eventCount,
      HEq (records (i.castLE hn)).nominalRadius (old i).nominalRadius)
    {cut bound : ℝ}
    (hbound : ∀ i : Fin H.eventCount, cut < H.time i.succ →
      ∀ h, (old i).nominalRadius h ≤ bound)
    (i : Fin J.eventCount) (hpast : J.time i.succ ≤ H.horizon)
    (hafter : cut < J.time i.succ) :
    ∀ h, (records i).nominalRadius h ≤ bound := by
  let a : Icc (0 : ℝ) J.horizon := ⟨H.horizon, H.horizon_nonneg, hp.horizon_le⟩
  have hi : i.val < (J.restrict a).eventCount :=
    (J.event_reached_iff a i).mp hpast
  let iR : Fin (J.restrict a).eventCount := ⟨i.val, hi⟩
  let j : Fin H.eventCount := Fin.cast hp.presentation.count_eq iR
  have hj : j.castLE hn = i := Fin.ext rfl
  have hE : (J.event i).SamePresentation (H.event j) :=
    hp.presentation.event_eq iR
  have hnom : HEq (records i).nominalRadius (old j).nominalRadius := by
    have key : ∀ i' : Fin J.eventCount, i' = j.castLE hn →
        HEq (records i').nominalRadius (old j).nominalRadius := by
      intro i' h
      subst h
      exact hrecords j
    exact key i hj.symm
  exact nominal_bound_of_samePresentation_C11RC hE _ _ hnom
    (hbound j (by rw [← hE.eventTime_eq]; exact hafter))

/-- **tail induction**：第 `k+1` 个 state 上晚于 `Hs k` horizon 的新事件带着上界
`(1/(k+2))·r (k+1)`；之后每个 state `m ≥ k+1` 里同一批物理事件、同一个 nominal-radius 函数仍
满足它（旧事件靠 prefix 传递，新事件靠更小的 reserve 与 `r` 的单调性）。 -/
theorem tail_records_bound_C11RC
    {Hs : ℕ → ObservedHistory.{u}} {ps : ℕ → CutoffParameters}
    (recs : ∀ m (i : Fin (Hs m).eventCount), GeometricCutoffRecord (Hs m) i (ps m))
    (r : ℕ → ℝ) (hr_nonneg : ∀ m, 0 ≤ r m) (hr_anti : Antitone r)
    (hpref : ∀ m, (Hs m).IsPrefixOf (Hs (m + 1)))
    (hpres : ∀ m (i : Fin (Hs m).eventCount),
      HEq (recs (m + 1) (i.castLE (eventCount_le_of_isPrefixOf_C11RC (hpref m)))).nominalRadius
        (recs m i).nominalRadius)
    (hrecent : ∀ k (i : Fin (Hs (k + 1)).eventCount),
      (Hs k).horizon < (Hs (k + 1)).time i.succ →
      ∀ h, (recs (k + 1) i).nominalRadius h ≤ (1 / ((k : ℝ) + 2)) * r (k + 1))
    (k m : ℕ) (hkm : k + 1 ≤ m) :
    ∀ i : Fin (Hs m).eventCount, (Hs k).horizon < (Hs m).time i.succ →
      ∀ h, (recs m i).nominalRadius h ≤ (1 / ((k : ℝ) + 2)) * r (k + 1) := by
  induction m, hkm using Nat.le_induction with
  | base => exact hrecent k
  | succ m hkm ih =>
    intro i hafter
    by_cases hpast : (Hs (m + 1)).time i.succ ≤ (Hs m).horizon
    · exact record_bound_of_prefix_C11RC (recs m) (recs (m + 1)) (hpref m)
        (eventCount_le_of_isPrefixOf_C11RC (hpref m)) (hpres m) ih i hpast hafter
    · intro h
      have hnew := hrecent m i (lt_of_not_ge hpast) h
      have hkm' : k ≤ m := (Nat.le_succ k).trans hkm
      exact hnew.trans (mul_le_mul (cutoffFactor_antitone_C11RC hkm')
        (hr_anti (Nat.succ_le_succ hkm')) (hr_nonneg _) (by positivity))

/-- 参数侧：后继参数在 activation 之前保持旧 `neckRadius`、之后取新 radius，所以第 `k` 个 band
`(activation k, activation (k+1)]` 内，所有 `m ≥ k+1` 的 `neckRadius` 都等于 `r (k+1)`。 -/
theorem neckRadius_band_C11RC (ps : ℕ → CutoffParameters) (r : ℕ → ℝ)
    (hbefore : ∀ m t, t ≤ activation_C11RC m →
      (ps (m + 1)).neckRadius t = (ps m).neckRadius t)
    (hafter : ∀ m t, activation_C11RC m < t → (ps (m + 1)).neckRadius t = r (m + 1))
    (k m : ℕ) (hkm : k + 1 ≤ m) {t : ℝ}
    (hleft : activation_C11RC k < t) (hright : t ≤ activation_C11RC (k + 1)) :
    (ps m).neckRadius t = r (k + 1) := by
  induction m, hkm using Nat.le_induction with
  | base => exact hafter k t hleft
  | succ m hkm ih =>
    exact (hbefore m t (hright.trans (activation_strictMono_C11RC.monotone hkm))).trans ih

/-- 对角参数 `q`（在 `[0, n]` 上与 `ps (n+1)` 相容，astra tuple 的 `hpref` 条款）在 band 内取
`r (k+1)`。 -/
theorem neckRadius_band_of_compat_C11RC (q : CutoffParameters) (ps : ℕ → CutoffParameters)
    (r : ℕ → ℝ)
    (hbefore : ∀ m t, t ≤ activation_C11RC m →
      (ps (m + 1)).neckRadius t = (ps m).neckRadius t)
    (hafter : ∀ m t, activation_C11RC m < t → (ps (m + 1)).neckRadius t = r (m + 1))
    (hq : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ), q.neckRadius t = (ps (n + 1)).neckRadius t)
    (k : ℕ) {t : ℝ} (hleft : activation_C11RC k < t) (hright : t ≤ activation_C11RC (k + 1)) :
    q.neckRadius t = r (k + 1) := by
  have hkt : (k : ℝ) < t := (nat_le_activation_C11RC k).trans_lt hleft
  have hkceil : k ≤ Nat.ceil t := by exact_mod_cast hkt.le.trans (Nat.le_ceil t)
  have ht0 : 0 ≤ t := (activation_pos_C11RC k).le.trans hleft.le
  rw [hq (Nat.ceil t) t ⟨ht0, Nat.le_ceil t⟩]
  exact neckRadius_band_C11RC ps r hbefore hafter k (Nat.ceil t + 1)
    (Nat.succ_le_succ hkceil) hleft hright

end GC.LongTime.Ch11

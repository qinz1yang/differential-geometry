import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialSurgery
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDecay
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialRecentCutoff

/-!
S-CH11-FIX6 port（astra `History/PreparedSpatialSurgeryDecay` 的 elaboration 修补；
陈述 / 定义 / 证明思路逐字不变）：
(a) `event_samePresentation_of_prefix` 的 `simpa only [hi] using hE`（simp 进不了
    `SamePresentation` 的依赖类型位）→ `rw [hi] at hE; exact hE`；
(b) `exists_surgery_with_spatial_control_and_decay` 里 `hi'` 的 `rw [hE.eventTime_eq]`
    （目标写 `(S.tower.history m).time …`，`eventTime_eq` 的左端是 `.toHistory.time …`，
    syntactic 不匹配）→ 先 `have ht := hE.eventTime_eq`，`change` 到 `.toHistory.time` 形再 `rw`。
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped ENNReal

namespace GC.GeneralFlow.PreparedSpatialChain
universe u

/-- The presentation identifies the actual nonempty-tubes witness domain before
using the heterogeneous equality of the selected nominal-radius functions. -/
private theorem nominal_bound_of_samePresentation
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

/-- The prefix identifies a retained event by its actual index and presentation. -/
private theorem event_samePresentation_of_prefix
    {H J : ObservedHistory.{u}} (hp : H.IsPrefixOf J)
    (hn : H.eventCount ≤ J.eventCount) (i : Fin H.eventCount) :
    (J.event (i.castLE hn)).SamePresentation (H.event i) := by
  let a : Icc (0 : ℝ) J.horizon := ⟨H.horizon, H.horizon_nonneg, hp.horizon_le⟩
  let iR : Fin (J.restrict a).eventCount := Fin.cast hp.presentation.count_eq.symm i
  have hi : Fin.cast hp.presentation.count_eq iR = i := Fin.ext rfl
  have hE := hp.presentation.event_eq iR
  change (J.event (i.castLE hn)).SamePresentation
    (H.event (Fin.cast hp.presentation.count_eq iR)) at hE
  rw [hi] at hE
  exact hE

/-- The one surgery and record family selected from the given chain has both
accuracy decay and physical recent-cutoff decay at every observation index. All
spatial, parameter, marking and selected-record conclusions are retained. -/
theorem exists_surgery_with_spatial_control_and_decay
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : ∀ n, ∀ i : Fin (F.tower.history n).eventCount,
        GeometricCutoffRecord (F.tower.history n).toHistory i q),
      F.tower = S.tower ∧
      (q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
        q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy ∧
        q.recenterConstant = pBase.recenterConstant) ∧
      (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      (∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
        q.delta t = (S.observation n).parameters.delta t ∧
        q.neckRadius t = (S.observation n).parameters.neckRadius t ∧
        q.protectedRadius t = (S.observation n).parameters.protectedRadius t) ∧
      (∀ (n : ℕ) (i : Fin (F.tower.history n).eventCount)
        (j : Fin (S.observation n).history.eventCount), i.val = j.val →
        HEq (records n i).nominalRadius ((S.observation n).records j).nominalRadius ∧
        HEq (records n i).delta ((S.observation n).records j).delta ∧
        HEq (records n i).order ((S.observation n).records j).order ∧
        HEq (records n i).neck ((S.observation n).records j).neck ∧
        HEq (records n i).static ((S.observation n).records j).static) ∧
      (∀ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
        (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
        (q.neckRadius t ^ 2)⁻¹ < metricScalarAt
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage t) t)
          C.epsilon (max C.C1s C.Cbirth) (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) x,
          W.capTubeHasNeckChart C.epsilon) ∧
      (∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) C.epsilon t) ∧
      (∃ hc : Monotone (fun n => (F.tower.history n).eventCount),
        ∀ (m n : ℕ) (hmn : m ≤ n),
          (F.tower.initial m).IsPrefixOf (F.tower.initial n) ∧
          ∀ i : Fin (F.tower.history m).eventCount,
            HEq (records n (i.castLE (hc hmn))).nominalRadius (records m i).nominalRadius ∧
            HEq (records n (i.castLE (hc hmn))).delta (records m i).delta ∧
            HEq (records n (i.castLE (hc hmn))).order (records m i).order ∧
            HEq (records n (i.castLE (hc hmn))).neck (records m i).neck ∧
            HEq (records n (i.castLE (hc hmn))).static (records m i).static) ∧
      Filter.Tendsto q.delta Filter.atTop (nhds (0 : ℝ)) ∧
      ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
        ∀ t : ℝ, T ≤ t → ∀ n : ℕ,
        ∀ i : Fin (F.tower.history n).eventCount,
          (F.tower.history n).time i.succ ∈ Icc (t / 2) t →
          ∀ h, (records n i).nominalRadius h ≤ η * q.neckRadius t := by
  obtain ⟨F, q, κ, records, hTower, hstatic, hκ, hκanti, hδanti, hranti,
    hpref, hbridge, hcanonical, hwin, hnc, hc, hOld⟩ :=
    S.exists_surgery_with_spatial_control
  rcases F with ⟨K, hcontrol⟩
  change K = S.tower at hTower
  subst K
  let D := CutoffParameters.diagonal (fun n => (S.observation n).parameters)
  have hdiag (t : ℝ) (ht : 0 ≤ t) :
      q.delta t = D.delta t ∧ q.neckRadius t = D.neckRadius t := by
    have hp := hpref (Nat.ceil t) t ⟨ht, Nat.le_ceil t⟩
    exact ⟨hp.1, hp.2.1⟩
  have hdelta : Filter.Tendsto q.delta Filter.atTop (nhds (0 : ℝ)) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 (S.diagonal_delta_tendsto) ε hε
    refine ⟨max M 0, ?_⟩
    intro t ht
    rw [(hdiag t ((le_max_right M 0).trans ht)).1]
    exact hM t ((le_max_left M 0).trans ht)
  refine ⟨⟨S.tower, hcontrol⟩, q, κ, records, rfl, hstatic, hκ, hκanti,
    hδanti, hranti, hpref, hbridge, hcanonical, hwin, hnc, ⟨hc, hOld⟩, hdelta, ?_⟩
  intro η hη
  obtain ⟨T, hT, hrecent⟩ := S.recent_cutoff_decay η hη
  have hlocal : ∀ t : ℝ, T ≤ t → ∀ n : ℕ, t ≤ (n : ℝ) →
      ∀ i : Fin (S.tower.history n).eventCount,
        (S.tower.history n).time i.succ ∈ Icc (t / 2) t →
        ∀ h, (records n i).nominalRadius h ≤ η * q.neckRadius t := by
    intro t htt n htn i hi h
    have hrecord : (records n i).nominalRadius =
        ((S.observation n).records i).nominalRadius :=
      eq_of_heq ((hbridge n i i rfl).1)
    rw [hrecord, (hdiag t (hT.le.trans htt)).2]
    exact hrecent t htt n htn i hi h
  refine ⟨T, hT, ?_⟩
  intro t htt n i hi
  let m : ℕ := max n (Nat.ceil t)
  have hnm : n ≤ m := le_max_left _ _
  have htm : t ≤ (m : ℝ) :=
    (Nat.le_ceil t).trans (Nat.cast_le.mpr (le_max_right n (Nat.ceil t)))
  have hp : (S.tower.history n).toHistory.IsPrefixOf (S.tower.history m).toHistory :=
    (hOld n m hnm).1.1
  have hE := event_samePresentation_of_prefix hp (hc hnm) i
  have hi' : (S.tower.history m).time (i.castLE (hc hnm)).succ ∈ Icc (t / 2) t := by
    have ht : (S.tower.history m).toHistory.time (i.castLE (hc hnm)).succ =
        (S.tower.history n).toHistory.time i.succ := hE.eventTime_eq
    change (S.tower.history m).toHistory.time (i.castLE (hc hnm)).succ ∈ Icc (t / 2) t
    rw [ht]
    exact hi
  exact nominal_bound_of_samePresentation hE.symm _ _
    ((hOld n m hnm).2 i).1.symm
    (hlocal t htt m htm (i.castLE (hc hnm)) hi')

end GC.GeneralFlow.PreparedSpatialChain

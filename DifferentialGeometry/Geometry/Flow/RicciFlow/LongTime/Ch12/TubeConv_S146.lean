import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TubeThread_S137
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HBirthPt_S146

/-!
# CH12-S146, group 2b: the S137 TUBE (tower stage metrics) read on the prefix history

`tube_stage_S146` evaluates the tube at a time `t` with active stage `towerIdx m`; `tube_slab_S146` (incoming slab of an
event, `t ∈ [time i.castSucc, time i.succ)`), `tube_out_S146` (initial metric of stage `i.succ`) and `tube_final_S146`
(the closed final slab `sliceSlabR_O3`) are its three readings.  The TUBE text is `[FROZEN] CH12-S137 tube` with `R`, `Bd` free.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

theorem tube_stage_S146 (s : RegularSlice F.observation) {j : Fin (sliceHistoryR_O3 F s).eventCount}
    {q : ((sliceHistoryR_O3 F s).toHistory.stage (Fin.last (sliceHistoryR_O3 F s).eventCount)).Carrier}
    (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
      (Fin.last (sliceHistoryR_O3 F s).eventCount) (Fin.le_last _) q) {R Bd : ℝ}
    (htube : ∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
      (hav : towerIdx_S137 s j.succ ≤ (sliceTowerHistory_CX2 s).activeStage v)
      (hvt : (sliceTowerHistory_CX2 s).activeStage v ≤
        towerIdx_S137 s (Fin.last (sliceHistoryR_O3 F s).eventCount)),
      v.val ≤ s.time →
      ∀ q ∈ riemannianBallOf
        ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v)
        ((towerTrace_S137 s B).point ((sliceTowerHistory_CX2 s).activeStage v) hav hvt) R,
      Real.sqrt (normSq0S
        ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q 4
        (metricRm04At
          ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q)) ≤ Bd)
    (t : ℝ) (m : Fin ((sliceHistoryR_O3 F s).eventCount + 1)) (hm : j.succ ≤ m)
    (ht1 : (sliceTowerHistory_CX2 s).time (towerIdx_S137 s m) ≤ t) (ht2 : t ≤ s.time)
    (hmax : ∀ k : Fin ((sliceTowerHistory_CX2 s).eventCount + 1),
      (sliceTowerHistory_CX2 s).time k ≤ t → k ≤ towerIdx_S137 s m) :
    ∀ x ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric (towerIdx_S137 s m) t)
        (B.point m hm (Fin.le_last _)) R,
      Real.sqrt (normSq0S ((sliceTowerHistory_CX2 s).stageMetric (towerIdx_S137 s m) t) x 4
        (metricRm04At ((sliceTowerHistory_CX2 s).stageMetric (towerIdx_S137 s m) t) x)) ≤ Bd := by
  have h0 : 0 ≤ t := ((sliceTowerHistory_CX2 s).time_nonneg _).trans ht1
  have hh : t ≤ (sliceTowerHistory_CX2 s).horizon := ht2.trans (sliceTowerTime_CX2 s).2.2
  let v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon := ⟨t, h0, hh⟩
  have hv : (sliceTowerHistory_CX2 s).activeStage v = towerIdx_S137 s m :=
    ObservedHistory.activeStage_eq_of_maximal _ v _ ht1 hmax
  have key : ∀ (m' : Fin ((sliceTowerHistory_CX2 s).eventCount + 1))
      (hv' : (sliceTowerHistory_CX2 s).activeStage v = m')
      (hav' : towerIdx_S137 s j.succ ≤ m') (hvt' : m' ≤ towerIdx_S137 s (Fin.last (sliceHistoryR_O3 F s).eventCount)),
      ∀ x ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric m' t) ((towerTrace_S137 s B).point m' hav' hvt') R,
      Real.sqrt (normSq0S ((sliceTowerHistory_CX2 s).stageMetric m' t) x 4
        (metricRm04At ((sliceTowerHistory_CX2 s).stageMetric m' t) x)) ≤ Bd := by
    intro m' hv'
    subst hv'
    intro hav' hvt'
    exact htube v hav' hvt' ht2
  exact key (towerIdx_S137 s m) hv (towerIdx_mono_S137 s hm) (towerIdx_mono_S137 s (Fin.le_last _))

private theorem sm_aux_S146 (Ht : ObservedHistory.{u}) (m : Fin (Ht.eventCount + 1)) (i' : Fin Ht.eventCount)
    (hm : m = i'.castSucc) (t R Bd : ℝ) (u : (Ht.stage m).Carrier)
    (h : ∀ x ∈ riemannianBallOf (Ht.stageMetric m t) u R,
      Real.sqrt (normSq0S (Ht.stageMetric m t) x 4 (metricRm04At (Ht.stageMetric m t) x)) ≤ Bd) :
    ∀ x ∈ riemannianBallOf ((Ht.event i').incoming.flow.base.metric t) (hm ▸ u) R,
      Real.sqrt (normSq0S ((Ht.event i').incoming.flow.base.metric t) x 4
        ((Ht.event i').incoming.flow.base.rm04 t x)) ≤ Bd := by
  subst hm
  have e : Ht.stageMetric i'.castSucc t = (Ht.event i').incoming.flow.base.metric t := by
    simp [ObservedHistory.stageMetric]
  rw [e] at h
  intro x hx
  have := h x hx
  rwa [SolutionFamily.rm04, metricRm04_apply]

theorem tube_slab_S146 (s : RegularSlice F.observation) {j : Fin (sliceHistoryR_O3 F s).eventCount}
    {q : ((sliceHistoryR_O3 F s).toHistory.stage (Fin.last (sliceHistoryR_O3 F s).eventCount)).Carrier}
    (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
      (Fin.last (sliceHistoryR_O3 F s).eventCount) (Fin.le_last _) q) {R Bd : ℝ}
    (htube : ∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
      (hav : towerIdx_S137 s j.succ ≤ (sliceTowerHistory_CX2 s).activeStage v)
      (hvt : (sliceTowerHistory_CX2 s).activeStage v ≤
        towerIdx_S137 s (Fin.last (sliceHistoryR_O3 F s).eventCount)),
      v.val ≤ s.time →
      ∀ q ∈ riemannianBallOf
        ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v)
        ((towerTrace_S137 s B).point ((sliceTowerHistory_CX2 s).activeStage v) hav hvt) R,
      Real.sqrt (normSq0S
        ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q 4
        (metricRm04At
          ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q)) ≤ Bd) :
    ∀ (i : Fin (sliceHistoryR_O3 F s).eventCount) (hi : j.succ ≤ i.castSucc),
      ∀ t ∈ Ico ((sliceHistoryR_O3 F s).time i.castSucc) ((sliceHistoryR_O3 F s).time i.succ),
      ∀ x ∈ riemannianBallOf (((sliceHistoryR_O3 F s).toHistory.event i).incoming.flow.base.metric t)
        (B.point i.castSucc hi (i.castSucc_lt_succ.le.trans (Fin.le_last _))) R,
        Real.sqrt (normSq0S (((sliceHistoryR_O3 F s).toHistory.event i).incoming.flow.base.metric t) x 4
          (((sliceHistoryR_O3 F s).toHistory.event i).incoming.flow.base.rm04 t x)) ≤ Bd := by
  intro i hi t ht
  have hts : (sliceHistoryR_O3 F s).time i.succ ≤ s.time :=
    ((sliceHistoryR_O3 F s).time_strictMono.monotone (Fin.le_last _)).trans
      (sliceSlabR_O3 F s).lt.le
  have hmax : ∀ k : Fin ((sliceTowerHistory_CX2 s).eventCount + 1),
      (sliceTowerHistory_CX2 s).time k ≤ t → k ≤ towerIdx_S137 s i.castSucc := by
    intro k hk
    by_contra hlt
    have h1 : towerIdx_S137 s i.succ ≤ k := by
      have := not_le.mp hlt
      rw [Fin.lt_def] at this
      rw [Fin.le_def]
      have e1 : (towerIdx_S137 s i.castSucc).val = i.val := rfl
      have e2 : (towerIdx_S137 s i.succ).val = i.val + 1 := rfl
      omega
    have h2 := (sliceTowerHistory_CX2 s).time_strictMono.monotone h1
    exact absurd (lt_of_lt_of_le ht.2 h2) (not_lt.mpr hk)
  have key := tube_stage_S146 s B htube t i.castSucc hi ht.1 (ht.2.le.trans hts) hmax
  exact sm_aux_S146 (sliceTowerHistory_CX2 s) (towerIdx_S137 s i.castSucc)
    (Fin.castLE (Nat.le_of_lt_succ (sliceStageR_O3 F s).isLt) i) (Fin.ext rfl) t R Bd _ key

theorem tube_out_S146 (s : RegularSlice F.observation) {j : Fin (sliceHistoryR_O3 F s).eventCount}
    {q : ((sliceHistoryR_O3 F s).toHistory.stage (Fin.last (sliceHistoryR_O3 F s).eventCount)).Carrier}
    (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
      (Fin.last (sliceHistoryR_O3 F s).eventCount) (Fin.le_last _) q) {R Bd : ℝ}
    (htube : ∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
      (hav : towerIdx_S137 s j.succ ≤ (sliceTowerHistory_CX2 s).activeStage v)
      (hvt : (sliceTowerHistory_CX2 s).activeStage v ≤
        towerIdx_S137 s (Fin.last (sliceHistoryR_O3 F s).eventCount)),
      v.val ≤ s.time →
      ∀ q ∈ riemannianBallOf
        ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v)
        ((towerTrace_S137 s B).point ((sliceTowerHistory_CX2 s).activeStage v) hav hvt) R,
      Real.sqrt (normSq0S
        ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q 4
        (metricRm04At
          ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q)) ≤ Bd) :
    ∀ (i : Fin (sliceHistoryR_O3 F s).eventCount) (hi : j.succ ≤ i.castSucc),
      ∀ y ∈ riemannianBallOf ((sliceHistoryR_O3 F s).initialMetric i.succ)
        (B.point i.succ (hi.trans i.castSucc_lt_succ.le) (Fin.le_last _)) R,
        Real.sqrt (normSq0S ((sliceHistoryR_O3 F s).initialMetric i.succ) y 4
          (metricRm04At ((sliceHistoryR_O3 F s).initialMetric i.succ) y)) ≤ Bd := by
  intro i hi
  have hts : (sliceHistoryR_O3 F s).time i.succ ≤ s.time :=
    ((sliceHistoryR_O3 F s).time_strictMono.monotone (Fin.le_last _)).trans
      (sliceSlabR_O3 F s).lt.le
  have key := tube_stage_S146 s B htube ((sliceHistoryR_O3 F s).time i.succ) i.succ
    (hi.trans i.castSucc_lt_succ.le) le_rfl hts
    (fun k hk => ((sliceTowerHistory_CX2 s).time_strictMono.le_iff_le).mp hk)
  have e : (sliceTowerHistory_CX2 s).stageMetric (towerIdx_S137 s i.succ)
      ((sliceHistoryR_O3 F s).time i.succ) =
      (sliceTowerHistory_CX2 s).initialMetric (towerIdx_S137 s i.succ) :=
    ObservedHistory.stageMetric_initial _ _
  rw [e] at key
  exact key

theorem tube_final_S146 (s : RegularSlice F.observation) {j : Fin (sliceHistoryR_O3 F s).eventCount}
    {q : ((sliceHistoryR_O3 F s).toHistory.stage (Fin.last (sliceHistoryR_O3 F s).eventCount)).Carrier}
    (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
      (Fin.last (sliceHistoryR_O3 F s).eventCount) (Fin.le_last _) q) {R Bd : ℝ}
    (htube : ∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
      (hav : towerIdx_S137 s j.succ ≤ (sliceTowerHistory_CX2 s).activeStage v)
      (hvt : (sliceTowerHistory_CX2 s).activeStage v ≤
        towerIdx_S137 s (Fin.last (sliceHistoryR_O3 F s).eventCount)),
      v.val ≤ s.time →
      ∀ q ∈ riemannianBallOf
        ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v)
        ((towerTrace_S137 s B).point ((sliceTowerHistory_CX2 s).activeStage v) hav hvt) R,
      Real.sqrt (normSq0S
        ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q 4
        (metricRm04At
          ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q)) ≤ Bd) :
    ∀ t ∈ Icc ((sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount)) s.time,
      ∀ x ∈ riemannianBallOf ((sliceSlabR_O3 F s).flow.base.metric t) q R,
        Real.sqrt (normSq0S ((sliceSlabR_O3 F s).flow.base.metric t) x 4
          ((sliceSlabR_O3 F s).flow.base.rm04 t x)) ≤ Bd := by
  intro t ht
  have hs1 : towerIdx_S137 s (Fin.last (sliceHistoryR_O3 F s).eventCount) = sliceStageR_O3 F s :=
    Fin.ext rfl
  have hmax : ∀ k : Fin ((sliceTowerHistory_CX2 s).eventCount + 1),
      (sliceTowerHistory_CX2 s).time k ≤ t →
        k ≤ towerIdx_S137 s (Fin.last (sliceHistoryR_O3 F s).eventCount) := by
    intro k hk
    rw [hs1]
    exact (F.tower.history (sliceIndexR_O3 F s)).toHistory.le_activeStage (sliceTimeR_O3 F s) k
      (hk.trans ht.2)
  have key := tube_stage_S146 s B htube t (Fin.last _) (Fin.le_last _) ht.1 ht.2 hmax
  have hq : B.point (Fin.last (sliceHistoryR_O3 F s).eventCount) (Fin.le_last _) (Fin.le_last _) = q :=
    B.endpoint_eq
  rw [hq] at key
  have hm : (sliceTowerHistory_CX2 s).stageMetric (towerIdx_S137 s (Fin.last (sliceHistoryR_O3 F s).eventCount)) t =
      (sliceSlabR_O3 F s).flow.base.metric t := (sliceSlabR_metric_O3 F s t).symm
  rw [hm] at key
  intro x hx
  have h' := key x hx
  rwa [SolutionFamily.rm04, metricRm04_apply]

end GC.LongTime.Ch12

import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.History
import Mathlib.Data.Finset.Max
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

noncomputable section
open Set
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

def activeStage (t : Icc (0 : ℝ) H.horizon) : Fin (H.eventCount + 1) := by
  classical
  let S := Finset.univ.filter (fun j => H.time j ≤ t.1)
  have hS : S.Nonempty := ⟨0, by simp [S, H.time_zero, t.2.1]⟩
  exact S.max' hS

theorem activeStage_time_le (t : Icc (0 : ℝ) H.horizon) :
    H.time (H.activeStage t) ≤ t.1 := by
  classical
  let S : Finset (Fin (H.eventCount + 1)) := Finset.univ.filter (fun j => H.time j ≤ t.1)
  have hS : S.Nonempty := ⟨0, by simp [S, H.time_zero, t.2.1]⟩
  have hm : S.max' hS ∈ S := Finset.max'_mem S hS
  exact (Finset.mem_filter.mp hm).2

theorem le_activeStage (t : Icc (0 : ℝ) H.horizon)
    (j : Fin (H.eventCount + 1)) (hj : H.time j ≤ t.1) :
    j ≤ H.activeStage t := by
  classical
  exact Finset.le_max' _ j (by simp [hj])

theorem activeStage_mono : Monotone H.activeStage := by
  intro t s hts
  exact H.le_activeStage s _ ((H.activeStage_time_le t).trans hts)

theorem time_nonneg (j : Fin (H.eventCount + 1)) : 0 ≤ H.time j := by
  rw [← H.time_zero]
  exact H.time_strictMono.monotone (Fin.zero_le j)

theorem time_le_horizon_at (j : Fin (H.eventCount + 1)) : H.time j ≤ H.horizon :=
  (H.time_strictMono.monotone (Fin.le_last j)).trans H.time_le_horizon

theorem activeStage_at_time (j : Fin (H.eventCount + 1)) :
    H.activeStage ⟨H.time j, H.time_nonneg j, H.time_le_horizon_at j⟩ = j := by
  apply le_antisymm
  · exact H.time_strictMono.le_iff_le.mp (H.activeStage_time_le _)
  · exact H.le_activeStage _ j le_rfl

theorem activeStage_at_horizon :
    H.activeStage ⟨H.horizon, H.horizon_nonneg, le_rfl⟩ = Fin.last H.eventCount := by
  apply le_antisymm (Fin.le_last _)
  exact H.le_activeStage _ _ H.time_le_horizon

theorem activeStage_before_next (t : Icc (0 : ℝ) H.horizon)
    (h : (H.activeStage t).val < H.eventCount) :
    t.1 < H.time (⟨(H.activeStage t).val + 1, by omega⟩ : Fin (H.eventCount + 1)) := by
  by_contra hn
  have hle := H.le_activeStage t
    (⟨(H.activeStage t).val + 1, by omega⟩ : Fin (H.eventCount + 1)) (not_lt.mp hn)
  change (H.activeStage t).val + 1 ≤ (H.activeStage t).val at hle
  omega


abbrev stageAt (t : Icc (0 : ℝ) H.horizon) : OrientedThreeStage.{u} :=
  H.stage (H.activeStage t)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

open scoped Manifold ContDiff
variable {P : OrientedThreeStage} {g : ℝ → P.Metric} {J K : Set ℝ}

theorem MetricSmoothUpTo.mono (hg : P.MetricSmoothUpTo g J) (hK : K ⊆ J) :
    P.MetricSmoothUpTo g K := by
  intro p t ht
  obtain ⟨U, hU, hp, hbase, V, hV, htv, A, hA, heq⟩ := hg p t (hK ht)
  refine ⟨U, hU, hp, hbase, V, hV, htv, A, hA, ?_⟩
  intro s hs x hx i j
  exact heq s ⟨hs.1, hK hs.2⟩ x hx i j

def IncomingSlab.closedPrefix {a s : ℝ} (G : P.IncomingSlab a s)
    (b : ℝ) (hab : a < b) (hbs : b < s) : P.ClosedSlab a b where
  lt := hab
  flow := G.flow.timeRestrict _
  equation := isSolutionOn_timeRestrict G.equation
    (fun _ ht => ⟨ht.1, ht.2.trans_lt hbs⟩)
    (fun _ ht => ⟨ht.1, ht.2.trans hbs⟩)
  smoothUpTo := G.smoothUpTo.mono (fun _ ht => ⟨ht.1, ht.2.trans_lt hbs⟩)


def ClosedSlab.closedPrefix {a b : ℝ} (G : P.ClosedSlab a b)
    (c : ℝ) (hac : a < c) (hcb : c ≤ b) : P.ClosedSlab a c where
  lt := hac
  flow := G.flow.timeRestrict _
  equation := isSolutionOn_timeRestrict G.equation
    (fun _ ht => ⟨ht.1, ht.2.trans hcb⟩)
    (fun _ ht => ⟨ht.1, ht.2.trans_le hcb⟩)
  smoothUpTo := G.smoothUpTo.mono (fun _ ht => ⟨ht.1, ht.2.trans hcb⟩)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})


def stageTime (j : Fin (H.eventCount + 1)) : Icc (0 : ℝ) H.horizon :=
  ⟨H.time j, H.time_nonneg j, H.time_le_horizon_at j⟩

@[simp] theorem activeStage_stageTime (j : Fin (H.eventCount + 1)) :
    H.activeStage (H.stageTime j) = j := H.activeStage_at_time j

theorem activeStage_eq_of_maximal (t : Icc (0 : ℝ) H.horizon)
    (j : Fin (H.eventCount + 1)) (hj : H.time j ≤ t.1)
    (hmax : ∀ k : Fin (H.eventCount + 1), H.time k ≤ t.1 → k ≤ j) :
    H.activeStage t = j :=
  le_antisymm (hmax _ (H.activeStage_time_le t)) (H.le_activeStage t j hj)

def stageDomain (j : Fin (H.eventCount + 1)) : Set ℝ :=
  Fin.lastCases (Icc (H.time (Fin.last H.eventCount)) H.horizon)
    (fun i => Ico (H.time i.castSucc) (H.time i.succ)) j

def stageMetric (j : Fin (H.eventCount + 1)) : ℝ → (H.stage j).Metric :=
  Fin.lastCases
    (if h : H.time (Fin.last H.eventCount) < H.horizon then
      (H.finalSlab h).flow.base.metric
    else fun _ => H.initialMetric (Fin.last H.eventCount))
    (fun i => (H.event i).incoming.flow.base.metric) j

private def closedPrefixOnStage (t : Icc (0 : ℝ) H.horizon)
    (k : Fin (H.eventCount + 1)) :
    H.time k < t.1 →
      (∀ i : Fin H.eventCount, k = i.castSucc → t.1 < H.time i.succ) →
      (H.stage k).ClosedSlab (H.time k) t.1 :=
  Fin.lastCases
    (fun hleft _ =>
      (H.finalSlab (hleft.trans_le t.2.2)).closedPrefix t.1 hleft t.2.2)
    (fun i hleft hright =>
      (H.event i).incoming.closedPrefix t.1 hleft (hright i rfl)) k

private theorem closedPrefixOnStage_last (t : Icc (0 : ℝ) H.horizon)
    (hleft : H.time (Fin.last H.eventCount) < t.1)
    (hright : ∀ i : Fin H.eventCount, Fin.last H.eventCount = i.castSucc →
      t.1 < H.time i.succ) :
    H.closedPrefixOnStage t (Fin.last H.eventCount) hleft hright =
      (H.finalSlab (hleft.trans_le t.2.2)).closedPrefix t.1 hleft t.2.2 := by
  have hcomp := Fin.lastCases_last
    (motive := fun k : Fin (H.eventCount + 1) =>
      H.time k < t.1 →
        (∀ i : Fin H.eventCount, k = i.castSucc → t.1 < H.time i.succ) →
        (H.stage k).ClosedSlab (H.time k) t.1)
    (last := fun hleft _ =>
      (H.finalSlab (hleft.trans_le t.2.2)).closedPrefix t.1 hleft t.2.2)
    (cast := fun i hleft hright =>
      (H.event i).incoming.closedPrefix t.1 hleft (hright i rfl))
  exact congrFun (congrFun hcomp hleft) hright

private theorem closedPrefixOnStage_castSucc (t : Icc (0 : ℝ) H.horizon)
    (i : Fin H.eventCount) (hleft : H.time i.castSucc < t.1)
    (hright : ∀ j : Fin H.eventCount, i.castSucc = j.castSucc → t.1 < H.time j.succ) :
    H.closedPrefixOnStage t i.castSucc hleft hright =
      (H.event i).incoming.closedPrefix t.1 hleft (hright i rfl) := by
  have hcomp := Fin.lastCases_castSucc
    (motive := fun k : Fin (H.eventCount + 1) =>
      H.time k < t.1 →
        (∀ j : Fin H.eventCount, k = j.castSucc → t.1 < H.time j.succ) →
        (H.stage k).ClosedSlab (H.time k) t.1)
    (last := fun hleft _ =>
      (H.finalSlab (hleft.trans_le t.2.2)).closedPrefix t.1 hleft t.2.2)
    (cast := fun j hleft hright =>
      (H.event j).incoming.closedPrefix t.1 hleft (hright j rfl)) i
  exact congrFun (congrFun hcomp hleft) hright
private theorem closedPrefixOnStage_initial (t : Icc (0 : ℝ) H.horizon)
    (k : Fin (H.eventCount + 1)) (hleft : H.time k < t.1)
    (hright : ∀ i : Fin H.eventCount, k = i.castSucc → t.1 < H.time i.succ) :
    (H.closedPrefixOnStage t k hleft hright).flow.base.metric (H.time k) =
      H.initialMetric k := by
  cases k using Fin.lastCases with
  | last =>
    rw [H.closedPrefixOnStage_last]
    change (H.finalSlab (hleft.trans_le t.2.2)).flow.base.metric
      (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount)
    exact H.final_initial (hleft.trans_le t.2.2)
  | cast i =>
    rw [H.closedPrefixOnStage_castSucc]
    change (H.event i).incoming.flow.base.metric (H.time i.castSucc) = H.initialMetric i.castSucc
    exact H.event_initial i


def closedPrefixAt (t : Icc (0 : ℝ) H.horizon) (h : H.time (H.activeStage t) < t.1) :
    (H.stage (H.activeStage t)).ClosedSlab (H.time (H.activeStage t)) t.1 :=
  H.closedPrefixOnStage t (H.activeStage t) h (fun i hi => by
    have hk : (H.activeStage t).val < H.eventCount := by rw [hi]; exact i.isLt
    have hn := H.activeStage_before_next t hk
    have he : (⟨(H.activeStage t).val + 1, by omega⟩ : Fin (H.eventCount + 1)) = i.succ := by
      apply Fin.ext
      change (H.activeStage t).val + 1 = i.val + 1
      have hv := congrArg Fin.val hi
      exact congrArg (· + 1) hv
    simpa only [he] using hn)


theorem closedPrefixAt_initial (t : Icc (0 : ℝ) H.horizon)
    (h : H.time (H.activeStage t) < t.1) :
    (H.closedPrefixAt t h).flow.base.metric (H.time (H.activeStage t)) =
      H.initialMetric (H.activeStage t) :=
  H.closedPrefixOnStage_initial t (H.activeStage t) h _

private theorem closedPrefixOnStage_metric (t : Icc (0 : ℝ) H.horizon)
    (k : Fin (H.eventCount + 1)) (hleft : H.time k < t.1)
    (hright : ∀ i : Fin H.eventCount, k = i.castSucc → t.1 < H.time i.succ)
    (τ : ℝ) :
    (H.closedPrefixOnStage t k hleft hright).flow.base.metric τ = H.stageMetric k τ := by
  cases k using Fin.lastCases with
  | last =>
    have hf : H.time (Fin.last H.eventCount) < H.horizon := hleft.trans_le t.2.2
    rw [H.closedPrefixOnStage_last]
    simp only [stageMetric, Fin.lastCases_last, dif_pos hf]
    rfl
  | cast i =>
    rw [H.closedPrefixOnStage_castSucc]
    simp only [stageMetric, Fin.lastCases_castSucc]
    rfl

theorem closedPrefixAt_metric (t : Icc (0 : ℝ) H.horizon)
    (h : H.time (H.activeStage t) < t.1) (τ : ℝ) :
    (H.closedPrefixAt t h).flow.base.metric τ = H.stageMetric (H.activeStage t) τ :=
  H.closedPrefixOnStage_metric t (H.activeStage t) h _ τ

def restrict (t : Icc (0 : ℝ) H.horizon) : ObservedHistory.{u} := by
  let k := H.activeStage t
  have hk : k.val ≤ H.eventCount := Nat.le_of_lt_succ k.isLt
  let cast : Fin (k.val + 1) → Fin (H.eventCount + 1) :=
    Fin.castLE (Nat.add_le_add_right hk 1)
  refine {
    horizon := t.1
    horizon_nonneg := t.2.1
    eventCount := k.val
    time := fun j => H.time (cast j)
    time_strictMono := fun _ _ hij => H.time_strictMono hij
    time_zero := H.time_zero
    time_le_horizon := H.activeStage_time_le t
    stage := fun j => H.stage (cast j)
    initialMetric := fun j => H.initialMetric (cast j)
    event := fun i => H.event (Fin.castLE hk i)
    event_initial := fun i => H.event_initial (Fin.castLE hk i)
    event_output := fun i => H.event_output (Fin.castLE hk i)
    finalSlab := fun h => H.closedPrefixAt t h
    final_initial := fun h => H.closedPrefixAt_initial t h }

@[simp] theorem restrict_horizon (t : Icc (0 : ℝ) H.horizon) :
    (H.restrict t).horizon = t.1 := rfl

@[simp] theorem restrict_eventCount (t : Icc (0 : ℝ) H.horizon) :
    (H.restrict t).eventCount = (H.activeStage t).val := rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

@[simp] theorem restrict_stage_zero (t : Icc (0 : ℝ) H.horizon) :
    (H.restrict t).stage 0 = H.stage 0 := rfl

@[simp] theorem restrict_initialMetric_zero (t : Icc (0 : ℝ) H.horizon) :
    (H.restrict t).initialMetric 0 = H.initialMetric 0 := rfl

theorem restrict_event (t : Icc (0 : ℝ) H.horizon) (i : Fin (H.restrict t).eventCount) :
    HEq ((H.restrict t).event i)
      (H.event (Fin.castLE (Nat.le_of_lt_succ (H.activeStage t).isLt) i)) := HEq.rfl

theorem event_reached_iff (t : Icc (0 : ℝ) H.horizon) (i : Fin H.eventCount) :
    H.time i.succ ≤ t.1 ↔ i.val < (H.activeStage t).val := by
  constructor
  · intro hi
    have hh := H.le_activeStage t i.succ hi
    change i.val + 1 ≤ (H.activeStage t).val at hh
    omega
  · intro hi
    apply le_trans (H.time_strictMono.monotone ?_) (H.activeStage_time_le t)
    change i.val + 1 ≤ (H.activeStage t).val
    omega


def eventTimes : Set ℝ := Set.range (fun i : Fin H.eventCount => H.time i.succ)

theorem restrict_eventTimes (t : Icc (0 : ℝ) H.horizon) :
    (H.restrict t).eventTimes = H.eventTimes ∩ Ioc 0 t.1 := by
  ext s
  constructor
  · rintro ⟨i, rfl⟩
    let j : Fin H.eventCount := Fin.castLE (Nat.le_of_lt_succ (H.activeStage t).isLt) i
    refine ⟨⟨j, rfl⟩, ?_, ?_⟩
    · change 0 < H.time j.succ
      rw [← H.time_zero]
      exact H.time_strictMono (by change 0 < j.val + 1; omega)
    · exact (H.event_reached_iff t j).mpr i.isLt
  · rintro ⟨⟨i, rfl⟩, ht⟩
    exact ⟨⟨i.val, (H.event_reached_iff t i).mp ht.2⟩, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification

universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {H : ObservedHistory.{u}}

def restrict (A : InitialIdentification P g H) (t : Icc (0 : ℝ) H.horizon) :
    InitialIdentification P g (H.restrict t) where
  map := A.map
  positive := A.positive
  metric_eq := A.metric_eq

@[simp] theorem restrict_map (A : InitialIdentification P g H) (t : Icc (0 : ℝ) H.horizon) :
    (A.restrict t).map = A.map := rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification

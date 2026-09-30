import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.ClassifiedHistory
import DifferentialGeometry.Geometry.Metric.CompactExistence
import Mathlib.Order.Filter.AtTopBot.Finite

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set Filter
namespace GC.LongTime
universe u

structure RegularSlice {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) where
  time : ℝ
  positive : 0 < time
  regular : time ∉ T.eventTimes
  preceding : (T.observe time positive.le).time
    (Fin.last (T.observe time positive.le).eventCount) < time

namespace RegularSlice
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {T : ObservationTower P g}

abbrev history (s : RegularSlice T) : ObservedHistory := T.observe s.time s.positive.le

abbrev stage (s : RegularSlice T) : OrientedThreeStage :=
  s.history.stage (Fin.last s.history.eventCount)

def metric (s : RegularSlice T) : s.stage.Metric :=
  s.history.stageMetric (Fin.last s.history.eventCount) s.time

def normalizedMetric (s : RegularSlice T) : s.stage.Metric :=
  scaleMetric s.time⁻¹ (inv_pos.mpr s.positive) s.metric

def curvatureOneMetric (s : RegularSlice T) : s.stage.Metric :=
  scaleMetric (4 * s.time)⁻¹ (inv_pos.mpr (mul_pos (by norm_num) s.positive)) s.metric

def initial (s : RegularSlice T) : InitialIdentification P g s.history :=
  T.observeInitial s.time s.positive.le

end RegularSlice

def hasArbitrarilyLateNonemptySlices {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) : Prop :=
  ∀ B : ℝ, ∃ s : RegularSlice T, B < s.time ∧ Nonempty s.stage.Carrier

theorem exists_regular_slice_after {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) (B : ℝ) :
    ∃ s : RegularSlice T, B < s.time := by
  obtain ⟨t, ht, hBt, hreg, hpre, _⟩ := GC.Surgery.late_prefix_with_initial T B
  exact ⟨⟨t, ht, hreg, hpre⟩, hBt⟩

theorem empty_slice_or_arbitrarily_late {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) :
    (∃ s : RegularSlice T, IsEmpty s.stage.Carrier) ∨
      hasArbitrarilyLateNonemptySlices T := by
  classical
  by_cases h : hasArbitrarilyLateNonemptySlices T
  · exact Or.inr h
  · left
    simp only [hasArbitrarilyLateNonemptySlices, not_forall, not_exists,
      not_and, not_nonempty_iff] at h
    obtain ⟨B, hB⟩ := h
    obtain ⟨s, hs⟩ := exists_regular_slice_after T B
    exact ⟨s, hB s hs⟩

theorem exists_common_late_slice {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) (hlate : hasArbitrarilyLateNonemptySlices T)
    {ι : Type*} (indices : Finset ι) (q : ι → RegularSlice T → Prop)
    (eventually : ∀ i ∈ indices, ∃ B : ℝ, ∀ s : RegularSlice T,
      B < s.time → q i s) (B : ℝ) :
    ∃ s : RegularSlice T, B < s.time ∧ Nonempty s.stage.Carrier ∧
      ∀ i ∈ indices, q i s := by
  classical
  have hbound : ∃ R : ℝ, B ≤ R ∧ ∀ i ∈ indices, ∀ s : RegularSlice T,
      R < s.time → q i s := by
    induction indices using Finset.induction_on with
    | empty => exact ⟨B, le_rfl, by simp⟩
    | @insert a set ha ih =>
      obtain ⟨R, hBR, hR⟩ := ih (fun i hi => eventually i (Finset.mem_insert_of_mem hi))
      obtain ⟨S, hS⟩ := eventually a (Finset.mem_insert_self _ _)
      refine ⟨max R S, hBR.trans (le_max_left _ _), ?_⟩
      intro i hi s hs
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hS s ((le_max_right _ _).trans_lt hs)
      · exact hR i hi s ((le_max_left _ _).trans_lt hs)
  obtain ⟨R, hBR, hR⟩ := hbound
  obtain ⟨s, hs, hne⟩ := hlate R
  exact ⟨s, hBR.trans_lt hs, hne, fun i hi => hR i hi s hs⟩

theorem geometrizes_of_late_slice_supply
    (M : ConnectedClosedOrientedManifold.{u} 3)
    {g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric}
    (F : GC.Interface.RawSurgery
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (supply : ∃ B : ℝ, ∀ s : RegularSlice F.observation,
      B < s.time → Nonempty s.stage.Carrier →
        GC.Endpoint.ComponentsGeometrize s.stage.toClosedOrientedManifold) :
    GC.Endpoint.Geometrizes M := by
  apply GC.Endpoint.geometrizes_of_raw_late M F
  obtain ⟨B, hB⟩ := supply
  refine ⟨B, ?_⟩
  intro t ht hBt hreg hpre hne
  exact hB ⟨t, ht, hreg, hpre⟩ hBt hne

end GC.LongTime

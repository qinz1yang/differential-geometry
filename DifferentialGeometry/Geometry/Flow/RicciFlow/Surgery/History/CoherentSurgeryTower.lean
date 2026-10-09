import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.GeneralPrefixExtension
set_option autoImplicit false
noncomputable section
open Set
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private structure IntegerHistory (P : OrientedThreeStage.{u}) (g : P.Metric) (n : ℕ) where
  history : RetainedCoreHistory.{u}
  initial : InitialIdentification P g history.toHistory
  horizon_eq : history.horizon = (n : ℝ)
  control : HistoryEventControl history

private def integer_start (P : OrientedThreeStage.{u}) (g : P.Metric) :
    IntegerHistory P g 0 where
  history := RetainedCoreHistory.atZero P g
  initial := InitialIdentification.atZero P g
  horizon_eq := by simp
  control := fun i => Fin.elim0 i

private theorem integer_extension {P : OrientedThreeStage.{u}} {g : P.Metric}
    {n : ℕ} (L : IntegerHistory P g n) :
    ∃ R : IntegerHistory P g (n+1), L.initial.IsPrefixOf R.initial := by
  have ht : L.history.horizon < ((n+1 : ℕ) : ℝ) := by
    rw [L.horizon_eq]
    exact_mod_cast Nat.lt_succ_self n
  obtain ⟨J,A,hj,ha,hc,-⟩ :=
    general_controlled_history_extension P g L.history L.initial L.control ((n+1 : ℕ) : ℝ) ht
  exact ⟨⟨J,A,hj,hc⟩,ha⟩

private def integer_next {P : OrientedThreeStage.{u}} {g : P.Metric}
    {n : ℕ} (L : IntegerHistory P g n) : IntegerHistory P g (n+1) :=
  Classical.choose (integer_extension L)

private theorem integer_next_prefix {P : OrientedThreeStage.{u}} {g : P.Metric}
    {n : ℕ} (L : IntegerHistory P g n) : L.initial.IsPrefixOf (integer_next L).initial :=
  Classical.choose_spec (integer_extension L)

private def integer_chain (P : OrientedThreeStage.{u}) (g : P.Metric) :
    (n : ℕ) → IntegerHistory P g n
  | 0 => integer_start P g
  | n+1 => integer_next (integer_chain P g n)

def general_retained_core_tower (P : OrientedThreeStage.{u}) (g : P.Metric) :
    RetainedCoreObservationTower P g where
  history := fun n => (integer_chain P g n).history
  horizon_eq := fun n => (integer_chain P g n).horizon_eq
  initial := fun n => (integer_chain P g n).initial
  successor := fun n => by
    have hp := (integer_next_prefix (integer_chain P g n)).1.presentation
    simpa only [integer_chain, (integer_chain P g n).horizon_eq] using hp
  initial_successor := fun n => (integer_next_prefix (integer_chain P g n)).2.symm

theorem general_retained_core_tower_control (P : OrientedThreeStage.{u}) (g : P.Metric)
    (n : ℕ) : HistoryEventControl ((general_retained_core_tower P g).history n) :=
  (integer_chain P g n).control

theorem general_retained_core_tower_geometry (P : OrientedThreeStage.{u}) (g : P.Metric)
    (n : ℕ) (i : Fin ((general_retained_core_tower P g).history n).eventCount) :
    GC.Surgery.ActualMetricEventGeometry
      (((general_retained_core_tower P g).history n).coreEvent i).toMetricCutCapEvent :=
  controlled_event_geometry _ (general_retained_core_tower_control P g n i)

theorem general_retained_core_tower_locally_finite (P : OrientedThreeStage.{u})
    (g : P.Metric) (a b : ℝ) :
    ((general_retained_core_tower P g).toObservationTower.eventTimes ∩ Icc a b).Finite :=
  (general_retained_core_tower P g).toObservationTower.eventTimes_finite_Icc a b

end GC.GeneralFlow

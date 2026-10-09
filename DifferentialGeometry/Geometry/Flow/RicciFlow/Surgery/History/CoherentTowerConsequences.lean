import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.CoherentSurgeryTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.LateOrEmpty
set_option autoImplicit false
noncomputable section
open Set
namespace GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

theorem general_late_prefix_with_initial (P : OrientedThreeStage.{u}) (g : P.Metric)
    (B : ℝ) :
    let T := (general_retained_core_tower P g).toObservationTower
    ∃ (t : ℝ) (ht : 0 < t), B < t ∧ t ∉ T.eventTimes ∧
      (T.observe t ht.le).time (Fin.last (T.observe t ht.le).eventCount) < t ∧
      Nonempty (InitialIdentification P g (T.observe t ht.le)) :=
  GC.Surgery.late_prefix_with_initial _ B

theorem general_late_nonempty_or_absorbing_empty (P : OrientedThreeStage.{u})
    (g : P.Metric) :
    let T := (general_retained_core_tower P g).toObservationTower
    (∃ (a : ℝ) (_ha : 0 ≤ a),
      (∀ (b : ℝ) (hb : 0 ≤ b), a ≤ b →
        IsEmpty ((T.observe b hb).stage (Fin.last (T.observe b hb).eventCount)).Carrier) ∧
      (∀ s ∈ T.eventTimes, s ≤ a)) ∨
    (∀ B : ℝ, ∃ (t : ℝ) (ht : 0 < t), B < t ∧ t ∉ T.eventTimes ∧
      (T.observe t ht.le).time (Fin.last (T.observe t ht.le).eventCount) < t ∧
      Nonempty ((T.observe t ht.le).stage (Fin.last (T.observe t ht.le).eventCount)).Carrier) :=
  GC.Surgery.late_nonempty_or_absorbing_empty _

end GC.GeneralFlow

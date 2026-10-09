import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialState
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.ScaffoldData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordHistoryRestriction.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace GC.GeneralFlow
universe u

/-- The full histories leave a strict buffer after every integer observation. -/
def preparedSpatialHorizon : ℕ → ℝ
  | 0 => 0
  | n + 1 => (3 : ℝ) ^ n

theorem nat_lt_three_pow (n : ℕ) : (n : ℝ) < (3 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith

/-- This is the actual selected recursive family, including its prescribed fine
accuracy and delayed radius activation. Its existence is supplied by the base
and prepared spatial successor; it is not a replacement geometric hypothesis. -/
structure PreparedSpatialChain (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (P : OrientedThreeStage.{u}) (g : P.Metric) where
  state : ∀ n : ℕ, PreparedSpatialState pBase C P g
    (preparedSpatialHorizon n) ((3 : ℝ) ^ n)
  accuracy : ℕ → ℝ
  accuracy_pos : ∀ n, 0 < accuracy n
  accuracy_lt_one : ∀ n, accuracy n < 1
  accuracy_le : ∀ n, accuracy n ≤ 1 / ((n : ℝ) + 2)
  successor : ∀ n, PreparedSpatialSuccessor (state n) (state (n + 1))
    ((5 / 6 : ℝ) * 3 ^ n) (1 / ((n : ℝ) + 2)) (accuracy n)
  initial_history : (state 0).history = RetainedCoreHistory.atZero P g
  initial_radius_le : (state 0).radius ≤ 1

namespace PreparedSpatialChain
variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}
  (S : PreparedSpatialChain pBase C P g)

/-- Observe the same full history at the integer, strictly before its horizon. -/
def observationTime (n : ℕ) : Icc (0 : ℝ) (S.state (n + 1)).history.horizon :=
  ⟨n, Nat.cast_nonneg n, by
    rw [(S.state (n + 1)).horizon_eq]
    exact (nat_lt_three_pow n).le⟩

def observation (n : ℕ) : ScaffoldState pBase P g C.epsilon n where
  history := (S.state (n + 1)).history.restrict (S.observationTime n)
  initial := (S.state (n + 1)).initial.restrict (S.observationTime n)
  horizon_eq := rfl
  parameters := (S.state (n + 1)).parameters
  records := (S.state (n + 1)).history.restrictRecords (S.observationTime n)
    (S.state (n + 1)).records
  static_eq := (S.state (n + 1)).static_eq
  control := history_control_restrict (S.state (n + 1)).eventControl (S.observationTime n)
  windows := (S.state (n + 1)).history.canonicalWindows_restrictRecords
    (S.observationTime n) (S.state (n + 1)).records (S.state (n + 1)).windows
  linked := fun i b => (S.state (n + 1)).linked
    (Fin.castLE (Nat.le_of_lt_succ ((S.state (n + 1)).history.toHistory.activeStage
      (S.observationTime n)).isLt) i) b
  kappa := (S.state (n + 1)).kappa
  kappa_pos := (S.state (n + 1)).kappa_pos
  noncollapsed := (S.state (n + 1)).history.noncollapsedBefore_restrict
    (S.observationTime n) (S.state (n + 1)).noncollapsed (S.observationTime n).2.2

theorem observation_successor (n : ℕ) :
    ScaffoldSuccessor (S.observation n) (S.observation (n + 1)) := by
  let L := S.state (n + 1)
  let R := S.state (n + 2)
  let a := S.observationTime n
  let b := S.observationTime (n + 1)
  have hLR := (S.successor (n + 1)).initial_prefix
  have hcut := L.initial.restrict_isPrefixOf a
  have hprefix := hcut.trans hLR
  have hab : (L.history.restrict a).horizon ≤ (b : ℝ) := by
    change (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
    exact_mod_cast Nat.le_succ n
  have hcutCount : (L.history.restrict a).eventCount ≤ L.history.eventCount :=
    Nat.le_of_lt_succ (L.history.toHistory.activeStage a).isLt
  have hcount : (L.history.restrict a).eventCount ≤ R.history.eventCount :=
    hcutCount.trans (S.successor (n + 1)).count_le
  have hrecords (i : Fin (L.history.restrict a).eventCount) :
      HEq (R.records (i.castLE hcount)).nominalRadius
        (L.history.restrictRecords a L.records i).nominalRadius ∧
      HEq (R.records (i.castLE hcount)).delta
        (L.history.restrictRecords a L.records i).delta ∧
      HEq (R.records (i.castLE hcount)).order
        (L.history.restrictRecords a L.records i).order ∧
      HEq (R.records (i.castLE hcount)).neck
        (L.history.restrictRecords a L.records i).neck ∧
      HEq (R.records (i.castLE hcount)).static
        (L.history.restrictRecords a L.records i).static := by
    have h₁ := (S.successor (n + 1)).records_preserved (i.castLE hcutCount)
    have h₂ := L.history.restrictRecords_preserves a L.records i
    exact ⟨h₁.1.trans h₂.1.symm, h₁.2.1.trans h₂.2.1.symm,
      h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.1.trans h₂.2.2.2.1.symm,
      h₁.2.2.2.2.trans h₂.2.2.2.2.symm⟩
  obtain ⟨hn, hOld⟩ := RetainedCoreHistory.restrictRecords_preserves_old
    (L.history.restrictRecords a L.records) R.records hprefix.1 hcount hrecords b hab
  refine ⟨hprefix.restrict_right b hab, hn, ?_, hOld⟩
  intro t ht
  exact (S.successor (n + 1)).parameters_past t
    (ht.trans (nat_lt_three_pow n).le)

/-- Integer observations are restrictions of this chain, with its original
marking. No independently constructed scaffold history is selected. -/
def tower : RetainedCoreObservationTower P g where
  history := fun n => (S.observation n).history
  horizon_eq := fun n => (S.observation n).horizon_eq
  initial := fun n => (S.observation n).initial
  successor := fun n => by
    have hp := (S.observation_successor n).initial_prefix.1.presentation
    simpa only [(S.observation n).horizon_eq] using hp
  initial_successor := fun n => (S.observation_successor n).initial_prefix.2.symm

open private overlapCastPoint overlapCastPoint_heq overlap_scalar_eq
  overlap_spatialWitness_transport from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport

/-- The strict full-history buffer supplies the closed endpoint of each actual
integer observation, including a surgery birth at that integer. -/
theorem observation_canonical (n : ℕ)
    (t : Icc (0 : ℝ) (S.observation n).history.toHistory.horizon)
    (x : ((S.observation n).history.toHistory.stageAt t).Carrier)
    (hx : ((S.observation n).parameters.neckRadius t ^ 2)⁻¹ < metricScalarAt
      ((S.observation n).history.toHistory.stageMetric
        ((S.observation n).history.toHistory.activeStage t) t) x) :
    ∃ W : SpatialCanonicalWitness
      ((S.observation n).history.toHistory.stageMetric
        ((S.observation n).history.toHistory.activeStage t) t)
      C.epsilon (max C.C1s C.Cbirth) (max C.C2s (max C.Cbirth (C.Cgrad : ℝ))) x,
      W.capTubeHasNeckChart C.epsilon := by
  let H := (S.state (n + 1)).history
  let a := S.observationTime n
  let tH : Icc (0 : ℝ) H.toHistory.horizon :=
    ⟨t, t.2.1, t.2.2.trans a.2.2⟩
  have hstage : (H.restrict a).toHistory.stageAt t = H.toHistory.stageAt tH :=
    H.toHistory.restrict_stageAt a t
  have hmetric : HEq
      ((H.restrict a).toHistory.stageMetric ((H.restrict a).toHistory.activeStage t) t)
      (H.toHistory.stageMetric (H.toHistory.activeStage tH) tH) :=
    H.toHistory.restrict_sliceMetric a t
  let xH := overlapCastPoint hstage x
  have hpoint : HEq x xH := (overlapCastPoint_heq hstage x).symm
  have hscalar := overlap_scalar_eq hstage hmetric hpoint
  have hxH : ((S.state (n + 1)).parameters.neckRadius tH ^ 2)⁻¹ <
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage tH) tH) xH := by
    rw [← hscalar]
    exact hx
  have htH : (tH : ℝ) < preparedSpatialHorizon (n + 1) :=
    t.2.2.trans_lt (nat_lt_three_pow n)
  obtain ⟨W, hW⟩ := (S.state (n + 1)).canonical tH htH xH hxH
  obtain ⟨W', hW', _⟩ := overlap_spatialWitness_transport hstage.symm
    hmetric.symm hpoint.symm W hW
  exact ⟨W', hW'⟩

end PreparedSpatialChain
end GC.GeneralFlow

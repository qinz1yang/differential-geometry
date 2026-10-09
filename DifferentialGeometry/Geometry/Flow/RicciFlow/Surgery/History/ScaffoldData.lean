import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.RawSurgery.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LinkedCanonicalWindowC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapse.Basic

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry.PDE.RicciFlow
open scoped ENNReal

namespace GC.GeneralFlow

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure ScaffoldState (p₀ : CutoffParameters)
    (P : OrientedThreeStage.{u}) (g : P.Metric) (ε : ℝ) (n : ℕ) where
  history : RetainedCoreHistory.{u}
  initial : InitialIdentification P g history.toHistory
  horizon_eq : history.horizon = (n : ℝ)
  parameters : CutoffParameters
  records : ∀ i : Fin history.eventCount,
    GeometricCutoffRecord history.toHistory i parameters
  static_eq : parameters.fixed = p₀.fixed ∧ parameters.modelRadius = p₀.modelRadius ∧
    parameters.modelOrder = p₀.modelOrder ∧ parameters.modelAccuracy = p₀.modelAccuracy ∧
    parameters.recenterConstant = p₀.recenterConstant
  control : HistoryEventControl history
  windows : ∀ i b, ((records i).static b).hasCanonicalWindow
  linked : ∀ i b, ((records i).static b).hasLinkedCanonicalWindow_C12X
  kappa : ℝ
  kappa_pos : 0 < kappa
  noncollapsed : history.NoncollapsedBefore kappa ε history.horizon

structure ScaffoldSuccessor {p₀ : CutoffParameters}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {ε : ℝ} {n : ℕ}
    (L : ScaffoldState p₀ P g ε n) (R : ScaffoldState p₀ P g ε (n + 1)) : Prop where
  initial_prefix : L.initial.IsPrefixOf R.initial
  count_le : L.history.eventCount ≤ R.history.eventCount
  parameters_past : ∀ t : ℝ, t ≤ L.history.horizon →
    R.parameters.delta t = L.parameters.delta t ∧
    R.parameters.neckRadius t = L.parameters.neckRadius t ∧
    R.parameters.protectedRadius t = L.parameters.protectedRadius t
  records_preserved : ∀ i : Fin L.history.eventCount,
    HEq (R.records (i.castLE count_le)).nominalRadius (L.records i).nominalRadius ∧
    HEq (R.records (i.castLE count_le)).delta (L.records i).delta ∧
    HEq (R.records (i.castLE count_le)).order (L.records i).order ∧
    HEq (R.records (i.castLE count_le)).neck (L.records i).neck ∧
    HEq (R.records (i.castLE count_le)).static (L.records i).static

theorem all_record_fields_of_successors
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : RetainedCoreObservationTower P g) (p : ℕ → CutoffParameters)
    (R : ∀ n : ℕ, ∀ i : Fin (T.history n).eventCount,
      GeometricCutoffRecord (T.history n).toHistory i (p n))
    (hnext : ∀ n : ℕ, ∃ hn : (T.history n).eventCount ≤ (T.history (n + 1)).eventCount,
      ∀ i : Fin (T.history n).eventCount,
        HEq (R (n + 1) (i.castLE hn)).nominalRadius (R n i).nominalRadius ∧
        HEq (R (n + 1) (i.castLE hn)).delta (R n i).delta ∧
        HEq (R (n + 1) (i.castLE hn)).order (R n i).order ∧
        HEq (R (n + 1) (i.castLE hn)).neck (R n i).neck ∧
        HEq (R (n + 1) (i.castLE hn)).static (R n i).static) :
    ∃ hmono : Monotone (fun n => (T.history n).eventCount),
      ∀ (m n : ℕ) (hmn : m ≤ n) (i : Fin (T.history m).eventCount),
        HEq (R n (i.castLE (hmono hmn))).nominalRadius (R m i).nominalRadius ∧
        HEq (R n (i.castLE (hmono hmn))).delta (R m i).delta ∧
        HEq (R n (i.castLE (hmono hmn))).order (R m i).order ∧
        HEq (R n (i.castLE (hmono hmn))).neck (R m i).neck ∧
        HEq (R n (i.castLE (hmono hmn))).static (R m i).static := by
  classical
  choose hc hold using hnext
  have hmono : Monotone (fun n => (T.history n).eventCount) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact le_refl _
    | succ n _ ih => exact ih.trans (hc n)
  refine ⟨hmono, ?_⟩
  intro m n hmn i
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  | succ n hmn ih =>
    obtain ⟨hr, hd, ho, hk, hs⟩ := hold n (i.castLE (hmono hmn))
    exact ⟨hr.trans ih.1, hd.trans ih.2.1, ho.trans ih.2.2.1,
      hk.trans ih.2.2.2.1, hs.trans ih.2.2.2.2⟩

theorem all_parameter_values_of_successors
    (p : ℕ → CutoffParameters)
    (hnext : ∀ n : ℕ, ∀ t : ℝ, t ≤ (n : ℝ) →
      (p (n + 1)).delta t = (p n).delta t ∧
      (p (n + 1)).neckRadius t = (p n).neckRadius t ∧
      (p (n + 1)).protectedRadius t = (p n).protectedRadius t) :
    ∀ m n : ℕ, m ≤ n → ∀ t : ℝ, t ≤ (m : ℝ) →
      (p n).delta t = (p m).delta t ∧
      (p n).neckRadius t = (p m).neckRadius t ∧
      (p n).protectedRadius t = (p m).protectedRadius t := by
  intro m n hmn t ht
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨rfl, rfl, rfl⟩
  | succ n hmn ih =>
    have htn : t ≤ (n : ℝ) := ht.trans (by exact_mod_cast hmn)
    obtain ⟨hd, hr, hp⟩ := hnext n t htn
    exact ⟨hd.trans ih.1, hr.trans ih.2.1, hp.trans ih.2.2⟩

end GC.GeneralFlow

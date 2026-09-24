import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.TowerExtinctionHorizon

set_option autoImplicit false
noncomputable section
open Set
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

namespace RetainedCoreHistory
variable {P : OrientedThreeStage.{u}}

def absorbingHistory (H : RetainedCoreHistory P)
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier] (n : ℕ) :
    RetainedCoreHistory P :=
  if h : (n : ℝ) < H.horizon then
    H.restrict ⟨(n : ℝ), Nat.cast_nonneg n, h.le⟩
  else H.emptyExtension (n : ℝ) (le_of_not_gt h)

theorem absorbingHistory_eq_restrict (H : RetainedCoreHistory P)
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier] (n : ℕ)
    (h : (n : ℝ) < H.horizon) :
    H.absorbingHistory n = H.restrict ⟨(n : ℝ), Nat.cast_nonneg n, h.le⟩ :=
  dif_pos h

theorem absorbingHistory_eq_emptyExtension (H : RetainedCoreHistory P)
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier] (n : ℕ)
    (h : H.horizon ≤ (n : ℝ)) :
    H.absorbingHistory n = H.emptyExtension (n : ℝ) h :=
  dif_neg (not_lt.mpr h)

theorem absorbingHistory_horizon (H : RetainedCoreHistory P)
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier] (n : ℕ) :
    (H.absorbingHistory n).horizon = (n : ℝ) := by
  unfold absorbingHistory
  split_ifs <;> rfl

private theorem restrict_samePresentation_of_eq {J K : ObservedHistory.{u}}
    (h : J = K) (p : Icc (0 : ℝ) J.horizon) (q : Icc (0 : ℝ) K.horizon)
    (hpq : p.1 = q.1) : (J.restrict p).SamePresentation (K.restrict q) := by
  subst K
  have hp : p = q := Subtype.ext hpq
  subst q
  exact ObservedHistory.SamePresentation.refl _

private theorem samePresentation_of_eq {J K : ObservedHistory.{u}} (h : J = K) :
    J.SamePresentation K := by
  subst K
  exact ObservedHistory.SamePresentation.refl _

theorem absorbingHistory_successor (H : RetainedCoreHistory P)
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier] (n : ℕ)
    (p : Icc (0 : ℝ) (H.absorbingHistory (n + 1)).toHistory.horizon)
    (hp : p.1 = (n : ℝ)) :
    ((H.absorbingHistory (n + 1)).toHistory.restrict p).SamePresentation
      (H.absorbingHistory n).toHistory := by
  have hstep : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  by_cases hn : (n : ℝ) < H.horizon
  · have e0 := congrArg RetainedCoreHistory.toHistory (H.absorbingHistory_eq_restrict n hn)
    by_cases hs : ((n + 1 : ℕ) : ℝ) < H.horizon
    · have e1 := congrArg RetainedCoreHistory.toHistory
        (H.absorbingHistory_eq_restrict (n + 1) hs)
      have htransport := restrict_samePresentation_of_eq e1 p
        ⟨(n : ℝ), Nat.cast_nonneg n, hstep⟩ hp
      exact htransport.trans ((H.successor_restrict_restrict n
        (not_le_of_gt hn) (not_le_of_gt hs)).trans (samePresentation_of_eq e0.symm))
    · have hs' := le_of_not_gt hs
      have e1 := congrArg RetainedCoreHistory.toHistory
        (H.absorbingHistory_eq_emptyExtension (n + 1) hs')
      have htransport := restrict_samePresentation_of_eq e1 p
        ⟨(n : ℝ), Nat.cast_nonneg n, hstep⟩ hp
      exact htransport.trans ((H.successor_empty_restrict n
        (not_le_of_gt hn) hs').trans (samePresentation_of_eq e0.symm))
  · have hn' := le_of_not_gt hn
    have hs := hn'.trans hstep
    have e0 := congrArg RetainedCoreHistory.toHistory
      (H.absorbingHistory_eq_emptyExtension n hn')
    have e1 := congrArg RetainedCoreHistory.toHistory
      (H.absorbingHistory_eq_emptyExtension (n + 1) hs)
    have htransport := restrict_samePresentation_of_eq e1 p
      ⟨(n : ℝ), Nat.cast_nonneg n, hstep⟩ hp
    exact htransport.trans ((H.successor_empty_empty n hn' hs).trans
      (samePresentation_of_eq e0.symm))

theorem absorbingHistory_stage_zero (H : RetainedCoreHistory P)
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier] (n : ℕ) :
    (H.absorbingHistory n).toHistory.stage 0 = H.toHistory.stage 0 := by
  by_cases h : (n : ℝ) < H.horizon
  · rw [absorbingHistory_eq_restrict H n h]
    rfl
  · rw [absorbingHistory_eq_emptyExtension H n (le_of_not_gt h)]
    rfl

theorem absorbingHistory_initialMetric_zero (H : RetainedCoreHistory P)
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier] (n : ℕ) :
    HEq ((H.absorbingHistory n).toHistory.initialMetric 0) (H.toHistory.initialMetric 0) := by
  by_cases h : (n : ℝ) < H.horizon
  · rw [absorbingHistory_eq_restrict H n h]
    simp only [RetainedCoreHistory.restrict_toHistory]
    exact heq_of_eq (ObservedHistory.restrict_initialMetric_zero H.toHistory _)
  · rw [absorbingHistory_eq_emptyExtension H n (le_of_not_gt h)]
    rfl

def absorbingInitial {g : P.Metric} (H : RetainedCoreHistory P)
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (A : InitialIdentification P g H.toHistory) (n : ℕ) :
    InitialIdentification P g (H.absorbingHistory n).toHistory :=
  InitialIdentification.of_stageZero A (H.absorbingHistory_stage_zero n)
    (H.absorbingHistory_initialMetric_zero n)

theorem absorbingInitial_map_heq {g : P.Metric} (H : RetainedCoreHistory P)
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (A : InitialIdentification P g H.toHistory) (n : ℕ) :
    HEq (H.absorbingInitial A n).map A.map :=
  InitialIdentification.map_of_stageZero_heq A (H.absorbingHistory_stage_zero n)
    (H.absorbingHistory_initialMetric_zero n)

def absorbingTower {g : P.Metric} (H : RetainedCoreHistory P)
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (A : InitialIdentification P g H.toHistory) : RetainedCoreObservationTower P g where
  history := H.absorbingHistory
  horizon_eq := H.absorbingHistory_horizon
  initial := H.absorbingInitial A
  successor n := H.absorbingHistory_successor n _ rfl
  initial_successor n :=
    (heq_of_eq (InitialIdentification.restrict_map (H.absorbingInitial A (n + 1)) _)).trans
      ((H.absorbingInitial_map_heq A (n + 1)).trans (H.absorbingInitial_map_heq A n).symm)

theorem towerExtinct_of_absorbingTower {g : P.Metric} (H : RetainedCoreHistory P)
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (A : InitialIdentification P g H.toHistory) :
    towerExtinct (H.absorbingTower A).toObservationTower := by
  apply (ObservationTower.towerExtinct_iff_exists_extinct_level
    (H.absorbingTower A).toObservationTower).mpr
  let n : ℕ := Nat.ceil H.horizon + 1
  have hn : H.horizon ≤ (n : ℝ) := by
    dsimp [n]
    exact (Nat.le_ceil H.horizon).trans (by
      exact_mod_cast Nat.le_succ (Nat.ceil H.horizon))
  have hnpos : 0 < n := by
    dsimp [n]
    exact Nat.succ_pos _
  refine ⟨n, hnpos, ?_⟩
  apply (ObservedHistory.isExtinctAtHorizon_iff_of_samePresentation
    ((H.absorbingTower A).toObservationTower.observe_eq_history n)).mpr
  change (H.absorbingHistory n).toHistory.IsExtinctAtHorizon
  rw [H.absorbingHistory_eq_emptyExtension n hn]
  change IsEmpty (H.stage (Fin.last H.eventCount)).Carrier
  exact inferInstance

end RetainedCoreHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

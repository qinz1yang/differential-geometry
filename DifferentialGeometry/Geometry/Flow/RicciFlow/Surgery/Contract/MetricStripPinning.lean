import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.ReducedLengthRealization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.MetricStepSatisfiability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem stageMetric_eq_closedPrefixAt {H : ObservedHistory.{u}} (t : Icc (0 : ℝ) H.horizon)
    (h : H.time (H.activeStage t) < t.1) :
    H.stageMetric (H.activeStage t) = (H.closedPrefixAt t h).flow.base.metric := by
  funext τ
  exact (H.closedPrefixAt_metric t h τ).symm

theorem stageMetric_castSucc_eq_flow {H : ObservedHistory.{u}} (i : Fin H.eventCount) :
    H.stageMetric i.castSucc = (H.event i).incoming.flow.base.metric := by
  funext t
  simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]

def IsTowerAdmissiblePath {H : ObservedHistory.{u}} (p : (H.stage 0).Carrier) (τ : ℝ)
    (γ : ℝ → (H.stage 0).Carrier) : Prop :=
  ContinuousOn γ (Icc (0 : ℝ) τ) ∧ γ 0 = p

theorem isTowerAdmissiblePath_const {H : ObservedHistory.{u}} (p : (H.stage 0).Carrier)
    (τ : ℝ) : IsTowerAdmissiblePath p τ (fun _ => p) :=
  ⟨continuousOn_const, rfl⟩

def IsTowerPinnedStrip {H : ObservedHistory.{u}} (S : VariationalStrip H) : Prop :=
  S.metricAt = H.stageMetric 0 ∧
    S.admissible = IsTowerAdmissiblePath S.pole (S.finish - S.start)

theorem hasAdmissibleCurve_of_admissible_eq {H : ObservedHistory.{u}}
    {S : VariationalStrip H} {A : (ℝ → (H.stage 0).Carrier) → Prop} (h : S.admissible = A)
    (hA : A (fun _ => S.pole)) : HasAdmissibleCurve S :=
  ⟨fun _ => S.pole, by
    rw [h]
    exact hA⟩

theorem hasAdmissibleCurve_of_admissible_eq_tower {H : ObservedHistory.{u}}
    {S : VariationalStrip H} (h : S.admissible = IsTowerAdmissiblePath S.pole (S.finish - S.start)) :
    HasAdmissibleCurve S :=
  hasAdmissibleCurve_of_admissible_eq h (isTowerAdmissiblePath_const S.pole (S.finish - S.start))

theorem hasAdmissibleCurve_of_isTowerPinnedStrip {H : ObservedHistory.{u}}
    {S : VariationalStrip H} (h : IsTowerPinnedStrip S) : HasAdmissibleCurve S :=
  hasAdmissibleCurve_of_admissible_eq_tower h.2

theorem hasAdmissibleCurve_congr {H : ObservedHistory.{u}} {S T : VariationalStrip H}
    (h : S.admissible = T.admissible) : HasAdmissibleCurve S ↔ HasAdmissibleCurve T := by
  rw [HasAdmissibleCurve, HasAdmissibleCurve, h]

noncomputable def towerVariationalStrip (H : ObservedHistory.{u}) (hpos : 0 < H.horizon)
    (p : (H.stage 0).Carrier) : VariationalStrip H where
  pole := p
  start := 0
  finish := H.horizon
  start_nonneg := le_rfl
  finish_le_horizon := le_rfl
  start_lt_finish := hpos
  radius := 1
  radius_pos := one_pos
  metricAt := H.stageMetric 0
  admissible := IsTowerAdmissiblePath p (H.horizon - 0)
  regular := fun _ => False
  regular_admissible := fun _ h => h.elim

theorem isTowerPinnedStrip_towerVariationalStrip (H : ObservedHistory.{u}) (hpos : 0 < H.horizon)
    (p : (H.stage 0).Carrier) : IsTowerPinnedStrip (towerVariationalStrip H hpos p) :=
  ⟨rfl, rfl⟩

theorem nonempty_isTowerPinnedStrip (H : ObservedHistory.{u}) (hpos : 0 < H.horizon)
    (p : (H.stage 0).Carrier) : ∃ S : VariationalStrip H, IsTowerPinnedStrip S :=
  ⟨towerVariationalStrip H hpos p, isTowerPinnedStrip_towerVariationalStrip H hpos p⟩

theorem hasAdmissibleCurve_towerVariationalStrip (H : ObservedHistory.{u}) (hpos : 0 < H.horizon)
    (p : (H.stage 0).Carrier) : HasAdmissibleCurve (towerVariationalStrip H hpos p) :=
  hasAdmissibleCurve_of_isTowerPinnedStrip (isTowerPinnedStrip_towerVariationalStrip H hpos p)

theorem not_isTowerPinnedStrip_emptyVariationalStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) :
    ¬ IsTowerPinnedStrip (emptyVariationalStrip H hpos p) :=
  fun h => not_hasAdmissibleCurve_emptyVariationalStrip H hpos p
    (hasAdmissibleCurve_of_isTowerPinnedStrip h)

theorem exists_isTowerPinnedStrip_of_hasNonemptyPositiveHorizonHistory
    (h : HasNonemptyPositiveHorizonHistory.{u}) :
    ∃ (H : ObservedHistory.{u}) (S : VariationalStrip H),
      0 < H.horizon ∧ IsTowerPinnedStrip S ∧ HasAdmissibleCurve S := by
  obtain ⟨H, hpos, ⟨p⟩⟩ := h
  exact ⟨H, towerVariationalStrip H hpos p, hpos, isTowerPinnedStrip_towerVariationalStrip H hpos p,
    hasAdmissibleCurve_towerVariationalStrip H hpos p⟩

def reducedActionValueSet {H : ObservedHistory.{u}} (S : VariationalStrip H) (u : ℝ)
    (x : (H.stage 0).Carrier) : Set ℝ :=
  {r : ℝ | ∃ γ : ℝ → (H.stage 0).Carrier,
    S.admissible γ ∧ γ 0 = S.pole ∧ γ (S.finish - u) = x ∧
      reducedAction S.metricAt S.finish (S.finish - u) γ = r}

theorem reducedLength_eq_sInf_reducedActionValueSet {H : ObservedHistory.{u}}
    (S : VariationalStrip H) (u : ℝ) (x : (H.stage 0).Carrier) :
    S.reducedLength u x = sInf (reducedActionValueSet S u x) := rfl

theorem reducedActionValueSet_nonempty_of_admissible {H : ObservedHistory.{u}}
    {S : VariationalStrip H} {u : ℝ} {x : (H.stage 0).Carrier} (γ : ℝ → (H.stage 0).Carrier)
    (hγ : S.admissible γ) (h0 : γ 0 = S.pole) (hτ : γ (S.finish - u) = x) :
    (reducedActionValueSet S u x).Nonempty :=
  ⟨reducedAction S.metricAt S.finish (S.finish - u) γ, γ, hγ, h0, hτ, rfl⟩

theorem reducedActionValueSet_eq_empty_of_not_hasAdmissibleCurve {H : ObservedHistory.{u}}
    {S : VariationalStrip H} (h : ¬ HasAdmissibleCurve S) (u : ℝ) (x : (H.stage 0).Carrier) :
    reducedActionValueSet S u x = ∅ := by
  ext r
  constructor
  · rintro ⟨γ, hγ, -⟩
    exact h ⟨γ, hγ⟩
  · intro hr
    exact absurd hr (Set.notMem_empty r)

theorem reducedActionValueSet_emptyVariationalStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) (u : ℝ) :
    reducedActionValueSet (emptyVariationalStrip H hpos p) u p = ∅ :=
  reducedActionValueSet_eq_empty_of_not_hasAdmissibleCurve
    (not_hasAdmissibleCurve_emptyVariationalStrip H hpos p) u p

theorem reducedActionValueSet_towerVariationalStrip_nonempty (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) (u : ℝ) :
    (reducedActionValueSet (towerVariationalStrip H hpos p) u p).Nonempty :=
  reducedActionValueSet_nonempty_of_admissible (S := towerVariationalStrip H hpos p) (u := u)
    (x := p) (fun _ => p)
    (by
      rw [(isTowerPinnedStrip_towerVariationalStrip H hpos p).2]
      exact isTowerAdmissiblePath_const p (H.horizon - 0))
    rfl rfl

theorem reducedLength_le_reducedAction_of_bddBelow {H : ObservedHistory.{u}}
    (S : VariationalStrip H) (u : ℝ) (x : (H.stage 0).Carrier) (γ : ℝ → (H.stage 0).Carrier)
    (hγ : S.admissible γ) (h0 : γ 0 = S.pole) (hτ : γ (S.finish - u) = x)
    (hb : BddBelow (reducedActionValueSet S u x)) :
    S.reducedLength u x ≤ reducedAction S.metricAt S.finish (S.finish - u) γ :=
  csInf_le hb ⟨γ, hγ, h0, hτ, rfl⟩

def isPinnedReducedLengthRealizationInput : Prop :=
  ∀ (H : ObservedHistory.{u}) (S : VariationalStrip H),
    IsTowerPinnedStrip S → IsReducedLengthRealization S

def isPinnedReducedLengthRealizationOnAdmissibleStripsInput : Prop :=
  ∀ (H : ObservedHistory.{u}) (S : VariationalStrip H),
    IsTowerPinnedStrip S → HasAdmissibleCurve S → IsReducedLengthRealization S

theorem isPinnedReducedLengthRealizationOnAdmissibleStripsInput_of_input
    (h : isPinnedReducedLengthRealizationInput.{u}) :
    isPinnedReducedLengthRealizationOnAdmissibleStripsInput.{u} :=
  fun H S hS _ => h H S hS

theorem isPinnedReducedLengthRealizationInput_of_onAdmissibleStrips
    (h : isPinnedReducedLengthRealizationOnAdmissibleStripsInput.{u}) :
    isPinnedReducedLengthRealizationInput.{u} :=
  fun H S hS => h H S hS (hasAdmissibleCurve_of_isTowerPinnedStrip hS)

theorem isPinnedReducedLengthRealizationInput_iff_onAdmissibleStrips :
    isPinnedReducedLengthRealizationInput.{u} ↔
      isPinnedReducedLengthRealizationOnAdmissibleStripsInput.{u} :=
  ⟨isPinnedReducedLengthRealizationOnAdmissibleStripsInput_of_input,
    isPinnedReducedLengthRealizationInput_of_onAdmissibleStrips⟩

theorem isPinnedReducedLengthRealizationOnAdmissibleStripsInput_of_isReducedLengthRealizationInput
    (h : isReducedLengthRealizationInput.{u}) :
    isPinnedReducedLengthRealizationOnAdmissibleStripsInput.{u} :=
  fun H S _ hγ => h H S hγ

theorem isPinnedReducedLengthRealizationOnAdmissibleStripsInput_of_isCommonLocalRealizationOnAdmissibleStrips
    (h : isCommonLocalRealizationOnAdmissibleStrips.{u}) :
    isPinnedReducedLengthRealizationOnAdmissibleStripsInput.{u} :=
  isPinnedReducedLengthRealizationOnAdmissibleStripsInput_of_isReducedLengthRealizationInput
    (isReducedLengthRealizationInput_of_isCommonLocalRealizationOnAdmissibleStrips h)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

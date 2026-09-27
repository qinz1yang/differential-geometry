import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.MetricStep
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Assembly

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem isCommonLocalRealization_iff_components :
    isCommonLocalRealization.{u} ↔
      (isLocalStabilityInput ∧ isBufferedControlInput.{u} ∧ isSurgeryVariationalInput.{u} ∧
        isJacobianInput.{u} ∧ (∃ d : OldData, isOldTubeInput.{u} d) ∧
        isEnlargementInput.{u} ∧ isRoundDegreeInput.{u}) :=
  Iff.rfl

theorem isLocalStabilityInput_of_isCommonLocalRealization
    (h : isCommonLocalRealization.{u}) : isLocalStabilityInput :=
  h.1

theorem isBufferedControlInput_of_isCommonLocalRealization
    (h : isCommonLocalRealization.{u}) : isBufferedControlInput.{u} :=
  h.2.1

theorem isSurgeryVariationalInput_of_isCommonLocalRealization
    (h : isCommonLocalRealization.{u}) : isSurgeryVariationalInput.{u} :=
  h.2.2.1

theorem isJacobianInput_of_isCommonLocalRealization
    (h : isCommonLocalRealization.{u}) : isJacobianInput.{u} :=
  h.2.2.2.1

theorem exists_isOldTubeInput_of_isCommonLocalRealization
    (h : isCommonLocalRealization.{u}) : ∃ d : OldData, isOldTubeInput.{u} d :=
  h.2.2.2.2.1

theorem isEnlargementInput_of_isCommonLocalRealization
    (h : isCommonLocalRealization.{u}) : isEnlargementInput.{u} :=
  h.2.2.2.2.2.1

theorem isRoundDegreeInput_of_isCommonLocalRealization
    (h : isCommonLocalRealization.{u}) : isRoundDegreeInput.{u} :=
  h.2.2.2.2.2.2

theorem isCommonLocalRealization_of_components
    (hstability : isLocalStabilityInput) (hbuffered : isBufferedControlInput.{u})
    (hvariational : isSurgeryVariationalInput.{u}) (hjacobian : isJacobianInput.{u})
    (htube : ∃ d : OldData, isOldTubeInput.{u} d) (henlargement : isEnlargementInput.{u})
    (hround : isRoundDegreeInput.{u}) : isCommonLocalRealization.{u} :=
  ⟨hstability, hbuffered, hvariational, hjacobian, htube, henlargement, hround⟩

theorem nonempty_oldData : Nonempty OldData :=
  ⟨{ horizon := 1, horizon_pos := one_pos
     initialParameter := 1, initialParameter_pos := one_pos
     epsilon := 1, epsilon_pos := one_pos
     comparisonConstant := 1, comparisonConstant_pos := one_pos
     volumeConstant := 1, volumeConstant_pos := one_pos
     scaleLower := 1, scaleLower_pos := one_pos
     noncollapsing := 1, noncollapsing_pos := one_pos
     olderLength := 1, olderLength_pos := one_pos
     energyBound := 1, olderLength_le_energy := le_rfl }⟩

theorem nonempty_capClass : Nonempty CapClass :=
  ⟨{ horizon := 1, horizon_pos := one_pos
     initialParameter := 1, initialParameter_pos := one_pos
     epsilon := 1, epsilon_pos := one_pos
     comparisonConstant := 1, comparisonConstant_pos := one_pos
     volumeConstant := 1, volumeConstant_pos := one_pos
     scaleLower := 1, scaleLower_pos := one_pos
     scaleUpper := 2, scale_lt := one_lt_two }⟩

def emptyVariationalStrip (H : ObservedHistory.{u}) (hpos : 0 < H.horizon)
    (p : (H.stage 0).Carrier) : VariationalStrip H where
  pole := p
  start := 0
  finish := H.horizon
  start_nonneg := le_rfl
  finish_le_horizon := le_rfl
  start_lt_finish := hpos
  radius := 1
  radius_pos := one_pos
  metricAt := fun _ => H.initialMetric 0
  admissible := fun _ => False
  regular := fun _ => False
  regular_admissible := fun _ h => h

theorem emptyVariationalStrip_reducedLength (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) (u : ℝ)
    (x : (H.stage 0).Carrier) :
    (emptyVariationalStrip H hpos p).reducedLength u x = 0 := by
  simp [emptyVariationalStrip, VariationalStrip.reducedLength, reducedLength]

theorem not_exists_emptyVariationalStrip_admissible (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) :
    ¬ ∃ γ : ℝ → (H.stage 0).Carrier, (emptyVariationalStrip H hpos p).admissible γ := by
  rintro ⟨γ, hγ⟩
  exact hγ

theorem forall_isLeast_emptyVariationalStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) (u : ℝ)
    (x : (H.stage 0).Carrier) :
    IsLeast (range fun y => (emptyVariationalStrip H hpos p).reducedLength u y)
      ((emptyVariationalStrip H hpos p).reducedLength u x) := by
  refine ⟨⟨x, rfl⟩, ?_⟩
  rintro _ ⟨z, rfl⟩
  simp [emptyVariationalStrip_reducedLength H hpos p u]

theorem not_exists_reachable_emptyVariationalStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) (u : ℝ)
    (x : (H.stage 0).Carrier) :
    ¬ ∃ γ : ℝ → (H.stage 0).Carrier,
      (emptyVariationalStrip H hpos p).admissible γ ∧ γ 0 = (emptyVariationalStrip H hpos p).pole ∧
        γ ((emptyVariationalStrip H hpos p).finish - u) = x := by
  rintro ⟨γ, hγ, -⟩
  exact hγ

theorem not_attainmentClause_emptyVariationalStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) (u : ℝ) :
    ¬ (∀ x : (H.stage 0).Carrier,
        IsLeast (range fun y => (emptyVariationalStrip H hpos p).reducedLength u y)
          ((emptyVariationalStrip H hpos p).reducedLength u x) →
          ∃ γ : ℝ → (H.stage 0).Carrier,
            (emptyVariationalStrip H hpos p).admissible γ ∧
              γ 0 = (emptyVariationalStrip H hpos p).pole ∧
              γ ((emptyVariationalStrip H hpos p).finish - u) = x ∧
              reducedAction (emptyVariationalStrip H hpos p).metricAt
                  (emptyVariationalStrip H hpos p).finish
                  ((emptyVariationalStrip H hpos p).finish - u) γ =
                (emptyVariationalStrip H hpos p).reducedLength u x) := by
  intro h
  obtain ⟨γ, hγ, -⟩ := h p (forall_isLeast_emptyVariationalStrip H hpos p u p)
  exact hγ

theorem not_isSurgeryVariationalInput_of_positiveHorizon (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) :
    ¬ isSurgeryVariationalInput.{u} := by
  intro h
  let S := emptyVariationalStrip H hpos p
  let u : ℝ := H.horizon / 2
  have hu : u ∈ Ioo (0 : ℝ) H.horizon := ⟨half_pos hpos, half_lt_self hpos⟩
  obtain ⟨-, -, hattain⟩ := (h H S).1 u hu
  exact not_attainmentClause_emptyVariationalStrip H hpos p u hattain

theorem not_isCommonLocalRealization_of_positiveHorizon (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) :
    ¬ isCommonLocalRealization.{u} :=
  fun h => not_isSurgeryVariationalInput_of_positiveHorizon H hpos p
    (isSurgeryVariationalInput_of_isCommonLocalRealization h)

structure UnguardedPoincareExtinctionContracts (DiscardedCutOpen : Type u → Prop)
    extends PoincareExtinctionContracts DiscardedCutOpen where
  metricStep_unguarded : isCommonLocalRealization.{u}

theorem nonempty_unguardedPoincareExtinctionContracts_of_isCommonLocalRealization
    {DiscardedCutOpen : Type u → Prop} (c : PoincareExtinctionContracts DiscardedCutOpen)
    (hm : isCommonLocalRealization.{u}) :
    Nonempty (UnguardedPoincareExtinctionContracts DiscardedCutOpen) :=
  ⟨{ toPoincareExtinctionContracts := c, metricStep_unguarded := hm }⟩

theorem not_nonempty_unguardedPoincareExtinctionContracts_of_positiveHorizon
    (DiscardedCutOpen : Type u → Prop) (H : ObservedHistory.{u}) (hpos : 0 < H.horizon)
    (p : (H.stage 0).Carrier) :
    ¬ Nonempty (UnguardedPoincareExtinctionContracts DiscardedCutOpen) := by
  rintro ⟨c⟩
  exact not_isCommonLocalRealization_of_positiveHorizon H hpos p c.metricStep_unguarded

def HasNonemptyPositiveHorizonHistory : Prop :=
  ∃ H : ObservedHistory.{u}, 0 < H.horizon ∧ Nonempty (H.stage 0).Carrier

theorem not_isCommonLocalRealization_of_hasNonemptyPositiveHorizonHistory
    (h : HasNonemptyPositiveHorizonHistory.{u}) : ¬ isCommonLocalRealization.{u} := by
  obtain ⟨H, hpos, ⟨p⟩⟩ := h
  exact not_isCommonLocalRealization_of_positiveHorizon H hpos p

theorem isReducedLengthAttainment_emptyVariationalStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) (u : ℝ) :
    IsReducedLengthAttainment (emptyVariationalStrip H hpos p) u := by
  intro x _ hreach
  obtain ⟨γ, hγ, -⟩ := hreach
  simp [emptyVariationalStrip] at hγ

theorem not_hasAdmissibleCurve_emptyVariationalStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) :
    ¬ HasAdmissibleCurve (emptyVariationalStrip H hpos p) :=
  not_exists_emptyVariationalStrip_admissible H hpos p

theorem lowerSemicontinuousOn_emptyVariationalStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) (u : ℝ) :
    LowerSemicontinuousOn
      (fun x => (emptyVariationalStrip H hpos p).reducedLength u x)
      (univ : Set (H.stage 0).Carrier) := by
  have hconst : (fun x => (emptyVariationalStrip H hpos p).reducedLength u x) =
      fun _ : (H.stage 0).Carrier => (0 : ℝ) := by
    funext x
    exact emptyVariationalStrip_reducedLength H hpos p u x
  rw [hconst]
  exact lowerSemicontinuousOn_const

theorem isReducedLengthRealization_emptyVariationalStrip_of_hasAdmissibleCurve
    (H : ObservedHistory.{u}) (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier)
    (h : HasAdmissibleCurve (emptyVariationalStrip H hpos p)) :
    IsReducedLengthRealization (emptyVariationalStrip H hpos p) :=
  absurd h (not_hasAdmissibleCurve_emptyVariationalStrip H hpos p)

theorem not_isReducedLengthRealization_emptyVariationalStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) :
    ¬ IsReducedLengthRealization (emptyVariationalStrip H hpos p) :=
  not_isReducedLengthRealization_of_not_hasAdmissibleCurve
    (not_hasAdmissibleCurve_emptyVariationalStrip H hpos p)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

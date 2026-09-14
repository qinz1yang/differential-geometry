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

theorem not_nonempty_poincareExtinctionContracts_of_positiveHorizon
    (DiscardedCutOpen : Type u → Prop) (H : ObservedHistory.{u}) (hpos : 0 < H.horizon)
    (p : (H.stage 0).Carrier) :
    ¬ Nonempty (PoincareExtinctionContracts DiscardedCutOpen) := by
  rintro ⟨c⟩
  exact not_isCommonLocalRealization_of_positiveHorizon H hpos p c.metricStep

def HasNonemptyPositiveHorizonHistory : Prop :=
  ∃ H : ObservedHistory.{u}, 0 < H.horizon ∧ Nonempty (H.stage 0).Carrier

theorem not_isCommonLocalRealization_of_hasNonemptyPositiveHorizonHistory
    (h : HasNonemptyPositiveHorizonHistory.{u}) : ¬ isCommonLocalRealization.{u} := by
  obtain ⟨H, hpos, ⟨p⟩⟩ := h
  exact not_isCommonLocalRealization_of_positiveHorizon H hpos p

def IsReducedLengthAttainment {H : ObservedHistory.{u}} (S : VariationalStrip H)
    (u : ℝ) : Prop :=
  ∀ x : (H.stage 0).Carrier,
    IsLeast (range fun y => S.reducedLength u y) (S.reducedLength u x) →
      (∃ γ : ℝ → (H.stage 0).Carrier,
        S.admissible γ ∧ γ 0 = S.pole ∧ γ (S.finish - u) = x) →
      ∃ γ : ℝ → (H.stage 0).Carrier,
        S.admissible γ ∧ γ 0 = S.pole ∧ γ (S.finish - u) = x ∧
          reducedAction S.metricAt S.finish (S.finish - u) γ = S.reducedLength u x

theorem isReducedLengthAttainment_emptyVariationalStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) (u : ℝ) :
    IsReducedLengthAttainment (emptyVariationalStrip H hpos p) u := by
  intro x _ hreach
  obtain ⟨γ, hγ, -⟩ := hreach
  simp [emptyVariationalStrip] at hγ

def HasAdmissibleCurve {H : ObservedHistory.{u}} (S : VariationalStrip H) : Prop :=
  ∃ γ : ℝ → (H.stage 0).Carrier, S.admissible γ

theorem not_hasAdmissibleCurve_emptyVariationalStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) :
    ¬ HasAdmissibleCurve (emptyVariationalStrip H hpos p) :=
  not_exists_emptyVariationalStrip_admissible H hpos p

def isReducedLengthRealizationInput : Prop :=
  ∀ (H : ObservedHistory.{u}) (S : VariationalStrip H), HasAdmissibleCurve S →
    (∀ u ∈ Ioo S.start S.finish, IsReducedLengthAttainment S u) ∧
    (∀ u ∈ Ioo S.start S.finish,
      LowerSemicontinuousOn (fun x => S.reducedLength u x)
        (univ : Set (H.stage 0).Carrier)) ∧
    (∀ u ∈ Ioo S.start S.finish, ∃ x : (H.stage 0).Carrier,
      IsLeast (range fun y => S.reducedLength u y) (S.reducedLength u x) ∧
        ∃ γ : ℝ → (H.stage 0).Carrier,
          S.admissible γ ∧ γ 0 = S.pole ∧ γ (S.finish - u) = x) ∧
    (∀ u ∈ Ioo S.start S.finish, ∀ x : (H.stage 0).Carrier,
      IsLeast (range fun y => S.reducedLength u y) (S.reducedLength u x) →
      (∀ γ : ℝ → (H.stage 0).Carrier, S.admissible γ → γ 0 = S.pole →
        γ (S.finish - u) = x →
        reducedAction S.metricAt S.finish (S.finish - u) γ = S.reducedLength u x →
        S.regular γ) →
      ∀ η : ℝ, 0 < η →
        ∃ (U : TopologicalSpace.Opens (H.stage 0).Carrier) (hxU : x ∈ U)
          (F : ℝ → ↥U → ℝ) (hF : ∀ σ : ℝ, ContMDiff ThreeModel 𝓘(ℝ, ℝ) ∞ (F σ)),
          F u ⟨x, hxU⟩ = S.reducedLength u x ∧
          (∀ y : ↥U, y ≠ ⟨x, hxU⟩ →
            F u y < S.reducedLength u (y : (H.stage 0).Carrier)) ∧
          deriv (fun σ : ℝ => F σ ⟨x, hxU⟩) u +
            DifferentialGeometry.Geometry.Operator.ΔG (I := ThreeModel) (M := ↥U)
              ((S.metricAt u).restrictOpen U) (⟨F u, hF u⟩ : C^∞⟮ThreeModel, ↥U; ℝ⟯)
              ⟨x, hxU⟩ ≤ 6 + η ∧
          Real.sqrt (DifferentialGeometry.Geometry.Operator.normGradSqFun (I := ThreeModel)
            (M := ↥U) ((S.metricAt u).restrictOpen U) (F u) ⟨x, hxU⟩) ≤ η) ∧
    (∀ u ∈ Ioo S.start S.finish,
      LowerSemicontinuousWithinAt
        (fun τ : ℝ => sInf (range (fun x => S.reducedLength (S.finish - τ) x)) - 6 * τ)
        (Ioo S.start S.finish) (S.finish - u))

theorem isReducedLengthRealizationInput_of_isSurgeryVariationalInput
    (h : isSurgeryVariationalInput.{u}) : isReducedLengthRealizationInput.{u} := by
  intro H S _
  obtain ⟨hfirst, hbarrier, hshift⟩ := h H S
  refine ⟨?_, ?_, ?_, hbarrier, hshift⟩
  · intro u hu x hle _
    exact (hfirst u hu).2.2 x hle
  · intro u hu
    exact (hfirst u hu).1
  · intro u hu
    obtain ⟨x, hx⟩ := (hfirst u hu).2.1
    obtain ⟨γ, hγ, hγ0, hγτ, -⟩ := (hfirst u hu).2.2 x hx
    exact ⟨x, hx, γ, hγ, hγ0, hγτ⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

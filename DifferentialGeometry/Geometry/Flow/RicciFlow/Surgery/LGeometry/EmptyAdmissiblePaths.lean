import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Realization

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry (SmoothRiemannianMetric)

universe u

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

def HasNonemptyPositiveHorizonHistory : Prop :=
  ∃ H : ObservedHistory.{u}, 0 < H.horizon ∧ Nonempty (H.stage 0).Carrier

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

theorem not_isReducedLengthRealization_emptyVariationalStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p : (H.stage 0).Carrier) :
    ¬ IsReducedLengthRealization (emptyVariationalStrip H hpos p) :=
  not_isReducedLengthRealization_of_not_hasAdmissibleCurve
    (not_hasAdmissibleCurve_emptyVariationalStrip H hpos p)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

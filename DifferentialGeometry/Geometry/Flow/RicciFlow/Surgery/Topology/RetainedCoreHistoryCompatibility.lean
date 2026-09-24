import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EmptyHistory

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
namespace RetainedCoreHistory
variable {P : OrientedThreeStage.{u}}

private theorem prefix_restrict_adapter {J K : ObservedHistory.{u}}
    (h : J.IsPrefixOf K) {t : Icc (0 : ℝ) K.horizon} (ht : J.horizon ≤ t.1) :
    J.IsPrefixOf (K.restrict t) := by
  refine ⟨ht, ?_⟩
  have h1 := ObservedHistory.restrict_restrict K t
    ⟨J.horizon, J.horizon_nonneg, ht⟩
  have h2 := h.presentation
  have hs : (⟨J.horizon, J.horizon_nonneg, ht.trans t.2.2⟩ : Icc (0 : ℝ) K.horizon) =
      ⟨J.horizon, J.horizon_nonneg, h.horizon_le⟩ := Subtype.ext rfl
  rw [← hs] at h2
  exact h1.trans h2

private theorem emptyExtension_restrict_adapter
    (H : ObservedHistory.{u}) [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (B : ℝ) (hB : H.horizon ≤ B)
    (t : Icc (0 : ℝ) H.horizon) :
    ((H.emptyExtension B hB).restrict
      ⟨t.1, t.2.1, t.2.2.trans hB⟩).SamePresentation (H.restrict t) := by
  let b : Icc (0 : ℝ) (H.emptyExtension B hB).horizon :=
    ⟨H.horizon, H.horizon_nonneg, hB⟩
  have hp := (H.isPrefixOf_emptyExtension B hB).presentation
  have hs := ObservedHistory.SamePresentation.restrict
    ((H.emptyExtension B hB).restrict b) hp t
  have hr := ObservedHistory.restrict_restrict (H.emptyExtension B hB) b t
  exact hr.symm.trans hs

theorem successor_empty_empty
    (H : RetainedCoreHistory P) [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (n : ℕ) (hn : H.horizon ≤ (n : ℝ))
    (hnext : H.horizon ≤ ((n + 1 : ℕ) : ℝ)) :
    ((H.emptyExtension ((n + 1 : ℕ) : ℝ) hnext).toHistory.restrict
      ⟨(n : ℝ), Nat.cast_nonneg n, by
        change (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
        exact_mod_cast Nat.le_succ n⟩).SamePresentation
      (H.emptyExtension (n : ℝ) hn).toHistory := by
  let E₁ := H.toHistory.emptyExtension ((n + 1 : ℕ) : ℝ) hnext
  have hp : H.toHistory.IsPrefixOf (E₁.restrict
      ⟨(n : ℝ), Nat.cast_nonneg n, by
        change (n : ℝ) ≤ E₁.horizon
        simp only [E₁, ObservedHistory.emptyExtension_horizon]
        exact_mod_cast Nat.le_succ n⟩) :=
    prefix_restrict_adapter
      (ObservedHistory.isPrefixOf_emptyExtension _ _ hnext) (by simpa using hn)
  have hu := ObservedHistory.emptyExtension_unique H.toHistory (n : ℝ) hn
    (E₁.restrict ⟨(n : ℝ), Nat.cast_nonneg n, by
      change (n : ℝ) ≤ E₁.horizon
      simp only [E₁, ObservedHistory.emptyExtension_horizon]
      exact_mod_cast Nat.le_succ n⟩) hp rfl
  simpa only [RetainedCoreHistory.toHistory_emptyExtension] using hu.symm

theorem successor_empty_restrict
    (H : RetainedCoreHistory P) [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (n : ℕ) (hn : ¬ H.horizon ≤ (n : ℝ))
    (hnext : H.horizon ≤ ((n + 1 : ℕ) : ℝ)) :
    ((H.emptyExtension ((n + 1 : ℕ) : ℝ) hnext).toHistory.restrict
      ⟨(n : ℝ), Nat.cast_nonneg n, by
        change (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
        exact_mod_cast Nat.le_succ n⟩).SamePresentation
      (H.restrict ⟨(n : ℝ), Nat.cast_nonneg n, le_of_not_ge hn⟩).toHistory := by
  exact emptyExtension_restrict_adapter H.toHistory ((n + 1 : ℕ) : ℝ) hnext
    ⟨(n : ℝ), Nat.cast_nonneg n, le_of_not_ge hn⟩

theorem successor_restrict_restrict
    (H : RetainedCoreHistory P) [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier]
    (n : ℕ) (hn : ¬ H.horizon ≤ (n : ℝ))
    (hnext : ¬ H.horizon ≤ ((n + 1 : ℕ) : ℝ)) :
    ((H.restrict ⟨((n + 1 : ℕ) : ℝ), Nat.cast_nonneg _, le_of_not_ge hnext⟩).toHistory.restrict
      ⟨(n : ℝ), Nat.cast_nonneg n, by
        change (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
        exact_mod_cast Nat.le_succ n⟩).SamePresentation
      (H.restrict ⟨(n : ℝ), Nat.cast_nonneg n, le_of_not_ge hn⟩).toHistory := by
  let _ : IsEmpty (H.stage (Fin.last H.eventCount)).Carrier := inferInstance
  let t : Icc (0 : ℝ) H.horizon :=
    ⟨((n + 1 : ℕ) : ℝ), Nat.cast_nonneg _, le_of_not_ge hnext⟩
  let s0 : Icc (0 : ℝ) H.horizon :=
    ⟨(n : ℝ), Nat.cast_nonneg _, le_of_not_ge hn⟩
  let s : Icc (0 : ℝ) (H.toHistory.restrict t).horizon :=
    ⟨s0.1, s0.2.1, by
      change (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
      exact_mod_cast Nat.le_succ n⟩
  have hr := ObservedHistory.restrict_restrict H.toHistory t s
  simpa only [RetainedCoreHistory.restrict_toHistory] using hr

end RetainedCoreHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

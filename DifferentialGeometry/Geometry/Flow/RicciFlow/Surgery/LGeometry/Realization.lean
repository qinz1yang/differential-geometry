import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.VariationalStrip

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def IsReducedLengthAttainment {H : ObservedHistory.{u}} (S : VariationalStrip H)
    (u : ℝ) : Prop :=
  ∀ x : (H.stage 0).Carrier,
    IsLeast (range fun y => S.reducedLength u y) (S.reducedLength u x) →
      (∃ γ : ℝ → (H.stage 0).Carrier,
        S.admissible γ ∧ γ 0 = S.pole ∧ γ (S.finish - u) = x) →
      ∃ γ : ℝ → (H.stage 0).Carrier,
        S.admissible γ ∧ γ 0 = S.pole ∧ γ (S.finish - u) = x ∧
          reducedAction S.metricAt S.finish (S.finish - u) γ = S.reducedLength u x

def HasAdmissibleCurve {H : ObservedHistory.{u}} (S : VariationalStrip H) : Prop :=
  ∃ γ : ℝ → (H.stage 0).Carrier, S.admissible γ

def IsReducedLengthRealization {H : ObservedHistory.{u}} (S : VariationalStrip H) : Prop :=
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

theorem not_isReducedLengthRealization_of_not_hasAdmissibleCurve {H : ObservedHistory.{u}}
    {S : VariationalStrip H} (h : ¬ HasAdmissibleCurve S) : ¬ IsReducedLengthRealization S := by
  intro hreal
  obtain ⟨-, -, hleast, -⟩ := hreal
  obtain ⟨x, -, γ, hγ, -, -⟩ :=
    hleast ((S.start + S.finish) / 2) (by constructor <;> linarith [S.start_lt_finish])
  exact h ⟨γ, hγ⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

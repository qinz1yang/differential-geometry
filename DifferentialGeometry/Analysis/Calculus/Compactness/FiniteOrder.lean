import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import DifferentialGeometry.Analysis.Calculus.Compactness.FiniteOrderProof

set_option autoImplicit false
noncomputable section
open Filter Topology
namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem exists_bilinear_form_limit_subsequence_of_bounded_derivatives
    (K : ℕ) (hK : 1 ≤ K) {U : Set E} (hU : IsOpen U)
    (g : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ i, ContDiffOn ℝ (K : WithTop ℕ∞) (g i) U)
    (hjets : ∀ q : ℕ, q ≤ K → ∀ S : Set E, IsCompact S → S ⊆ U →
      ∃ C : ℝ, ∀ᶠ i in atTop, ∀ x ∈ S, ‖iteratedFDeriv ℝ q (g i) x‖ ≤ C)
    (lower upper : ℝ) (hlower : 0 < lower)
    (hsymm : ∀ i x, x ∈ U → ∀ v w, g i x v w = g i x w v)
    (helliptic : ∀ i x, x ∈ U → ∀ v,
      lower * ‖v‖ ^ 2 ≤ g i x v v ∧ g i x v v ≤ upper * ‖v‖ ^ 2) :
    ∃ (φ : ℕ → ℕ) (gLimit : E → E →L[ℝ] E →L[ℝ] ℝ),
      StrictMono φ ∧ ContDiffOn ℝ ((K - 1 : ℕ) : WithTop ℕ∞) gLimit U ∧
      (∀ S : Set E, IsCompact S → S ⊆ U →
        MapCPConvergenceOn S (K - 1) (fun i => g (φ i)) gLimit) ∧
      (∀ x ∈ U, ∀ v w, gLimit x v w = gLimit x w v) ∧
      (∀ x ∈ U, ∀ v,
        lower * ‖v‖ ^ 2 ≤ gLimit x v v ∧ gLimit x v v ≤ upper * ‖v‖ ^ 2) := by
  exact exists_bilinear_form_limit_subsequence_of_bounded_derivatives_proved K hK hU g hg hjets
    lower upper hlower hsymm helliptic

end DifferentialGeometry.CheegerGromovCompactness

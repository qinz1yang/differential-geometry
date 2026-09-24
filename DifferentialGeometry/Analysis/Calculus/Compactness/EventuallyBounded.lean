import DifferentialGeometry.Analysis.Calculus.Compactness.BilinearForm
import DifferentialGeometry.Analysis.Calculus.MapConvergence.DerivativeBounds

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter Topology

section MapArzelaAscoli

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_cInf_subseq_on_of_eventually_bdd
    {U : Set E} (hU : IsOpen U) (Φ : ℕ → E → F)
    (hΦ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Φ k) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ M : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) Φinf U ∧
        MapCInfConvergenceOnCompacts U (fun k => Φ (φ k)) Φinf :=
  exists_cInf_subseq_on hU Φ hΦ (exists_iteratedFDeriv_bound_of_eventually_bounded hU hΦ hbdd)

end MapArzelaAscoli

section BilinearFormArzelaAscoli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_smooth_bilinear_form_limit_subsequence_on_of_eventually_bdd
    {U : Set E} (hU : IsOpen U)
    (g : ℕ → E → (E →L[ℝ] E →L[ℝ] ℝ))
    (hg : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (g k) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (g k) x‖ ≤ C)
    (a b : ℝ)
    (hab : ∀ k : ℕ, ∀ z ∈ U, ∀ v : E,
      a * ‖v‖ ^ 2 ≤ g k z v v ∧ g k z v v ≤ b * ‖v‖ ^ 2) :
    ∃ (φ : ℕ → ℕ) (gInf : E → (E →L[ℝ] E →L[ℝ] ℝ)),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) gInf U ∧
        MapCInfConvergenceOnCompacts U (fun k => g (φ k)) gInf ∧
        ∀ z ∈ U, ∀ v : E,
          a * ‖v‖ ^ 2 ≤ gInf z v v ∧ gInf z v v ≤ b * ‖v‖ ^ 2 :=
  exists_smooth_bilinear_form_limit_subsequence_on hU g hg
    (exists_iteratedFDeriv_bound_of_eventually_bounded hU hg hbdd) a b hab

end BilinearFormArzelaAscoli

end CheegerGromovCompactness
end DifferentialGeometry

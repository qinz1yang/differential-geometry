import DifferentialGeometry.Analysis.Calculus.Compactness.SmoothMap

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_smooth_bilinear_form_limit_subsequence_on
    {U : Set E} (hU : IsOpen U)
    (g : ℕ → E → (E →L[ℝ] E →L[ℝ] ℝ))
    (hg : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (g k) U)
    (hbdd : ∀ r : ℕ, ∀ K : Set E, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (g k) x‖ ≤ C)
    (a b : ℝ)
    (hab : ∀ k : ℕ, ∀ z ∈ U, ∀ v : E,
      a * ‖v‖ ^ 2 ≤ g k z v v ∧ g k z v v ≤ b * ‖v‖ ^ 2) :
    ∃ (φ : ℕ → ℕ) (gInf : E → (E →L[ℝ] E →L[ℝ] ℝ)),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) gInf U ∧
        MapCInfConvergenceOnCompacts U (fun k => g (φ k)) gInf ∧
        ∀ z ∈ U, ∀ v : E,
          a * ‖v‖ ^ 2 ≤ gInf z v v ∧ gInf z v v ≤ b * ‖v‖ ^ 2 := by
  obtain ⟨φ, gInf, hφ, hsmooth, hconv⟩ := exists_cInf_subseq_on hU g hg hbdd
  refine ⟨φ, gInf, hφ, hsmooth, hconv, fun z hz v => ?_⟩
  have htend : Tendsto (fun k => g (φ k) z) atTop (𝓝 (gInf z)) :=
    tendsto_of_cInf hconv hz
  have hcont : Continuous (fun c : E →L[ℝ] E →L[ℝ] ℝ => c v v) := by
    fun_prop
  have htendv : Tendsto (fun k => g (φ k) z v v) atTop (𝓝 (gInf z v v)) :=
    (hcont.tendsto (gInf z)).comp htend
  exact ⟨
    ge_of_tendsto htendv
      (Filter.Eventually.of_forall fun k => (hab (φ k) z hz v).1),
    le_of_tendsto htendv
      (Filter.Eventually.of_forall fun k => (hab (φ k) z hz v).2)⟩

end CheegerGromovCompactness
end DifferentialGeometry

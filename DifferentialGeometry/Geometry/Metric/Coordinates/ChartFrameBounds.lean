import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open Bundle Set
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_pos_bound_chartBasisVec_on_compact
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {K : Set M} (hK : IsCompact K)
    (hchart : K ⊆ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ K, ∀ i : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner x (chartBasisVecFiber (I := I) x₀ i x)
        (chartBasisVecFiber (I := I) x₀ i x)) ≤ R := by
  classical
  have hbound (i : Fin (Module.finrank ℝ E)) : ∃ C : ℝ, ∀ x ∈ K,
      Real.sqrt (chartGramMatrix g x₀ x i i) ≤ C := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (((chartGramMatrix_entry_contMDiffOn g x₀ i i).continuousOn.mono hchart).sqrt)
    exact ⟨C, fun x hx => by simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hC x hx⟩
  choose C hC using hbound
  refine ⟨1 + ∑ i, max (C i) 0, by positivity, fun x hx i => ?_⟩
  calc
    _ ≤ C i := hC i x hx
    _ ≤ max (C i) 0 := le_max_left _ _
    _ ≤ ∑ j, max (C j) 0 :=
      Finset.single_le_sum (fun j _ => le_max_right (C j) 0) (Finset.mem_univ i)
    _ ≤ _ := by linarith

end DifferentialGeometry.Tensor.Coordinates

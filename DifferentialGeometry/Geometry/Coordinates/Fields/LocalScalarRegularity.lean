import DifferentialGeometry.Geometry.Coordinates.Fields.Scalar


noncomputable section

open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} [IsManifold I n M]

theorem scalarOnE_contDiffOn_of_contMDiffOn
    (x₀ : M) {f : M → ℝ} {U : Set M}
    (hf : ContMDiffOn I 𝓘(ℝ) n f U) :
    ContDiffOn ℝ n (scalarOnE (I := I) x₀ f)
      ((extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' U) := by
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I n (extChartAt I x₀).symm
      ((extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' U) :=
    (contMDiffOn_extChartAt_symm (I := I) x₀).mono inter_subset_left
  exact (hf.comp hsymm (fun _ hy => hy.2)).contDiffOn

theorem scalarOnE_contDiffAt_of_contMDiffOn
    [I.Boundaryless] (x₀ : M) {f : M → ℝ} {U : Set M} {y : E}
    (hf : ContMDiffOn I 𝓘(ℝ) n f U) (hU : IsOpen U)
    (hy : y ∈ (extChartAt I x₀).target)
    (hyU : (extChartAt I x₀).symm y ∈ U) :
    ContDiffAt ℝ n (scalarOnE (I := I) x₀ f) y := by
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I n (extChartAt I x₀).symm y :=
    (contMDiffOn_extChartAt_symm (I := I) x₀).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  exact ((hf.contMDiffAt (hU.mem_nhds hyU)).comp y hsymm).contDiffAt

end DifferentialGeometry.Tensor.Coordinates

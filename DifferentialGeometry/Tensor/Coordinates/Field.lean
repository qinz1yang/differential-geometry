import DifferentialGeometry.Geometry.Coordinates.Frame.Chart
import DifferentialGeometry.Geometry.Coordinates.Frame.Coordinate
import DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation

set_option autoImplicit false
noncomputable section
open Bundle Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem tensor_field_chart_components_contDiffOn {r : ℕ}
    (A : Tensor0SField (I := I) (M := M) (n := ∞) r) (p : M)
    {W : Set E} (hWt : W ⊆ (extChartAt I p).target)
    (slots : Fin r → CoordinateIdx (𝕜 := ℝ) E) :
    ContDiffOn ℝ ∞ (fun y => A ((extChartAt I p).symm y)
      (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm y))) W := by
  apply contMDiffOn_iff_contDiffOn.mp
  intro y hy
  let e := trivializationAt E (TangentSpace I : M → Type _) p
  have hx : (extChartAt I p).symm y ∈ e.baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have hs := (extChartAt I p).map_target (hWt hy)
    rwa [extChartAt_source_eq_chartAt_source] at hs
  have ha := TensorMultilinear.contMDiffAt_section_apply (I := I)
    (T := fun x => A x) (A.contMDiff ((extChartAt I p).symm y))
    (v := fun j x => chartBasisVecFiber (I := I) p (slots j) x)
    (fun j => (chartBasisVec_contMDiffOn (I := I) p (slots j) _ hx).contMDiffAt
      (e.open_baseSet.mem_nhds hx))
  exact ha.comp_contMDiffWithinAt y ((contMDiffOn_extChartAt_symm p).mono hWt y hy)

end DifferentialGeometry.Tensor.Coordinates

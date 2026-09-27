import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

noncomputable section

set_option autoImplicit false

namespace DifferentialGeometry

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

theorem extChartAt_prod (x : M) (y : N) :
    extChartAt (I.prod J) (x, y) = (extChartAt I x).prod (extChartAt J y) := by
  refine PartialEquiv.ext (fun z => ?_) (fun z => ?_) ?_
  · simp only [extChartAt_coe, Function.comp_apply, prodChartedSpace_chartAt,
      modelWithCorners_prod_coe]
    rw [OpenPartialHomeomorph.prod_apply]
    rfl
  · rw [extChartAt_coe_symm (I := I.prod J) (x := (x, y)), PartialEquiv.prod_coe_symm]
    simp only [Function.comp_apply, prodChartedSpace_chartAt, modelWithCorners_prod_coe_symm,
      extChartAt_coe_symm]
    rw [OpenPartialHomeomorph.prod_symm_apply]
    rfl
  · simp only [extChartAt_source, prodChartedSpace_chartAt, PartialEquiv.prod_source,
      OpenPartialHomeomorph.prod_source]

end DifferentialGeometry

import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Function Manifold TopologicalSpace
open scoped ContDiff Topology
namespace DifferentialGeometry.Manifold


theorem contMDiffOn_of_contMDiff_open_restrict
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    (U : Opens M) (f : M → N)
    (hf : ContMDiff I J ∞ (fun q : U => f q.val)) :
    ContMDiffOn I J ∞ f U := by
  intro x hx
  let e := openSubtypePartialDiffeomorph I U ⟨⟨x, hx⟩⟩
  have ht : x ∈ e.target := by rw [openSubtypePartialDiffeomorph_target]; exact hx
  have hi := e.symm.contMDiffOn.contMDiffAt (e.open_target.mem_nhds ht)
  have hh := hf.contMDiffAt.comp x hi
  apply ContMDiffAt.contMDiffWithinAt
  apply hh.congr_of_eventuallyEq
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  change f y = f (e.symm y).val
  rw [show e.symm y = ⟨y, hy⟩ from openSubtypePartialDiffeomorph_symm_apply I U ⟨⟨x, hx⟩⟩ hy]

end DifferentialGeometry.Manifold

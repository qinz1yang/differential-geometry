import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false
noncomputable section
open IsManifold
open Set Function Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E H S T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] [Nonempty H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace S] [ChartedSpace H S] [IsManifold I ∞ S]
variable [TopologicalSpace T] [ChartedSpace H T]

theorem isLocalDiffeomorph_of_lifted_charts (F : S → T)
    (hF : _root_.Topology.IsOpenEmbedding F)
    (hcharts : ∀ x : S, (chartAt H x).lift_openEmbedding hF ∈ maximalAtlas I ∞ T) :
    IsLocalDiffeomorph I I ∞ F := by
  intro x
  let c := chartAt H x
  let d := c.lift_openEmbedding hF
  let e := c.trans d.symm
  have hc : ContMDiffOn I I ∞ c c.source := contMDiffOn_chart
  have hc' : ContMDiffOn I I ∞ c.symm c.target := contMDiffOn_chart_symm
  have hd : ContMDiffOn I I ∞ d d.source := contMDiffOn_of_mem_maximalAtlas (hcharts x)
  have hd' : ContMDiffOn I I ∞ d.symm d.target := contMDiffOn_symm_of_mem_maximalAtlas (hcharts x)
  let D : PartialDiffeomorph I I S T ∞ :=
    { e with
      contMDiffOn_toFun := hd'.comp' hc
      contMDiffOn_invFun := hc'.comp' hd }
  refine ⟨D, ⟨mem_chart_source H x, ?_⟩, ?_⟩
  · exact c.map_source (mem_chart_source H x)
  · intro y hy
    change F y = F (c.symm (c y))
    rw [c.left_inv hy.1]
end DifferentialGeometry.Topology.Manifold

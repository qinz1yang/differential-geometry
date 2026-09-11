import DifferentialGeometry.Topology.Manifold.InteriorChart

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
namespace DifferentialGeometry.Manifold
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H) {n : ℕ∞ω} [IsManifold I n M]

theorem contDiffAt_comp_extChartAt_symm_of_isInteriorPoint {f : M → F}
    (hf : ContMDiff I 𝓘(𝕜, F) n f) {x : M} (hx : I.IsInteriorPoint x) :
    ContDiffAt 𝕜 n (fun y => f ((extChartAt I x).symm y)) (extChartAt I x x) := by
  let c := interiorChart I n x
  have hxc : x ∈ c.source := (mem_interiorChart_source_iff I n x).mpr hx
  exact ((hf.comp_contMDiffOn c.symm.contMDiffOn).contMDiffAt
    (c.open_target.mem_nhds (c.map_source hxc))).contDiffAt

end DifferentialGeometry.Manifold

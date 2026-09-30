import DifferentialGeometry.Topology.ThreeManifold.TorusCut.TorusCylinder

set_option autoImplicit false
namespace GC.Topology
open DifferentialGeometry.Topology

theorem torusAt_injective_iff
    {M : Type*} [TopologicalSpace M]
    {c : C(GC.Topology.TorusCylinder, M)} (r s : ℝ) {x : GC.Topology.Torus} :
    Function.Injective (FundamentalGroup.map (c.comp (GC.Topology.torusAt r)) x) ↔
      Function.Injective (FundamentalGroup.map (c.comp (GC.Topology.torusAt s)) x) := by
  apply GC.Topology.homotopic_injective_iff
  exact (ContinuousMap.Homotopy.refl c).comp (GC.Topology.torusSlide r s)

end GC.Topology

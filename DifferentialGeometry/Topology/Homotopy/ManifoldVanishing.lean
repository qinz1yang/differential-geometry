import DifferentialGeometry.Topology.Homology.ManifoldHomologyVanishing
import DifferentialGeometry.Topology.Homology.HurewiczTwo
import DifferentialGeometry.Topology.Homotopy.Homeomorph
import DifferentialGeometry.Topology.Manifold.ChartedSpaceHomeomorph
import DifferentialGeometry.Topology.Manifold.Small
import Mathlib.Topology.Instances.Shrink

noncomputable section

open scoped Manifold

universe u

namespace DifferentialGeometry.Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M] [SimplyConnectedSpace M]

theorem homotopyGroup_two_subsingleton_of_simplyConnected_of_finrank_eq_three
    (hE : Module.finrank ℝ E = 3) (q : M) : Subsingleton (HomotopyGroup (Fin 2) M q) := by
  let _ : Small.{0} M := ChartedSpace.small_of_compactSpace E M
  let N := Shrink.{0} M
  let e : M ≃ₜ N := Shrink.homeomorph M
  let _ : ChartedSpace E N := e.chartedSpace
  let _ : IsManifold 𝓘(ℝ, E) 1 N :=
    DifferentialGeometry.Manifold.isManifold_homeomorphChartedSpace e
  let _ : CompactSpace N := e.compactSpace
  let _ : T2Space N := e.t2Space
  let _ : SimplyConnectedSpace N := e.symm.toHomotopyEquiv.simplyConnectedSpace
  let _ : Subsingleton (integralSingularHomology 2 N) :=
    integralSingularHomology_two_subsingleton_of_simplyConnected_of_finrank_eq_three
      (E := E) (X := N) hE
  let _ : Subsingleton (HomotopyGroup (Fin 2) N (e q)) :=
    (injective_sphereHurewicz_triangleSphereFundamentalClass (e q)).subsingleton
  exact (homotopyGroupHomeomorphMulEquiv (N := Fin 2) e q).injective.subsingleton

end DifferentialGeometry.Topology

end

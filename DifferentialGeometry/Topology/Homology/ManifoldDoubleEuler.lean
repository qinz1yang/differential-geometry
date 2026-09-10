import DifferentialGeometry.Topology.Homology.DoubleEuler
import DifferentialGeometry.Topology.Homology.ManifoldBoundary
import DifferentialGeometry.Topology.Homology.Manifold
import DifferentialGeometry.Topology.Manifold.Boundary.DefiningCollar
import DifferentialGeometry.Topology.Double.SeamNeighborhood

set_option autoImplicit false
noncomputable section
open Set Function Topology
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
namespace Poincare.Homology
open Poincare.Topology

theorem finiteHomologyType_and_eulerChar_intrinsicDouble
    {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [CompactSpace M]
    (K : Type) [Field K] :
    finiteHomologyType K (TopCat.of (Double ((𝓡∂ (n + 1)).boundary M))) ∧
      eulerChar K (TopCat.of (Double ((𝓡∂ (n + 1)).boundary M))) =
        2 * eulerChar K (TopCat.of M) - eulerChar K (TopCat.of ((𝓡∂ (n + 1)).boundary M)) := by
  obtain ⟨r, _, hrn, hrzero, a, ha, c, hc, _, _, hheight, hsmall, _⟩ :=
    Poincare.Manifold.Boundary.exists_definingFunction_sublevel_collar (n := n) (M := M)
  let B := (𝓡∂ (n + 1)).boundary M
  have hr (b : B) : r b.val = 0 := (hrzero b.val).mpr b.property
  have hz (x : M) (hx : r x = 0) : x ∈ B := (hrzero x).mp hx
  have hsub (x : M) (hx : r x ≤ a) : x ∈ range c := hsmall.symm ▸ hx
  let s := doubleSeamHomeomorph B r hr hz hrn c hheight hsub hc.isEmbedding
  exact finiteHomologyType_and_eulerChar_double_of_collar B r hr hrn hz ha s
    (doubleHeight_seamHomeomorph B r hr hz hrn c hheight hsub hc.isEmbedding) K
    (finiteHomologyType_of_compact_manifold_withBoundary (n := n + 1) (M := M) K)
    (finiteHomologyType_intrinsicBoundary (𝓡∂ (n + 1)) K)

end Poincare.Homology

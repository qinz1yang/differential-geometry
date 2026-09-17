import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceFilling
import DifferentialGeometry.Topology.Connected.CompactRegion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isCombinatorialManifoldWithBoundary_of_regularClosed_of_frontier_eq
    (L R : Geometry.SimplicialComplex ℝ E) [Finite L.faces] [Finite R.faces]
    (hL : IsCombinatorialManifold 2 L) (hdim : Module.finrank ℝ E = 3)
    (hconn : IsConnected L.space) (hreg : closure (interior R.space) = R.space)
    (hfront : frontier R.space = L.space) : IsCombinatorialManifoldWithBoundary 3 R := by
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
  obtain ⟨B, hBfin, hB, -, hBfront, hBreg, hBint, hBext⟩ :=
    hL.exists_isCombinatorialManifoldWithBoundary_boundaryComplex L hdim hconn
  let _ : Finite B.faces := hBfin.to_subtype
  have hne : R.space.Nonempty := hconn.nonempty.mono
    (hfront.symm.subset.trans (isPolyhedron_space R).isClosed.frontier_subset)
  have heq : R.space = B.space := Topology.eq_of_isCompact_of_frontier_eq
    (isPolyhedron_space R).isCompact (isPolyhedron_space B).isCompact hreg hBreg
    hBint.isPreconnected hBext.isPreconnected hne (hfront.trans hBfront.symm)
  have hid : IsPLHomeomorphOn (id : E → E) B.space R.space := by
    rw [heq]
    exact (isPolyhedron_space B).isPLHomeomorphOn_id
  exact hB.of_isPLHomeomorphOn hid

open Classical in
theorem isCombinatorialManifoldWithBoundary_of_isPLSphere_frontier
    (R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hdim : Module.finrank ℝ E = 3) (hreg : closure (interior R.space) = R.space)
    (hS : IsPLSphere 2 (frontier R.space)) : IsCombinatorialManifoldWithBoundary 3 R := by
  obtain ⟨L, hLfin, hLspace⟩ := hS.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLSphere 2 L.space := hLspace.symm ▸ hS
  exact isCombinatorialManifoldWithBoundary_of_regularClosed_of_frontier_eq L R
    hL.isCombinatorialManifold hdim hL.isConnected hreg hLspace.symm

end DifferentialGeometry.Topology.PiecewiseLinear

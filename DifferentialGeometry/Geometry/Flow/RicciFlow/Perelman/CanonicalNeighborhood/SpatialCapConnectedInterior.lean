import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialFiniteCapFrontier
import DifferentialGeometry.Topology.Connected.InteriorUnion
import DifferentialGeometry.Topology.Manifold.SphereBoundaryDomain

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}

theorem isConnected_interior_of_compact_regular_neck_boundary
    (nk : SpatialNeck g eps p) {level : ℝ} (hlevel : |level| ≤ 4)
    {K : Set M} (hK : IsCompact K) (hKr : closure (interior K) = K)
    (hfront : frontier K = range (fun z : Sphere 2 => nk.map (z, level))) :
    IsConnected (interior K) := by
  have hnonempty : (interior K).Nonempty := by
    by_contra h
    have hi : interior K = ∅ := not_nonempty_iff_eq_empty.mp h
    have hKe : K = ∅ := by simpa only [hi, closure_empty] using hKr.symm
    have hf := hfront.symm ▸ (mem_range_self nk.center :
      nk.map (nk.center, level) ∈ range (fun z : Sphere 2 => nk.map (z, level)))
    simp only [hKe, frontier_empty, notMem_empty] at hf
  have he := nk.isSmoothEmbedding_level (hlevel.trans_lt
    ((lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small])))
  exact (DifferentialGeometry.Topology.Manifold.isConnected_interior_and_compl_of_sphere_boundary
    hK.isClosed hnonempty _ he hfront).1

theorem isConnected_interior_union_of_neck_cap_filling
    (nk : SpatialNeck g eps p) {level : ℝ} (hlevel : |level| ≤ 4)
    {W K : Set M} (hW : closure (interior W) = W)
    (hconn : IsPreconnected (interior W)) (hK : IsCompact K)
    (hKr : closure (interior K) = K)
    (hfront : frontier K = range (fun z : Sphere 2 => nk.map (z, level)))
    (hinter : K ∩ W = range (fun z : Sphere 2 => nk.map (z, level)))
    (hfill : range (fun z : Sphere 2 => nk.map (z, level)) ⊆ interior (W ∪ K)) :
    IsConnected (interior (W ∪ K)) := by
  have hkc := isConnected_interior_of_compact_regular_neck_boundary nk hlevel hK hKr hfront
  have hx : nk.map (nk.center, level) ∈ range (fun z : Sphere 2 => nk.map (z, level)) :=
    mem_range_self _
  have hxm := hinter.symm ▸ hx
  exact DifferentialGeometry.Topology.isConnected_interior_union
    (S := W) (T := K) hW.symm.subset hKr.symm.subset hconn hkc.isPreconnected
    ⟨_, ⟨hW.symm ▸ hxm.2, hKr.symm ▸ hxm.1⟩, hfill hx⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

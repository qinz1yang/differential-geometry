import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapSlabCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapExterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds
import DifferentialGeometry.Topology.Manifold.SphereBoundaryDomain

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M] [NoncompactSpace M]
  [SigmaCompactSpace M] {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps epsc C1 C2 t : ℝ} {p y : M}

theorem CanonicalWitness.scalar_le_mul_scalar_of_cap_on_spatial_neck_frontier
    (witness : CanonicalWitness S epsc C1 C2 y t)
    (nk : SpatialNeck (S.base.metric t) eps p) (heps : eps ≤ 1 / 8646)
    (q : Sphere 2) {level : ℝ} (hlevel : |level| ≤ 4) (hy : nk.map (q, level) = y)
    (cap : LocalCap S epsc y t witness.domain.carrier)
    (hdepth : ∀ z ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t y) ≤ metricDistance (S.base.metric t) y z)
    {W : Set M} (hcompact : IsCompact W)
    (hfront : frontier W ⊆ range (fun z : Sphere 2 => nk.map (z, level)))
    (anchor : M) (hanchor : anchor ∈ W) :
    S.scalar t y ≤ C2 * S.scalar t anchor := by
  have hinside : frontier W ⊆ interior witness.domain.carrier := by
    intro z hz
    obtain ⟨v, rfl⟩ := hfront hz
    exact cap.core_inside (interior_subset
      (nk.image_slab_subset_cap_core_of_center_in_slab heps q hlevel hy cap hdepth
        ⟨(v, level), ⟨mem_univ _, abs_le.mp hlevel⟩, rfl⟩))
  have hWU : W ⊆ witness.domain.carrier := by
    rcases DifferentialGeometry.Topology.Manifold.subset_or_union_eq_univ_of_frontier_subset_interior
      hcompact.isClosed cap.isConnected_interior_and_compl.2.isPreconnected hinside with hsub | hfull
    · exact hsub
    · exact (noncompact_univ (X := M)
        (hfull ▸ hcompact.union witness.domain.compact)).elim
  have ha : anchor ∈ witness.domain.carrier := hWU hanchor
  have hC2 : 0 < C2 := zero_lt_one.trans_le witness.one_le_comparison_constant
  have hbound := mul_le_mul_of_nonneg_left (witness.scalar_bounds anchor ha).1 hC2.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hC2.ne', one_mul] using hbound

theorem CanonicalWitness.alternative_eq_neck_of_mul_scalar_lt_on_spatial_neck_frontier
    (witness : CanonicalWitness S epsc C1 C2 y t)
    (nk : SpatialNeck (S.base.metric t) eps p) (heps : eps ≤ 1 / 8646)
    (q : Sphere 2) {level : ℝ} (hlevel : |level| ≤ 4) (hy : nk.map (q, level) = y)
    {W : Set M} (hcompact : IsCompact W)
    (hfront : frontier W ⊆ range (fun z : Sphere 2 => nk.map (z, level)))
    (anchor : M) (hanchor : anchor ∈ W) (hscalar : C2 * S.scalar t anchor < S.scalar t y) :
    ∃ neck : LocalNeck S epsc y t witness.domain.carrier,
      witness.alternative = CanonicalAlternative.neck neck := by
  have hcomponent : anchor ∈ connectedComponent y := by
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    exact mem_univ _
  rcases witness.alternative_eq_neck_or_cap_of_mul_scalar_lt hcomponent hscalar with
    hneck | ⟨cap, hdepth, _⟩
  · exact hneck
  · exact (hscalar.not_ge (witness.scalar_le_mul_scalar_of_cap_on_spatial_neck_frontier
      nk heps q hlevel hy cap hdepth hcompact hfront anchor hanchor)).elim

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

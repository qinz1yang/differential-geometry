import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapSlabCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapExterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds
import DifferentialGeometry.Topology.Manifold.SphereBoundaryDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCapFrontierFilling
import DifferentialGeometry.Topology.Connected.Frontier

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

section

omit [NoncompactSpace M]

private theorem isCompact_closure_of_incident_compact_filling
    {X : Type*} [TopologicalSpace X] [T2Space X] {W K C : Set X}
    (hK : IsCompact K) (hC : IsPreconnected C) (hCW : C ⊆ Wᶜ)
    (hfront : frontier K ⊆ W)
    (hmeet : (closure C ∩ interior (W ∪ K)).Nonempty) : IsCompact (closure C) := by
  obtain ⟨x, hxC, hxU⟩ := hmeet
  obtain ⟨z, hzU, hzC⟩ := mem_closure_iff.mp hxC _ isOpen_interior hxU
  have hzK : z ∈ K := (interior_subset hzU).resolve_left (hCW hzC)
  have havoid : Disjoint C (frontier K) := disjoint_left.mpr
    (fun y hyC hyK => hCW hyC (hfront hyK))
  have hzint : z ∈ interior K := by
    by_contra h
    exact disjoint_left.mp havoid hzC ⟨subset_closure hzK, h⟩
  have hsub := DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
    hC havoid ⟨z, hzC, hzint⟩
  exact hK.of_isClosed_subset isClosed_closure
    ((closure_mono (hsub.trans interior_subset)).trans_eq hK.isClosed.closure_eq)

theorem CanonicalWitness.isCompact_closure_component_compl_of_cap_on_finite_spatial_neck_frontier
    {ι : Type*} (alive : Finset ι) (point : ι → M)
    (neck : ∀ i, SpatialNeck (S.base.metric t) eps (point i)) (level : ι → ℝ)
    (hlevel : ∀ i ∈ alive, |level i| ≤ 4)
    (hdisjoint : (alive : Set ι).Pairwise (fun i j =>
      Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i)))
        (range (fun q : Sphere 2 => (neck j).map (q, level j)))))
    (heps : eps ≤ 1 / 8646) (i : ι) (hi : i ∈ alive) (q : Sphere 2)
    (hy : (neck i).map (q, level i) = y)
    (witness : CanonicalWitness S epsc C1 C2 y t)
    {W : Set M} (hcompact : IsCompact W) (hW : closure (interior W) = W)
    (hconn : IsPreconnected (interior W))
    (hfront : frontier W = ⋃ j ∈ alive, range (fun z : Sphere 2 => (neck j).map (z, level j)))
    (anchor : M) (hanchor : anchor ∈ W) (hscalar : C2 * S.scalar t anchor < S.scalar t y)
    (cap : LocalCap S epsc y t witness.domain.carrier)
    (hdepth : ∀ z ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t y) ≤ metricDistance (S.base.metric t) y z)
    (x : M) (hincident : (closure (connectedComponentIn Wᶜ x) ∩
      range (fun z : Sphere 2 => (neck i).map (z, level i))).Nonempty) :
    IsCompact (closure (connectedComponentIn Wᶜ x)) := by
  obtain ⟨K, hK, _, _, hKfront, _, _, _, _, _, hfill⟩ :=
    exists_connected_cap_filling_on_finite_spatial_neck_frontier_of_mul_scalar_lt
      alive point neck level hlevel hdisjoint heps i hi q hy witness cap hdepth
      hcompact hW hconn hfront anchor hanchor hscalar
  apply isCompact_closure_of_incident_compact_filling hK isPreconnected_connectedComponentIn
    (connectedComponentIn_subset Wᶜ x)
  · intro z hz
    exact hcompact.isClosed.frontier_subset (hfront.symm ▸
      mem_iUnion₂.mpr ⟨i, hi, hKfront ▸ hz⟩)
  · exact hincident.mono (inter_subset_inter_right _ hfill)

theorem CanonicalWitness.alternative_eq_neck_of_noncompact_incident_component
    {ι : Type*} (alive : Finset ι) (point : ι → M)
    (neck : ∀ i, SpatialNeck (S.base.metric t) eps (point i)) (level : ι → ℝ)
    (hlevel : ∀ i ∈ alive, |level i| ≤ 4)
    (hdisjoint : (alive : Set ι).Pairwise (fun i j =>
      Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i)))
        (range (fun q : Sphere 2 => (neck j).map (q, level j)))))
    (heps : eps ≤ 1 / 8646) (i : ι) (hi : i ∈ alive) (q : Sphere 2)
    (hy : (neck i).map (q, level i) = y)
    (witness : CanonicalWitness S epsc C1 C2 y t)
    {W : Set M} (hcompact : IsCompact W) (hW : closure (interior W) = W)
    (hconn : IsPreconnected (interior W))
    (hfront : frontier W = ⋃ j ∈ alive, range (fun z : Sphere 2 => (neck j).map (z, level j)))
    (anchor : M) (hanchor : anchor ∈ W) (hscalar : C2 * S.scalar t anchor < S.scalar t y)
    (x : M) (hnotcompact : ¬ IsCompact (closure (connectedComponentIn Wᶜ x)))
    (hincident : (closure (connectedComponentIn Wᶜ x) ∩
      range (fun z : Sphere 2 => (neck i).map (z, level i))).Nonempty) :
    ∃ localNeck : LocalNeck S epsc y t witness.domain.carrier,
      witness.alternative = CanonicalAlternative.neck localNeck := by
  have hcomponent : anchor ∈ connectedComponent y := by
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    exact mem_univ _
  rcases witness.alternative_eq_neck_or_cap_of_mul_scalar_lt hcomponent hscalar with
    hn | ⟨cap, hdepth, _⟩
  · exact hn
  · exact (hnotcompact (witness.isCompact_closure_component_compl_of_cap_on_finite_spatial_neck_frontier
      alive point neck level hlevel hdisjoint heps i hi q hy
      hcompact hW hconn hfront anchor hanchor hscalar cap hdepth x hincident)).elim


end

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

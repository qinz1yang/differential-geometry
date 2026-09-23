import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCapConnectedInterior

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps epsc t : ℝ} {y : M} {U : Set M}

theorem exists_connected_cap_move_on_finite_spatial_neck_frontier_of_sphere_subset
    {g : SmoothRiemannianMetric I3 M} {ι : Type*} (alive : Finset ι) (point : ι → M)
    (neck : ∀ i, SpatialNeck g eps (point i)) (level : ι → ℝ)
    (hlevel : ∀ i ∈ alive, |level i| ≤ 4)
    (hdisjoint : (alive : Set ι).Pairwise (fun i j =>
      Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i)))
        (range (fun q : Sphere 2 => (neck j).map (q, level j)))))
    (i : ι) (hi : i ∈ alive) (cap : CapCore U)
    (hinside : range (fun z : Sphere 2 => (neck i).map (z, level i)) ⊆ interior U)
    {W : Set M} (hcompact : IsCompact W) (hW : closure (interior W) = W)
    (hconn : IsPreconnected (interior W))
    (hfront : frontier W = ⋃ j ∈ alive, range (fun z : Sphere 2 => (neck j).map (z, level j))) :
    ∃ (V K : Set M) (next : Finset ι),
      IsCompact V ∧ IsConnected (interior V) ∧ closure (interior V) = V ∧ W ⊆ V ∧
      IsCompact K ∧ closure (interior K) = K ∧ K ⊆ interior U ∧
      frontier K = range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
      frontier V = ⋃ j ∈ next, range (fun z : Sphere 2 => (neck j).map (z, level j)) ∧
      next ⊆ alive ∧ next.card ≤ alive.card ∧
      (1 < alive.card → next.card < alive.card) ∧
      ((V = K ∧ next = {i}) ∨
        (V = W ∪ K ∧ (next : Set ι) = (alive : Set ι) \ {i} ∧
          K ∩ W = range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
          range (fun z : Sphere 2 => (neck i).map (z, level i)) ⊆ interior V ∧
          next.card < alive.card)) := by
  obtain ⟨V, K, next, hV, hVr, hWV, hK, hKr, hKin, hKf, hVf, hnext, hle, hlt, hcases⟩ :=
    exists_cap_move_on_finite_spatial_neck_frontier_of_sphere_subset alive point neck level
      hlevel hdisjoint i hi cap hinside hcompact hW hconn hfront
  have hVc : IsConnected (interior V) := by
    rcases hcases with ⟨rfl, _⟩ | ⟨rfl, _, hinter, hfill, _⟩
    · exact isConnected_interior_of_compact_regular_neck_boundary (neck i) (hlevel i hi) hK hKr hKf
    · exact isConnected_interior_union_of_neck_cap_filling (neck i) (hlevel i hi) hW hconn
        hK hKr hKf hinter hfill
  exact ⟨V, K, next, hV, hVc, hVr, hWV, hK, hKr, hKin, hKf, hVf, hnext, hle, hlt, hcases⟩

theorem exists_connected_cap_move_on_finite_spatial_neck_frontier
    {ι : Type*} (alive : Finset ι) (point : ι → M)
    (neck : ∀ i, SpatialNeck (S.base.metric t) eps (point i)) (level : ι → ℝ)
    (hlevel : ∀ i ∈ alive, |level i| ≤ 4)
    (hdisjoint : (alive : Set ι).Pairwise (fun i j =>
      Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i)))
        (range (fun q : Sphere 2 => (neck j).map (q, level j)))))
    (heps : eps ≤ 1 / 8646) (i : ι) (hi : i ∈ alive) (q : Sphere 2)
    (hy : (neck i).map (q, level i) = y)
    (cap : LocalCap S epsc y t U)
    (hdepth : ∀ z ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t y) ≤ metricDistance (S.base.metric t) y z)
    {W : Set M} (hcompact : IsCompact W) (hW : closure (interior W) = W)
    (hconn : IsPreconnected (interior W))
    (hfront : frontier W = ⋃ j ∈ alive, range (fun z : Sphere 2 => (neck j).map (z, level j))) :
    ∃ (V K : Set M) (next : Finset ι),
      IsCompact V ∧ IsConnected (interior V) ∧ closure (interior V) = V ∧ W ⊆ V ∧
      IsCompact K ∧ closure (interior K) = K ∧ K ⊆ interior cap.core.carrier ∧
      frontier K = range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
      frontier V = ⋃ j ∈ next, range (fun z : Sphere 2 => (neck j).map (z, level j)) ∧
      next ⊆ alive ∧ next.card ≤ alive.card ∧
      (1 < alive.card → next.card < alive.card) ∧
      ((V = K ∧ next = {i}) ∨
        (V = W ∪ K ∧ (next : Set ι) = (alive : Set ι) \ {i} ∧
          K ∩ W = range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
          range (fun z : Sphere 2 => (neck i).map (z, level i)) ⊆ interior V ∧
          next.card < alive.card)) := by
  exact exists_connected_cap_move_on_finite_spatial_neck_frontier_of_sphere_subset alive point neck level
    hlevel hdisjoint i hi cap.core_model
    (by
      rintro z ⟨v, rfl⟩
      exact (neck i).image_slab_subset_cap_core_of_center_in_slab heps q (hlevel i hi) hy cap hdepth
        ⟨(v, level i), ⟨mem_univ _, abs_le.mp (hlevel i hi)⟩, rfl⟩)
    hcompact hW hconn hfront

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

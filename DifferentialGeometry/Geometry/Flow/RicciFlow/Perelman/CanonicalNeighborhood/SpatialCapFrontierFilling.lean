import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialConnectedCapFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M]

private theorem exists_connected_cap_filling_on_finite_spatial_neck_frontier_of_not_subset
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {ι : Type*}
    (alive : Finset ι) (point : ι → M) (neck : ∀ i, SpatialNeck g eps (point i))
    (level : ι → ℝ) (hlevel : ∀ i ∈ alive, |level i| ≤ 4)
    (hdisjoint : (alive : Set ι).Pairwise (fun i j =>
      Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i)))
        (range (fun q : Sphere 2 => (neck j).map (q, level j)))))
    (i : ι) (hi : i ∈ alive) {U : Set M} (cap : CapCore U)
    (hinside : range (fun z : Sphere 2 => (neck i).map (z, level i)) ⊆ interior U)
    {W : Set M} (hcompact : IsCompact W) (hW : closure (interior W) = W)
    (hconn : IsPreconnected (interior W))
    (hfront : frontier W = ⋃ j ∈ alive, range (fun z : Sphere 2 => (neck j).map (z, level j)))
    (hnot : ¬ W ⊆ interior U) :
    ∃ K : Set M, IsCompact K ∧ closure (interior K) = K ∧ K ⊆ interior U ∧
      frontier K = range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
      K ∩ W = range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
      IsCompact (W ∪ K) ∧ IsConnected (interior (W ∪ K)) ∧
      closure (interior (W ∪ K)) = W ∪ K ∧
      frontier (W ∪ K) = ⋃ j ∈ alive, ⋃ (_ : j ≠ i),
        range (fun z : Sphere 2 => (neck j).map (z, level j)) ∧
      range (fun z : Sphere 2 => (neck i).map (z, level i)) ⊆ interior (W ∪ K) := by
  obtain ⟨V, K, next, hV, hVc, hVr, hWV, hK, hKr, hKin, hKf,
    hVf, _, _, _, hcases⟩ :=
    exists_connected_cap_move_on_finite_spatial_neck_frontier_of_sphere_subset
      alive point neck level hlevel hdisjoint i hi cap hinside hcompact hW hconn hfront
  rcases hcases with ⟨hVK, _⟩ | ⟨rfl, hnext, hinter, hfill, _⟩
  · exact (hnot ((hVK ▸ hWV).trans hKin)).elim
  · refine ⟨K, hK, hKr, hKin, hKf, hinter, hV, hVc, hVr, ?_, hfill⟩
    rw [hVf]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨j, hj, hx⟩
      have hj' : j ∈ (alive : Set ι) \ {i} := hnext ▸ hj
      exact ⟨j, hj'.1, hj'.2, hx⟩
    · rintro ⟨j, hj, hji, hx⟩
      have hj' : j ∈ (next : Set ι) := hnext.symm ▸ (show j ∈ (alive : Set ι) \ {i} from
        ⟨hj, hji⟩)
      exact ⟨j, hj', hx⟩

variable [SigmaCompactSpace M] {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps epsc C1 C2 t : ℝ} {y : M}

theorem exists_connected_cap_filling_on_finite_spatial_neck_frontier_of_mul_scalar_lt
    {ι : Type*} (alive : Finset ι) (point : ι → M)
    (neck : ∀ i, SpatialNeck (S.base.metric t) eps (point i)) (level : ι → ℝ)
    (hlevel : ∀ i ∈ alive, |level i| ≤ 4)
    (hdisjoint : (alive : Set ι).Pairwise (fun i j =>
      Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i)))
        (range (fun q : Sphere 2 => (neck j).map (q, level j)))))
    (heps : eps ≤ 1 / 8646) (i : ι) (hi : i ∈ alive) (q : Sphere 2)
    (hy : (neck i).map (q, level i) = y)
    (witness : CanonicalWitness S epsc C1 C2 y t)
    (cap : LocalCap S epsc y t witness.domain.carrier)
    (hdepth : ∀ z ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t y) ≤ metricDistance (S.base.metric t) y z)
    {W : Set M} (hcompact : IsCompact W) (hW : closure (interior W) = W)
    (hconn : IsPreconnected (interior W))
    (hfront : frontier W = ⋃ j ∈ alive, range (fun z : Sphere 2 => (neck j).map (z, level j)))
    (anchor : M) (hanchor : anchor ∈ W) (hscalar : C2 * S.scalar t anchor < S.scalar t y) :
    ∃ K : Set M, IsCompact K ∧ closure (interior K) = K ∧ K ⊆ interior cap.core.carrier ∧
      frontier K = range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
      K ∩ W = range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
      IsCompact (W ∪ K) ∧ IsConnected (interior (W ∪ K)) ∧
      closure (interior (W ∪ K)) = W ∪ K ∧
      frontier (W ∪ K) = ⋃ j ∈ alive, ⋃ (_ : j ≠ i),
        range (fun z : Sphere 2 => (neck j).map (z, level j)) ∧
      range (fun z : Sphere 2 => (neck i).map (z, level i)) ⊆ interior (W ∪ K) := by
  apply exists_connected_cap_filling_on_finite_spatial_neck_frontier_of_not_subset
    alive point neck level hlevel hdisjoint i hi cap.core_model
    (by
      rintro z ⟨v, rfl⟩
      exact (neck i).image_slab_subset_cap_core_of_center_in_slab heps q (hlevel i hi) hy cap hdepth
        ⟨(v, level i), ⟨mem_univ _, abs_le.mp (hlevel i hi)⟩, rfl⟩)
    hcompact hW hconn hfront
  intro hsub
  have ha : anchor ∈ witness.domain.carrier :=
    interior_subset (cap.core_inside (interior_subset (hsub hanchor)))
  have hC2 : 0 < C2 := zero_lt_one.trans_le witness.one_le_comparison_constant
  have hbound := mul_le_mul_of_nonneg_left (witness.scalar_bounds anchor ha).1 hC2.le
  rw [← mul_assoc, mul_inv_cancel₀ hC2.ne', one_mul] at hbound
  exact hscalar.not_ge hbound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

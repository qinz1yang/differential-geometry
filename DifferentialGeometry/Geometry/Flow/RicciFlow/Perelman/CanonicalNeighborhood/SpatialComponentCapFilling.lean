import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCapFrontierFilling
import DifferentialGeometry.Topology.Connected.ComponentFilling
import DifferentialGeometry.Geometry.Neck.SpatialCapFilling

noncomputable section
open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M]

variable [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps epsc C1 C2 t : ℝ} {y : M}

open scoped Classical in
theorem exists_cap_filling_on_finite_spatial_neck_frontier_of_componentwise_mul_scalar_lt
    {ι : Type*} (alive : Finset ι) (point : ι → M)
    (neck : ∀ i, SpatialNeck (S.base.metric t) eps (point i)) (level : ι → ℝ)
    (hlevel : ∀ i ∈ alive, |level i| ≤ 4)
    (hpair : (alive : Set ι).Pairwise (fun i j =>
      Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i)))
        (range (fun q : Sphere 2 => (neck j).map (q, level j)))))
    (heps : eps ≤ 1 / 8646) (i : ι) (hi : i ∈ alive) (q : Sphere 2)
    (hy : (neck i).map (q, level i) = y)
    (witness : CanonicalWitness S epsc C1 C2 y t)
    (cap : LocalCap S epsc y t witness.domain.carrier)
    (hdepth : ∀ z ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t y) ≤ metricDistance (S.base.metric t) y z)
    {W : Set M} (hWcompact : IsCompact W) (hW : closure (interior W) = W)
    (hfront : frontier W = ⋃ j ∈ alive, range (fun z : Sphere 2 => (neck j).map (z, level j)))
    (hanchor : ∀ x ∈ interior W, ∃ a ∈ connectedComponentIn (interior W) x,
      C2 * S.scalar t a < S.scalar t y) :
    ∃ K : Set M, IsCompact K ∧ closure (interior K) = K ∧
      K ⊆ interior cap.core.carrier ∧
      frontier K = range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
      K ∩ W = range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
      IsCompact (W ∪ K) ∧ closure (interior (W ∪ K)) = W ∪ K ∧
      frontier (W ∪ K) = ⋃ j ∈ alive.erase i, range (fun z : Sphere 2 => (neck j).map (z, level j)) ∧
      range (fun z : Sphere 2 => (neck i).map (z, level i)) ⊆ interior (W ∪ K) ∧
      (∀ z ∈ K, C2⁻¹ * S.scalar t y ≤ S.scalar t z ∧ S.scalar t z ≤ C2 * S.scalar t y) ∧
      ∀ z ∈ K, connectedComponentIn (interior W)ᶜ z = K := by
  obtain ⟨K, hK, hKr, hKin, hKf, hinter, hWK, hregular, hnewfront, hfill, hcomponent, _, _⟩ :=
    exists_cap_filling_on_finite_spatial_neck_frontier_of_componentwise_avoidance
      alive point neck level hlevel hpair i hi cap.coreModel
      (by
        rintro z ⟨v, rfl⟩
        exact (neck i).image_slab_subset_cap_core_of_center_in_slab heps q (hlevel i hi) hy cap hdepth
          ⟨(v, level i), ⟨mem_univ _, abs_le.mp (hlevel i hi)⟩, rfl⟩)
      hWcompact hW hfront (by
        intro x hx
        obtain ⟨a, ha, hlt⟩ := hanchor x hx
        refine ⟨a, ha, ?_⟩
        intro haU
        have hC2 : 0 < C2 := zero_lt_one.trans_le witness.one_le_comparison_constant
        have hb := mul_le_mul_of_nonneg_left
          (witness.scalar_bounds a (interior_subset (cap.core_inside (interior_subset haU)))).1 hC2.le
        rw [← mul_assoc, mul_inv_cancel₀ hC2.ne', one_mul] at hb
        exact hlt.not_ge hb)
  refine ⟨K, hK, hKr, hKin, hKf, hinter, hWK, hregular, hnewfront, hfill, ?_, hcomponent⟩
  intro z hz
  exact witness.scalar_bounds z (interior_subset (cap.core_inside (interior_subset (hKin hz))))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

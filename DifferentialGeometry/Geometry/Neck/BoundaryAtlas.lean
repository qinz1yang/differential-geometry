import DifferentialGeometry.Topology.Manifold.FiniteCollarBoundaryAtlas
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Inclusion
import DifferentialGeometry.Geometry.Neck.Spatial

noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem exists_smoothBoundaryAtlas_of_finite_spatial_neck_levels
    {M ι : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [Finite ι]
    (g : SmoothRiemannianMetric I3 M) {eps : ℝ}
    (point : ι → M) (neck : ∀ i, SpatialNeck g eps (point i))
    (level : ι → ℝ) (hlevel : ∀ i, |level i| < eps⁻¹)
    (param : ι → Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
    (hdisjoint : Pairwise (fun i j => Disjoint
      (range (fun q => (neck i).map (param i q, level i)))
      (range (fun q => (neck j).map (param j q, level j)))))
    {K : Set M} (hregular : closure (interior K) = K)
    (hfrontier : frontier K ⊆ ⋃ i, range (fun q => (neck i).map (param i q, level i))) :
    ∃ C : DifferentialGeometry.Topology.SmoothBoundaryAtlas I3 3 K,
      ∀ x : K, C.ambientChart x x.val 0 = 0 ↔ x.val ∈ frontier K := by
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  let e : ι → PartialDiffeomorph IC I3 Cylinder M ∞ := fun i =>
    ((param i).prodCongr (DifferentialGeometry.Topology.translateDiffeomorph (level i)))
      |>.toPartialDiffeomorph.trans (neck i).map
  have heq (i : ι) (q : Sphere 2) (t : ℝ) :
      e i (q, t) = (neck i).map (param i q, t + level i) := rfl
  have hzero (i : ι) (q : Sphere 2) : (q, (0 : ℝ)) ∈ (e i).source := by
    refine ⟨mem_univ _, ?_⟩
    change (param i q, 0 + level i) ∈ (neck i).map.source
    rw [zero_add]
    exact (neck i).domain ⟨mem_univ _, (abs_lt.mp (hlevel i)).1, (abs_lt.mp (hlevel i)).2⟩
  apply DifferentialGeometry.Topology.exists_smoothBoundaryAtlas_of_finite_disjoint_collars
    e hzero
  · simpa only [heq, zero_add] using hdisjoint
  · exact hregular
  · simpa only [heq, zero_add] using hfrontier

theorem exists_isManifold_of_finite_spatial_neck_levels
    {M ι : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [Finite ι]
    (g : SmoothRiemannianMetric I3 M) {eps : ℝ}
    (point : ι → M) (neck : ∀ i, SpatialNeck g eps (point i))
    (level : ι → ℝ) (hlevel : ∀ i, |level i| < eps⁻¹)
    (param : ι → Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
    (hdisjoint : Pairwise (fun i j => Disjoint
      (range (fun q => (neck i).map (param i q, level i)))
      (range (fun q => (neck j).map (param j q, level j)))))
    {K : Set M} (hregular : closure (interior K) = K)
    (hfrontier : frontier K ⊆ ⋃ i, range (fun q => (neck i).map (param i q, level i))) :
    ∃ charts : ChartedSpace (EuclideanHalfSpace 3) K,
      let _ := charts
      IsManifold (𝓡∂ 3) ∞ K ∧
        IsSmoothEmbedding (𝓡∂ 3) I3 ∞ (Subtype.val : K → M) ∧
        Subtype.val '' ((𝓡∂ 3).boundary K) = frontier K ∧
        Subtype.val '' ((𝓡∂ 3).interior K) = interior K := by
  obtain ⟨C, hC⟩ := exists_smoothBoundaryAtlas_of_finite_spatial_neck_levels
    g point neck level hlevel param hdisjoint hregular hfrontier
  refine ⟨C.toChartedSpace, C.isManifold, C.isSmoothEmbedding_subtype_val, ?_,
    C.image_interior_subtype_val hC⟩
  exact C.image_boundary_subtype_val (hregular ▸ isClosed_closure) hC

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

import DifferentialGeometry.Geometry.Neck.BoundaryAtlas
import DifferentialGeometry.Geometry.Neck.SpatialLevelEmbedding
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.ConnectedComponents
import DifferentialGeometry.Topology.Connected.ComponentCollar
import DifferentialGeometry.Geometry.Neck.Spatial

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M} (nk : SpatialNeck g eps p)

theorem SpatialNeck.signed_collar_connectedComponentIn
    {K : Set M} {x : M} {level σ r : ℝ}
    (hsource : ∀ z, ∀ t ∈ Ioo (-r) r, (z, level + σ * t) ∈ nk.map.source)
    (hside : ∀ z, ∀ t ∈ Ioo (-r) r, nk.map (z, level + σ * t) ∈ K ↔ t ≤ 0)
    (hinterior : ∀ z, ∀ t ∈ Ioo (-r) r,
      nk.map (z, level + σ * t) ∈ interior K ↔ t < 0)
    (hzero : ∀ z, nk.map (z, level) ∈ connectedComponentIn K x) :
    (∀ z, ∀ t ∈ Ioo (-r) r,
      nk.map (z, level + σ * t) ∈ connectedComponentIn K x ↔ t ≤ 0) ∧
    ∀ z, ∀ t ∈ Ioo (-r) r,
      nk.map (z, level + σ * t) ∈ interior (connectedComponentIn K x) ↔ t < 0 := by
  let _ : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ThreeSpace M
  apply DifferentialGeometry.Topology.connectedComponentIn_interval_side
    (fun z t => nk.map (z, level + σ * t))
  · intro z
    have hcurve : ContinuousOn (fun t : ℝ => (z, level + σ * t)) (Ioo (-r) r) := by
      exact (continuous_const.prodMk (continuous_const.add
        (continuous_const.mul continuous_id))).continuousOn
    exact nk.map.contMDiffOn_toFun.continuousOn.comp hcurve
      (fun t ht => hsource z t ht)
  · exact hside
  · exact hinterior
  · simpa only [mul_zero, add_zero] using hzero

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem spatial_neck_component_union_meeting
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] {ι : Type*} [Finite ι]
    (g : SmoothRiemannianMetric I3 M) {eps : ℝ} (point : ι → M)
    (neck : ∀ i, SpatialNeck g eps (point i)) (level : ι → ℝ)
    (hlevel : ∀ i, |level i| < eps⁻¹)
    (hdisjoint : Pairwise (fun i j => Disjoint
      (range (fun q : Sphere 2 => (neck i).map (q, level i)))
      (range (fun q : Sphere 2 => (neck j).map (q, level j)))))
    {W L : Set M} (hWcompact : IsCompact W) (hWregular : closure (interior W) = W)
    (hfrontier : frontier W = ⋃ i, range (fun q : Sphere 2 => (neck i).map (q, level i)))
    (hL : L ⊆ interior W) :
    let R := ⋃ y ∈ L, connectedComponentIn W y
    let alive := {i : ι | (range (fun q : Sphere 2 => (neck i).map (q, level i)) ∩ R).Nonempty}
    IsCompact R ∧ R ⊆ W ∧ L ⊆ interior R ∧ closure (interior R) = R ∧
      frontier R = ⋃ i ∈ alive, range (fun q : Sphere 2 => (neck i).map (q, level i)) ∧
      (∀ x ∈ interior R, ∃ a ∈ connectedComponentIn (interior R) x, a ∈ L) ∧
      (∃ atlas : DifferentialGeometry.Topology.SmoothBoundaryAtlas I3 3 R,
        ∀ x : R, atlas.ambientChart x x.val 0 = 0 ↔ x.val ∈ frontier R) ∧
      ∀ i ∈ alive, ∀ (r σ : ℝ),
        (∀ q t, t ∈ Ioo (-r) r → (q, level i + σ * t) ∈ (neck i).map.source) →
        (∀ q t, t ∈ Ioo (-r) r → ((neck i).map (q, level i + σ * t) ∈ W ↔ t ≤ 0)) →
        (∀ q t, t ∈ Ioo (-r) r →
          ((neck i).map (q, level i + σ * t) ∈ interior W ↔ t < 0)) →
        (∀ q t, t ∈ Ioo (-r) r → ((neck i).map (q, level i + σ * t) ∈ R ↔ t ≤ 0)) ∧
        (∀ q t, t ∈ Ioo (-r) r →
          ((neck i).map (q, level i + σ * t) ∈ interior R ↔ t < 0)) := by
  obtain ⟨atlasW, _⟩ := exists_smoothBoundaryAtlas_of_finite_spatial_neck_levels
    g point neck level hlevel (fun _ => Diffeomorph.refl I2 (Sphere 2) ∞)
    (by simpa only [Diffeomorph.coe_refl, id_eq] using hdisjoint) hWregular (by
      simpa only [Diffeomorph.coe_refl, id_eq] using hfrontier.subset)
  let _ := atlasW.toChartedSpace
  let _ := atlasW.isManifold
  let _ : LocallyConnectedSpace W :=
    ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 3) W
  let R := ⋃ y ∈ L, connectedComponentIn W y
  let F (i : ι) := range (fun q : Sphere 2 => (neck i).map (q, level i))
  have hF (i : ι) : IsPreconnected (F i) := by
    let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
        (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
    exact isPreconnected_range ((neck i).isSmoothEmbedding_level (hlevel i)).contMDiff.continuous
  obtain ⟨hRcompact, hRW, hLR, hRregular, hRfrontsub, _⟩ :=
    DifferentialGeometry.Topology.component_union_meeting_compact_regular_closed
      hWcompact hWregular hL
  have hRfront := DifferentialGeometry.Topology.frontier_component_union_meeting_eq_iUnion
    (L := L) hWcompact.isClosed F hF hfrontier
  have hanchor := DifferentialGeometry.Topology.component_union_meeting_interior_anchor hL
    (fun y _ => atlasW.isPreconnected_interior_connectedComponentIn y)
  have hatlas := exists_smoothBoundaryAtlas_of_finite_spatial_neck_levels
    g point neck level hlevel (fun _ => Diffeomorph.refl I2 (Sphere 2) ∞)
    (by simpa only [Diffeomorph.coe_refl, id_eq] using hdisjoint) hRregular (by
      simpa only [Diffeomorph.coe_refl, id_eq] using hRfrontsub.trans hfrontier.subset)
  refine ⟨hRcompact, hRW, hLR, hRregular, hRfront, hanchor, hatlas, ?_⟩
  intro i hi r σ hsource hside hinside
  obtain ⟨z, hzF, hzR⟩ := hi
  obtain ⟨y, hyL, hzy⟩ := mem_iUnion₂.mp hzR
  have hFW : F i ⊆ W := by
    intro w hw
    exact hWcompact.isClosed.frontier_subset (hfrontier.symm ▸ mem_iUnion.mpr ⟨i, hw⟩)
  have hFC : F i ⊆ connectedComponentIn W y := by
    rw [connectedComponentIn_eq hzy]
    exact (hF i).subset_connectedComponentIn hzF hFW
  have hCsub : connectedComponentIn W y ⊆ R := subset_iUnion₂_of_subset y hyL subset_rfl
  obtain ⟨hclosedside, hopenSide⟩ := (neck i).signed_collar_connectedComponentIn
    hsource hside hinside (fun q => hFC (mem_range_self q))
  constructor
  · intro q t ht
    exact ⟨fun h => (hside q t ht).mp (hRW h),
      fun h => hCsub ((hclosedside q t ht).mpr h)⟩
  · intro q t ht
    exact ⟨fun h => (hinside q t ht).mp (interior_mono hRW h),
      fun h => interior_mono hCsub ((hopenSide q t ht).mpr h)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

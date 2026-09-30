import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapSlabCapture
import DifferentialGeometry.Topology.OpenPartialHomeomorph.CapFilling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCoreSphereFilling
import DifferentialGeometry.Geometry.Neck.SpatialLevelEmbedding

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps epsc t : ℝ} {p y : M} {U : Set M}


theorem SpatialNeck.exists_cap_filling_or_containment_of_sphere_subset
    {g : SmoothRiemannianMetric I3 M} (nk : SpatialNeck g eps p)
    {level : ℝ} (hlevel : |level| ≤ 4) (cap : CapCore U)
    (hinside : range (fun z : Sphere 2 => nk.map (z, level)) ⊆ interior U)
    {W R : Set M} (hW : closure (interior W) = W)
    (hconn : IsPreconnected (interior W)) (hR : IsClosed R)
    (hfront : frontier W = range (fun z : Sphere 2 => nk.map (z, level)) ∪ R)
    (hdis : Disjoint (range (fun z : Sphere 2 => nk.map (z, level))) R) :
    ∃ K : Set M, IsCompact K ∧ closure (interior K) = K ∧
      frontier K = range (fun z : Sphere 2 => nk.map (z, level)) ∧
      K ⊆ interior U ∧
      (W ⊆ K ∨ K ∩ W = range (fun z : Sphere 2 => nk.map (z, level)) ∧
        closure (interior (W ∪ K)) = W ∪ K ∧ frontier (W ∪ K) = R ∧
        range (fun z : Sphere 2 => nk.map (z, level)) ⊆ interior (W ∪ K)) := by
  obtain ⟨K, hcompact, hreg, hfrontK, hKin⟩ :=
    cap.exists_compact_side_of_sphere_embedding (fun z : Sphere 2 => nk.map (z, level))
      (nk.isSmoothEmbedding_level (hlevel.trans_lt
        ((lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small])))) hinside
  let A : Cylinder ≃ₜ Cylinder :=
    { toFun := fun z => (z.1, level + z.2)
      invFun := fun z => (z.1, z.2 - level)
      left_inv := by intro z; ext <;> simp
      right_inv := by intro z; ext <;> simp
      continuous_toFun := continuous_fst.prodMk (continuous_const.add continuous_snd)
      continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_const) }
  let T := A.transOpenPartialHomeomorph nk.map.toOpenPartialHomeomorph
  have hzero (z : Sphere 2) : T (z, 0) = nk.map (z, level) := by
    change nk.map (z, level + 0) = _
    rw [add_zero]
  have hsrc (z : Sphere 2) : (z, 0) ∈ T.source := by
    change (z, level + 0) ∈ nk.map.source
    rw [add_zero]
    have hlen : (4 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small])
    exact nk.domain ⟨mem_univ _, by constructor <;>
      linarith [(abs_le.mp hlevel).1, (abs_le.mp hlevel).2]⟩
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) zero_le_one)
  refine ⟨K, hcompact, hreg, hfrontK, hKin, ?_⟩
  simpa only [hzero] using
    DifferentialGeometry.Topology.subset_or_fill_of_shared_cylinder_boundary T hsrc hW hreg
      hconn hR (by simpa only [hzero] using hfront)
      (by simpa only [hzero] using hfrontK) (by simpa only [hzero] using hdis)

theorem SpatialNeck.exists_cap_filling_or_containment
    (nk : SpatialNeck (S.base.metric t) eps p) (heps : eps ≤ 1 / 8646)
    (q : Sphere 2) {level : ℝ} (hlevel : |level| ≤ 4) (hy : nk.map (q, level) = y)
    (cap : LocalCap S epsc y t U)
    (hdepth : ∀ z ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t y) ≤ metricDistance (S.base.metric t) y z)
    {W R : Set M} (hW : closure (interior W) = W)
    (hconn : IsPreconnected (interior W)) (hR : IsClosed R)
    (hfront : frontier W = range (fun z : Sphere 2 => nk.map (z, level)) ∪ R)
    (hdis : Disjoint (range (fun z : Sphere 2 => nk.map (z, level))) R) :
    ∃ K : Set M, IsCompact K ∧ closure (interior K) = K ∧
      frontier K = range (fun z : Sphere 2 => nk.map (z, level)) ∧
      K ⊆ interior cap.core.carrier ∧
      (W ⊆ K ∨ K ∩ W = range (fun z : Sphere 2 => nk.map (z, level)) ∧
        closure (interior (W ∪ K)) = W ∪ K ∧ frontier (W ∪ K) = R ∧
        range (fun z : Sphere 2 => nk.map (z, level)) ⊆ interior (W ∪ K)) := by
  have hcapture := nk.image_slab_subset_cap_core_of_center_in_slab heps q hlevel hy cap hdepth
  exact nk.exists_cap_filling_or_containment_of_sphere_subset hlevel cap.coreModel
    (by
      rintro z ⟨v, rfl⟩
      exact hcapture ⟨(v, level), ⟨mem_univ _, abs_le.mp hlevel⟩, rfl⟩)
    hW hconn hR hfront hdis

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

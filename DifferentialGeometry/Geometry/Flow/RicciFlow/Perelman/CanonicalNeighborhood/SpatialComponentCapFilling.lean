import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCapFrontierFilling
import DifferentialGeometry.Topology.Connected.ComponentFilling

noncomputable section
open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M] [SigmaCompactSpace M]
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
  classical
  let F (j : ι) := range (fun z : Sphere 2 => (neck j).map (z, level j))
  let R := ⋃ j ∈ alive.erase i, F j
  have hFclosed (j : ι) (hj : j ∈ alive) : IsClosed (F j) := by
    have hlen : (4 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (neck j).eps_pos).mpr (by linarith [(neck j).eps_small])
    apply IsCompact.isClosed
    apply isCompact_range
    exact (neck j).map.contMDiffOn_toFun.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const)
      (fun z => (neck j).domain ⟨mem_univ _, by constructor <;>
        linarith [(abs_le.mp (hlevel j hj)).1, (abs_le.mp (hlevel j hj)).2]⟩)
  have hR : IsClosed R := by
    apply Set.Finite.isClosed_biUnion (alive.erase i).finite_toSet
    exact fun j hj => hFclosed j (Finset.mem_of_mem_erase hj)
  have hfront' : frontier W = F i ∪ R := by
    rw [hfront]
    ext z
    simp only [F, R, mem_union, mem_iUnion, Finset.mem_erase]
    constructor
    · rintro ⟨j, hj, hz⟩
      by_cases hji : j = i
      · subst j; exact Or.inl hz
      · exact Or.inr ⟨j, ⟨hji, hj⟩, hz⟩
    · rintro (hz | ⟨j, hj, hz⟩)
      · exact ⟨i, hi, hz⟩
      · exact ⟨j, hj.2, hz⟩
  have hdis : Disjoint (F i) R := by
    apply disjoint_iUnion_right.mpr
    intro j
    apply disjoint_iUnion_right.mpr
    intro hj
    exact hpair hi (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm
  obtain ⟨K, hK, hKr, hKf, hKin⟩ := cap.core_model.exists_compact_side_of_sphere_embedding
    (fun z : Sphere 2 => (neck i).map (z, level i))
    ((neck i).isSmoothEmbedding_level ((hlevel i hi).trans_lt
      ((lt_inv_comm₀ (by norm_num) (neck i).eps_pos).mpr (by linarith [(neck i).eps_small]))))
    (by
      rintro z ⟨v, rfl⟩
      exact (neck i).image_slab_subset_cap_core_of_center_in_slab heps q (hlevel i hi) hy cap hdepth
        ⟨(v, level i), ⟨mem_univ _, abs_le.mp (hlevel i hi)⟩, rfl⟩)
  have hscalar : ∀ z ∈ K, C2⁻¹ * S.scalar t y ≤ S.scalar t z ∧ S.scalar t z ≤ C2 * S.scalar t y := by
    intro z hz
    exact witness.scalar_bounds z (interior_subset (cap.core_inside (interior_subset (hKin hz))))
  have havoid : W ⊆ (interior K)ᶜ := by
    apply DifferentialGeometry.Topology.subset_compl_interior_of_frontier_subset_of_components_meet_compl
      hW.symm.subset (by rw [hKf, hfront']; exact subset_union_left)
    intro x hx
    obtain ⟨a, ha, hlt⟩ := hanchor x hx
    refine ⟨a, ha, ?_⟩
    intro haK
    have hC2 : 0 < C2 := zero_lt_one.trans_le witness.one_le_comparison_constant
    have hb := mul_le_mul_of_nonneg_left (hscalar a haK).1 hC2.le
    rw [← mul_assoc, mul_inv_cancel₀ hC2.ne', one_mul] at hb
    exact hlt.not_ge hb
  let translate : Cylinder ≃ₜ Cylinder :=
    { toFun := fun z => (z.1, level i + z.2)
      invFun := fun z => (z.1, z.2 - level i)
      left_inv := by intro z; ext <;> simp
      right_inv := by intro z; ext <;> simp
      continuous_toFun := continuous_fst.prodMk (continuous_const.add continuous_snd)
      continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_const) }
  let T := translate.transOpenPartialHomeomorph (neck i).map.toOpenPartialHomeomorph
  have hzero (z : Sphere 2) : T (z, 0) = (neck i).map (z, level i) := by
    change (neck i).map (z, level i + 0) = _
    rw [add_zero]
  have hsrc (z : Sphere 2) : (z, 0) ∈ T.source := by
    change (z, level i + 0) ∈ (neck i).map.source
    rw [add_zero]
    have hlen : (4 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (neck i).eps_pos).mpr (by linarith [(neck i).eps_small])
    exact (neck i).domain ⟨mem_univ _, by constructor <;>
      linarith [(abs_le.mp (hlevel i hi)).1, (abs_le.mp (hlevel i hi)).2]⟩
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) zero_le_one)
  obtain ⟨hinter, hregular, hnewfront, hfill⟩ :=
    DifferentialGeometry.Topology.fill_of_shared_cylinder_boundary_of_disjoint_interiors T hsrc hW hKr
      (disjoint_left.mpr (fun z hzW hzK => havoid (interior_subset hzW) hzK)) hR
      (by simpa only [hzero] using hfront') (by simpa only [hzero] using hKf)
      (by simpa only [hzero] using hdis)
  simp only [hzero] at hinter hfill
  have hKavoid : K ⊆ (interior W)ᶜ := by
    have hd : Disjoint (interior K) (interior W) :=
      disjoint_left.mpr (fun z hzK hzW => havoid (interior_subset hzW) hzK)
    rw [← hKr]
    exact (hd.closure_left isOpen_interior).subset_compl_right
  have hKconn : IsPreconnected K := by
    rw [← hKr]
    exact (isConnected_interior_of_compact_regular_neck_boundary (neck i) (hlevel i hi)
      hK hKr hKf).isPreconnected.closure
  have hfrontDis : Disjoint K (frontier (W ∪ K)) := by
    rw [hnewfront, disjoint_left]
    intro z hzK hzR
    have hzW := hWcompact.isClosed.frontier_subset (hfront'.symm ▸ (show z ∈ F i ∪ R from Or.inr hzR))
    exact disjoint_left.mp hdis ((Set.ext_iff.mp hinter z).mp ⟨hzK, hzW⟩) hzR
  refine ⟨K, hK, hKr, hKin, hKf, hinter, hWcompact.union hK, hregular,
    hnewfront, hfill, hscalar, ?_⟩
  intro z hz
  exact DifferentialGeometry.Topology.connectedComponentIn_closed_exterior_eq_of_disjoint_frontier_union
    hK.isClosed hKconn hKavoid hfrontDis hz

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

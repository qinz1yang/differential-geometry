import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCapConnectedInterior
import DifferentialGeometry.Topology.Connected.ComponentFilling
import DifferentialGeometry.Topology.Connected.InteriorUnion

noncomputable section
open Set Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M]

open scoped Classical in
theorem exists_cap_filling_on_finite_spatial_neck_frontier_of_componentwise_avoidance
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ}
    {ι : Type*} (alive : Finset ι) (point : ι → M)
    (neck : ∀ i, SpatialNeck g eps (point i)) (level : ι → ℝ)
    (hlevel : ∀ i ∈ alive, |level i| ≤ 4)
    (hpair : (alive : Set ι).Pairwise (fun i j =>
      Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i)))
        (range (fun q : Sphere 2 => (neck j).map (q, level j)))))
    (i : ι) (hi : i ∈ alive) {U : Set M} (cap : CapCore U)
    (hinside : range (fun z : Sphere 2 => (neck i).map (z, level i)) ⊆ interior U)
    {W : Set M} (hWcompact : IsCompact W) (hW : closure (interior W) = W)
    (hfront : frontier W = ⋃ j ∈ alive, range (fun z : Sphere 2 => (neck j).map (z, level j)))
    (hanchor : ∀ x ∈ interior W, ∃ a ∈ connectedComponentIn (interior W) x,
      a ∉ interior U) :
    ∃ K : Set M, IsCompact K ∧ closure (interior K) = K ∧
      K ⊆ interior U ∧
      frontier K = range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
      K ∩ W = range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
      IsCompact (W ∪ K) ∧ closure (interior (W ∪ K)) = W ∪ K ∧
      frontier (W ∪ K) = ⋃ j ∈ alive.erase i, range (fun z : Sphere 2 => (neck j).map (z, level j)) ∧
      range (fun z : Sphere 2 => (neck i).map (z, level i)) ⊆ interior (W ∪ K) ∧
      (∀ z ∈ K, connectedComponentIn (interior W)ᶜ z = K) ∧
      K ⊆ interior (W ∪ K) ∧
      ∀ x ∈ interior (W ∪ K),
        (connectedComponentIn (interior (W ∪ K)) x ∩ interior W).Nonempty := by
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
  obtain ⟨K, hK, hKr, hKf, hKin⟩ := cap.exists_compact_side_of_sphere_embedding
    (fun z : Sphere 2 => (neck i).map (z, level i))
    ((neck i).isSmoothEmbedding_level ((hlevel i hi).trans_lt
      ((lt_inv_comm₀ (by norm_num) (neck i).eps_pos).mpr (by linarith [(neck i).eps_small]))))
    hinside
  have havoid : W ⊆ (interior K)ᶜ := by
    apply DifferentialGeometry.Topology.subset_compl_interior_of_frontier_subset_of_components_meet_compl
      hW.symm.subset (by rw [hKf, hfront']; exact subset_union_left)
    intro x hx
    obtain ⟨a, ha, haU⟩ := hanchor x hx
    exact ⟨a, ha, fun haK => haU (hKin haK)⟩
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
  have hKfill : K ⊆ interior (W ∪ K) := by
    intro z hz
    by_cases hzint : z ∈ interior K
    · exact interior_mono subset_union_right hzint
    · exact hfill (hKf ▸ ⟨subset_closure hz, hzint⟩)
  have hmeet : (K ∩ W).Nonempty := by
    rw [hinter]
    exact ⟨(neck i).map ((neck i).center, level i), mem_range_self _⟩
  let _ : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ThreeSpace M
  refine ⟨K, hK, hKr, hKin, hKf, hinter, hWcompact.union hK, hregular,
    hnewfront, hfill, ?_, hKfill, ?_⟩
  · intro z hz
    exact DifferentialGeometry.Topology.connectedComponentIn_closed_exterior_eq_of_disjoint_frontier_union
      hK.isClosed hKconn hKavoid hfrontDis hz
  · intro x hx
    exact DifferentialGeometry.Topology.connectedComponentIn_interior_union_inter_interior_nonempty
      hW.symm.subset hK.isClosed hKconn hKfill hmeet hx

omit [PreconnectedSpace M] in
theorem exists_cap_union_on_finite_spatial_neck_frontier
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ}
    {ι : Type*} (alive : Finset ι) (point : ι → M)
    (neck : ∀ i, SpatialNeck g eps (point i)) (level : ι → ℝ)
    (hlevel : ∀ i ∈ alive, |level i| < eps⁻¹)
    (hpair : (alive : Set ι).Pairwise (fun i j =>
      Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i)))
        (range (fun q : Sphere 2 => (neck j).map (q, level j)))))
    (i : ι) (hi : i ∈ alive) {U : Set M} (cap : CapCore U)
    (hinside : range (fun z : Sphere 2 => (neck i).map (z, level i)) ⊆ interior U)
    {W : Set M} (hWcompact : IsCompact W) (hW : closure (interior W) = W)
    (hfront : frontier W = ⋃ j ∈ alive, range (fun z : Sphere 2 => (neck j).map (z, level j))) :
    ∃ (K : Set M) (remaining : Finset ι),
      IsCompact K ∧ closure (interior K) = K ∧ K ⊆ interior U ∧
      frontier K = range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
      IsCompact (W ∪ K) ∧ closure (interior (W ∪ K)) = W ∪ K ∧
      remaining ⊆ alive ∧
      frontier (W ∪ K) = ⋃ j ∈ remaining, range (fun z : Sphere 2 => (neck j).map (z, level j)) ∧
      (∀ j ∈ alive, j ≠ i → (j ∈ remaining ↔
        Disjoint (range (fun z : Sphere 2 => (neck j).map (z, level j))) K)) ∧
      (∀ j ∈ alive, j ∉ remaining →
        range (fun z : Sphere 2 => (neck j).map (z, level j)) ⊆ interior (W ∪ K)) ∧
      ((range (fun z : Sphere 2 => (neck i).map (z, level i)) ∩
        closure (W \ K)).Nonempty → i ∉ remaining) ∧
      ((i ∈ remaining ∧
          range (fun z : Sphere 2 => (neck i).map (z, level i)) ⊆ frontier (W ∪ K)) ∨
        (i ∉ remaining ∧ remaining.card < alive.card ∧ K ⊆ interior (W ∪ K))) := by
  classical
  let F (j : ι) := range (fun z : Sphere 2 => (neck j).map (z, level j))
  let R := ⋃ j ∈ alive.erase i, F j
  have hcontinuous (j : ι) (hj : j ∈ alive) :
      Continuous (fun z : Sphere 2 => (neck j).map (z, level j)) := by
    exact (neck j).map.contMDiffOn_toFun.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const)
      (fun z => (neck j).domain ⟨mem_univ _, abs_lt.mp (hlevel j hj)⟩)
  have hR : IsClosed R := by
    apply Set.Finite.isClosed_biUnion (alive.erase i).finite_toSet
    intro j hj
    exact (isCompact_range (hcontinuous j (Finset.mem_of_mem_erase hj))).isClosed
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
  obtain ⟨K, hK, hKr, hKf, hKin⟩ := cap.exists_compact_side_of_sphere_embedding
    (fun z : Sphere 2 => (neck i).map (z, level i))
    ((neck i).isSmoothEmbedding_level (hlevel i hi))
    hinside
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
    exact (neck i).domain ⟨mem_univ _, abs_lt.mp (hlevel i hi)⟩
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) zero_le_one)
  let outside := (alive.erase i).filter (fun j => Disjoint (F j) K)
  have houtside : outside ⊆ alive := fun j hj =>
    Finset.mem_of_mem_erase (Finset.mem_filter.mp hj).1
  have hnoti : i ∉ outside := by simp [outside]
  have hFavoid (j : ι) (hj : j ∈ alive) (hji : j ≠ i) :
      Disjoint (F j) (frontier K) := by
    rw [hKf]
    exact hpair hj hi hji
  have hFin (j : ι) (hj : j ∈ alive) (hji : j ≠ i)
      (hnot : ¬ Disjoint (F j) K) : F j ⊆ interior K := by
    obtain ⟨z, hzF, hzK⟩ := Set.not_disjoint_iff.mp hnot
    have hzint : z ∈ interior K := by
      by_contra hn
      exact disjoint_left.mp (hFavoid j hj hji) hzF ⟨subset_closure hzK, hn⟩
    exact DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
      (isPreconnected_range (hcontinuous j hj)) (hFavoid j hj hji) ⟨z, hzF, hzint⟩
  have houtfront : R \ K = ⋃ j ∈ outside, F j := by
    ext z
    constructor
    · rintro ⟨hzR, hzK⟩
      obtain ⟨j, hj, hzF⟩ := mem_iUnion₂.mp hzR
      have hjdis : Disjoint (F j) K := by
        by_contra hn
        exact hzK (interior_subset
          (hFin j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj) hn hzF))
      exact mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hjdis⟩, hzF⟩
    · intro hz
      obtain ⟨j, hj, hzF⟩ := mem_iUnion₂.mp hz
      obtain ⟨hj, hjdis⟩ := Finset.mem_filter.mp hj
      exact ⟨mem_iUnion₂.mpr ⟨j, hj, hzF⟩, fun hzK => disjoint_left.mp hjdis hzF hzK⟩
  obtain ⟨hregular, hcases⟩ :=
    DifferentialGeometry.Topology.frontier_union_of_shared_cylinder_boundary T hsrc hW hKr
      hR (by simpa only [hzero] using hfront') (by simpa only [hzero] using hKf)
      (by simpa only [hzero] using hdis)
  simp only [hzero] at hcases
  have haccum (ht : (F i ∩ closure (W \ K)).Nonempty) : F i ⊆ interior (W ∪ K) := by
    obtain ⟨_, _, hfill⟩ :=
      DifferentialGeometry.Topology.fill_of_shared_cylinder_boundary_of_exterior_accumulation
        T hsrc hW hKr hR (by simpa only [hzero] using hfront')
        (by simpa only [hzero] using hKf) (by simpa only [hzero] using hdis)
        (by simpa only [hzero] using ht)
    simpa only [hzero] using hfill
  rcases hcases with ⟨hfrontV, hfill⟩ | ⟨hfrontV, hkeep⟩
  · refine ⟨K, outside, hK, hKr, hKin, hKf, hWcompact.union hK, hregular, houtside,
      hfrontV.trans houtfront, ?_, ?_, fun _ => hnoti, Or.inr ⟨hnoti, ?_, ?_⟩⟩
    · intro j hj hji
      simp [outside, hj, hji, F]
    · intro j hj hjout
      by_cases hji : j = i
      · subst j; exact hfill
      · exact (hFin j hj hji (by simpa [outside, hj, hji] using hjout)).trans
          (interior_mono subset_union_right)
    · exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨houtside, fun he => hnoti (he ▸ hi)⟩)
    · intro z hzK
      by_cases hzint : z ∈ interior K
      · exact interior_mono subset_union_right hzint
      · exact hfill (hKf ▸ ⟨subset_closure hzK, hzint⟩)
  · refine ⟨K, insert i outside, hK, hKr, hKin, hKf, hWcompact.union hK, hregular,
      Finset.insert_subset hi houtside, ?_, ?_, ?_, ?_, Or.inl ⟨Finset.mem_insert_self _ _, hkeep⟩⟩
    · rw [hfrontV, houtfront]
      ext z
      simp only [Finset.mem_insert, mem_iUnion, mem_union]
      aesop
    · intro j hj hji
      simp [outside, hj, hji, F]
    · intro j hj hjout
      have hji : j ≠ i := fun he => hjout (he ▸ Finset.mem_insert_self i outside)
      have hn : ¬ Disjoint (F j) K := by
        intro hd
        exact hjout (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨hji, hj⟩, hd⟩))
      exact (hFin j hj hji hn).trans (interior_mono subset_union_right)
    · intro ht _
      exact (hkeep (mem_range_self (neck i).center)).2 (haccum ht (mem_range_self _))

omit [PreconnectedSpace M] in
theorem exists_cap_filling_on_finite_spatial_neck_frontier_of_incident_component_avoidance
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ}
    {ι : Type*} (alive : Finset ι) (point : ι → M)
    (neck : ∀ i, SpatialNeck g eps (point i)) (level : ι → ℝ)
    (hlevel : ∀ i ∈ alive, |level i| < eps⁻¹)
    (hpair : (alive : Set ι).Pairwise (fun i j =>
      Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i)))
        (range (fun q : Sphere 2 => (neck j).map (q, level j)))))
    (i : ι) (hi : i ∈ alive) {U : Set M} (cap : CapCore U)
    (hinside : range (fun z : Sphere 2 => (neck i).map (z, level i)) ⊆ interior U)
    {W : Set M} (hWcompact : IsCompact W) (hW : closure (interior W) = W)
    (hfront : frontier W = ⋃ j ∈ alive, range (fun z : Sphere 2 => (neck j).map (z, level j)))
    (x : M)
    (hincident : (range (fun z : Sphere 2 => (neck i).map (z, level i)) ∩
      closure (connectedComponentIn (interior W) x)).Nonempty)
    (hanchor : ∃ a ∈ connectedComponentIn (interior W) x, a ∉ interior U) :
    ∃ (K : Set M) (remaining : Finset ι),
      IsCompact K ∧ closure (interior K) = K ∧ K ⊆ interior U ∧
      frontier K = range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
      IsCompact (W ∪ K) ∧ closure (interior (W ∪ K)) = W ∪ K ∧
      remaining ⊆ alive ∧
      frontier (W ∪ K) = ⋃ j ∈ remaining, range (fun z : Sphere 2 => (neck j).map (z, level j)) ∧
      (∀ j ∈ alive, j ≠ i → (j ∈ remaining ↔
        Disjoint (range (fun z : Sphere 2 => (neck j).map (z, level j))) K)) ∧
      (∀ j ∈ alive, j ∉ remaining →
        range (fun z : Sphere 2 => (neck j).map (z, level j)) ⊆ interior (W ∪ K)) ∧
      i ∉ remaining ∧ remaining.card < alive.card ∧ K ⊆ interior (W ∪ K) := by
  obtain ⟨K, remaining, hK, hKr, hKin, hKf, hV, hVr, hremaining,
    hfrontV, hother, hremoved, haccum, hcases⟩ :=
    exists_cap_union_on_finite_spatial_neck_frontier alive point neck level hlevel hpair
      i hi cap hinside hWcompact hW hfront
  have havoid : connectedComponentIn (interior W) x ⊆ (frontier K)ᶜ := by
    intro y hy hyK
    have hyF : y ∈ frontier W := hfront.symm ▸ mem_iUnion₂.mpr ⟨i, hi, hKf ▸ hyK⟩
    exact hyF.2 (connectedComponentIn_subset (interior W) x hy)
  have hsplit : (frontier K)ᶜ = interior K ∪ Kᶜ := by
    rw [compl_frontier_eq_union_interior, hK.isClosed.isOpen_compl.interior_eq]
  have hout : connectedComponentIn (interior W) x ⊆ Kᶜ := by
    rcases isPreconnected_connectedComponentIn.subset_or_subset isOpen_interior
      hK.isClosed.isOpen_compl (disjoint_compl_right.mono_left interior_subset)
      (havoid.trans hsplit.subset) with hin | hout
    · obtain ⟨a, ha, haU⟩ := hanchor
      exact (haU (hKin (interior_subset (hin ha)))).elim
    · exact hout
  have hiout : i ∉ remaining := by
    apply haccum
    obtain ⟨y, hyS, hyC⟩ := hincident
    refine ⟨y, hyS, closure_mono ?_ hyC⟩
    intro z hz
    exact ⟨interior_subset (connectedComponentIn_subset (interior W) x hz), hout hz⟩
  rcases hcases with ⟨hikeep, _⟩ | ⟨_, hcard, hfill⟩
  · exact (hiout hikeep).elim
  · exact ⟨K, remaining, hK, hKr, hKin, hKf, hV, hVr, hremaining,
      hfrontV, hother, hremoved, hiout, hcard, hfill⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

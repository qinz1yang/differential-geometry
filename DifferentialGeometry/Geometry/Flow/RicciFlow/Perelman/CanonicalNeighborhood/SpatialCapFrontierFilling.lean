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
    alive point neck level hlevel hdisjoint i hi cap.coreModel
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

open scoped Classical in
theorem CanonicalWitness.exists_neck_or_cap_filling_on_finite_spatial_neck_frontier
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
    (anchor : M) (hanchor : anchor ∈ W) (hscalar : C2 * S.scalar t anchor < S.scalar t y) :
    (∃ localNeck : LocalNeck S epsc y t witness.domain.carrier,
      witness.alternative = CanonicalAlternative.neck localNeck) ∨
    ∃ (cap : LocalCap S epsc y t witness.domain.carrier)
      (depth : ∀ z ∈ cap.tube,
        10000 / Real.sqrt (S.scalar t y) ≤ metricDistance (S.base.metric t) y z),
      witness.alternative = CanonicalAlternative.cap cap depth ∧
      ∃ K : Set M, IsCompact K ∧ closure (interior K) = K ∧ K ⊆ interior cap.core.carrier ∧
        frontier K = range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
        K ∩ W = range (fun z : Sphere 2 => (neck i).map (z, level i)) ∧
        IsCompact (W ∪ K) ∧ IsConnected (interior (W ∪ K)) ∧
        closure (interior (W ∪ K)) = W ∪ K ∧
        frontier (W ∪ K) = ⋃ j ∈ alive.erase i,
          range (fun z : Sphere 2 => (neck j).map (z, level j)) ∧
        range (fun z : Sphere 2 => (neck i).map (z, level i)) ⊆ interior (W ∪ K) ∧
        (alive.erase i).card + 1 = alive.card ∧
        (∀ j ∈ alive.erase i,
          Disjoint K (range (fun z : Sphere 2 => (neck j).map (z, level j)))) ∧
        (∀ z ∈ K, C2⁻¹ * S.scalar t y ≤ S.scalar t z ∧
          S.scalar t z ≤ C2 * S.scalar t y) ∧
        ∀ {B : ℝ}, (∀ z ∈ W, S.scalar t z ≤ B) →
          ∀ z ∈ W ∪ K, S.scalar t z ≤ max B (C2 * S.scalar t y) := by
  classical
  have hcomponent : anchor ∈ connectedComponent y := by
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    exact mem_univ _
  rcases witness.alternative_eq_neck_or_cap_of_mul_scalar_lt hcomponent hscalar with
    hn | ⟨cap, depth, htag⟩
  · exact Or.inl hn
  · obtain ⟨K, hK, hKr, hKin, hKf, hinter, hV, hVc, hVr, hVf, hfill⟩ :=
      exists_connected_cap_filling_on_finite_spatial_neck_frontier_of_mul_scalar_lt
        alive point neck level hlevel hdisjoint heps i hi q hy witness cap depth
        hcompact hW hconn hfront anchor hanchor hscalar
    have hKscalar : ∀ z ∈ K, C2⁻¹ * S.scalar t y ≤ S.scalar t z ∧
        S.scalar t z ≤ C2 * S.scalar t y := by
      intro z hz
      exact witness.scalar_bounds z
        (interior_subset (cap.core_inside (interior_subset (hKin hz))))
    refine Or.inr ⟨cap, depth, htag, K, hK, hKr, hKin, hKf, hinter,
      hV, hVc, hVr, ?_, hfill, ?_, ?_, hKscalar, ?_⟩
    · rw [hVf]
      ext z
      simp only [mem_iUnion, Finset.mem_erase]
      constructor
      · rintro ⟨j, hj, hji, hz⟩
        exact ⟨j, ⟨hji, hj⟩, hz⟩
      · rintro ⟨j, ⟨hji, hj⟩, hz⟩
        exact ⟨j, hj, hji, hz⟩
    · exact Finset.card_erase_add_one hi
    · intro j hj
      rw [disjoint_left]
      intro z hzK hzj
      have hzW := hcompact.isClosed.frontier_subset
        (hfront.symm ▸ mem_iUnion₂.mpr ⟨j, Finset.mem_of_mem_erase hj, hzj⟩)
      have hzi : z ∈ range (fun v : Sphere 2 => (neck i).map (v, level i)) :=
        hinter ▸ (show z ∈ K ∩ W from ⟨hzK, hzW⟩)
      exact disjoint_left.mp
        (hdisjoint hi (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm) hzi hzj
    · intro B hbound z hz
      rcases hz with hz | hz
      · exact (hbound z hz).trans (le_max_left _ _)
      · exact (hKscalar z hz).2.trans (le_max_right _ _)


theorem exists_connected_region_with_neck_alternatives_on_finite_spatial_neck_frontier
    {ι : Type*} (alive : Finset ι) (point : ι → M)
    (neck : ∀ i, SpatialNeck (S.base.metric t) eps (point i)) (level : ι → ℝ)
    (hlevel : ∀ i ∈ alive, |level i| ≤ 4)
    (hdisjoint : (alive : Set ι).Pairwise (fun i j =>
      Disjoint (range (fun q : Sphere 2 => (neck i).map (q, level i)))
        (range (fun q : Sphere 2 => (neck j).map (q, level j)))))
    (heps : eps ≤ 1 / 8646)
    (witness : ∀ i ∈ alive, CanonicalWitness S epsc C1 C2 ((neck i).map ((neck i).center, level i)) t)
    {W : Set M} (hcompact : IsCompact W) (hW : closure (interior W) = W)
    (hconn : IsPreconnected (interior W))
    (hfront : frontier W = ⋃ j ∈ alive, range (fun z : Sphere 2 => (neck j).map (z, level j)))
    (anchor : M) (hanchor : anchor ∈ W)
    (hscalar : ∀ i ∈ alive, C2 * S.scalar t anchor <
      S.scalar t ((neck i).map ((neck i).center, level i))) :
    ∃ (V : Set M) (remaining : Finset ι),
      W ⊆ V ∧ IsCompact V ∧ closure (interior V) = V ∧ IsConnected (interior V) ∧
      ∃ hremaining : remaining ⊆ alive,
      frontier V = ⋃ j ∈ remaining, range (fun z : Sphere 2 => (neck j).map (z, level j)) ∧
      V ⊆ W ∪ ⋃ j, ⋃ hj : j ∈ alive, (witness j hj).domain.carrier ∧
      (∀ j (hj : j ∈ alive), j ∉ remaining →
        range (fun z : Sphere 2 => (neck j).map (z, level j)) ⊆ interior V ∧
        ∃ (cap : LocalCap S epsc ((neck j).map ((neck j).center, level j)) t
            (witness j hj).domain.carrier)
          (depth : ∀ z ∈ cap.tube, 10000 / Real.sqrt
            (S.scalar t ((neck j).map ((neck j).center, level j))) ≤
              metricDistance (S.base.metric t) ((neck j).map ((neck j).center, level j)) z),
          (witness j hj).alternative = CanonicalAlternative.cap cap depth) ∧
      ∀ j (hj : j ∈ remaining), ∃ localNeck : LocalNeck S epsc
          ((neck j).map ((neck j).center, level j)) t (witness j (hremaining hj)).domain.carrier,
        (witness j (hremaining hj)).alternative = CanonicalAlternative.neck localNeck := by
  classical
  induction alive using Finset.strongInductionOn generalizing W
  rename_i alive ih
  by_cases hall : ∀ j (hj : j ∈ alive), ∃ localNeck : LocalNeck S epsc
      ((neck j).map ((neck j).center, level j)) t (witness j hj).domain.carrier,
      (witness j hj).alternative = CanonicalAlternative.neck localNeck
  · have hne : (interior W).Nonempty := closure_nonempty_iff.mp
      (show (closure (interior W)).Nonempty from hW.symm ▸ ⟨anchor, hanchor⟩)
    exact ⟨W, alive, Subset.rfl, hcompact, hW, ⟨hne, hconn⟩, Subset.rfl, hfront,
      subset_union_left, fun j hj h => (h hj).elim, hall⟩
  push Not at hall
  obtain ⟨i, hi, hn⟩ := hall
  rcases (witness i hi).exists_neck_or_cap_filling_on_finite_spatial_neck_frontier
    alive point neck level hlevel hdisjoint heps i hi (neck i).center rfl
    hcompact hW hconn hfront anchor hanchor (hscalar i hi) with hneck | hcap
  · obtain ⟨localNeck, htag⟩ := hneck
    exact (hn localNeck htag).elim
  · obtain ⟨cap, depth, htag, K, _, _, hKin, _, _, hV, hVc, hVr, hVf, hfill, _, _, _, _⟩ := hcap
    have hsub : alive.erase i ⊂ alive := Finset.erase_ssubset hi
    obtain ⟨V, remaining, hUV, hcompactV, hregularV, hconnV, hremaining, hfrontV,
      hcontrolled, hremoved, hnecks⟩ :=
      ih (alive.erase i) hsub (fun j hj => hlevel j (Finset.mem_of_mem_erase hj))
        (fun j hj k hk hjk => hdisjoint (Finset.mem_of_mem_erase hj)
          (Finset.mem_of_mem_erase hk) hjk)
        (fun j hj => witness j (Finset.mem_of_mem_erase hj)) hV hVr hVc.isPreconnected hVf
        (Or.inl hanchor) (fun j hj => hscalar j (Finset.mem_of_mem_erase hj))
    refine ⟨V, remaining, subset_union_left.trans hUV, hcompactV, hregularV, hconnV,
      hremaining.trans (Finset.erase_subset _ _), hfrontV, ?_, ?_, hnecks⟩
    · intro z hz
      rcases hcontrolled hz with (hzW | hzK) | hzU
      · exact Or.inl hzW
      · exact Or.inr (mem_iUnion₂.mpr ⟨i, hi,
          interior_subset (cap.core_inside (interior_subset (hKin hzK)))⟩)
      · obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hzU
        exact Or.inr (mem_iUnion₂.mpr ⟨j, Finset.mem_of_mem_erase hj, hzj⟩)
    · intro j hj hjn
      by_cases hji : j = i
      · subst j
        exact ⟨hfill.trans (interior_mono hUV), cap, depth, htag⟩
      · obtain ⟨hinside, cap', depth', htag'⟩ :=
          hremoved j (Finset.mem_erase.mpr ⟨hji, hj⟩) hjn
        exact ⟨hinside, cap', depth', htag'⟩


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

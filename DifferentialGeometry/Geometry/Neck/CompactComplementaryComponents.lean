import DifferentialGeometry.Geometry.Neck.FiniteFrontierEnd
import DifferentialGeometry.Topology.ProperMap.HalfCylinderComponent
import DifferentialGeometry.Topology.Connected.ComponentFilling

noncomputable section
open Set Manifold
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

theorem exists_spatial_neck_compact_bridging_component_tolerance :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [PreconnectedSpace M]
        (g : SmoothRiemannianMetric I3 M) (W : Set M),
        IsCompact W → closure (interior W) = W →
        ∀ (ι : Type v) [Finite ι] (point : ι → M) (neck : ∀ i, SpatialNeck g eps (point i))
        (level : ι → ℝ), (∀ i, |level i| ≤ 4) →
        Pairwise (fun i j => Disjoint (range (fun q => (neck i).map (q, level i)))
          (range (fun q => (neck j).map (q, level j)))) →
        frontier W = ⋃ i, range (fun q => (neck i).map (q, level i)) →
        (∀ x : M, x ∉ interior W → Nonempty (SpatialNeck g eps x)) →
        (∀ B : ℝ, IsCompact {x : M | Geometry.Curvature.metricScalarAt g x ≤ B}) →
        ∀ x p q : M,
          (connectedComponentIn (interior W)ᶜ x ∩ connectedComponentIn W p).Nonempty →
          (connectedComponentIn (interior W)ᶜ x ∩ connectedComponentIn W q).Nonempty →
          connectedComponentIn W p ≠ connectedComponentIn W q →
          IsCompact (connectedComponentIn (interior W)ᶜ x) := by
  obtain ⟨eta, heta, hends⟩ := exists_spatial_neck_saved_end_decomposition_tolerance.{u, v}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ _ g W hW hWreg ι _ point neck level hlevel hpair
    hfront hneck hscalar x p q hp hq hne
  have hWne : W.Nonempty := by
    obtain ⟨a, _, hap⟩ := hp
    exact ⟨a, connectedComponentIn_subset W p hap⟩
  by_cases hM : IsCompact (univ : Set M)
  · exact hM.of_isClosed_subset (isOpen_interior.isClosed_compl.connectedComponentIn x)
      (subset_univ _)
  let _ : NoncompactSpace M := ⟨hM⟩
  obtain ⟨K, m, origin, Θ, hWK, hK, hKconn, hKreg, hm, horigin, hfrontsub, hbase,
    hends, hdisjoint, hfrontK, hcover⟩ :=
    hends eps heps M g W hW hWne hWreg ι point neck level hlevel hpair hfront hneck hscalar
  let E (i : Fin m) := Θ i '' (univ ×ˢ Ici (0 : ℝ))
  let F (i : Fin m) (z : Sphere 2 × ℝ≥0) := Θ i (z.1, z.2.val)
  have hErange (i) : E i = range (F i) := by
    ext y
    constructor
    · rintro ⟨⟨z, t⟩, ⟨_, ht⟩, hy⟩
      exact ⟨(z, ⟨t, ht⟩), hy⟩
    · rintro ⟨⟨z, t⟩, hy⟩
      exact ⟨(z, t.val), ⟨mem_univ _, t.property⟩, hy⟩
  have hbaseRange (i) : range (fun z => F i (z, 0)) =
      range (fun z => (neck (origin i)).map (z, level (origin i))) :=
    congrArg range (funext (hbase i))
  have hbaseW (i) : range (fun z => F i (z, 0)) ⊆ W := by
    rw [hbaseRange]
    intro y hy
    exact hW.isClosed.frontier_subset (hfront.symm ▸ mem_iUnion.mpr ⟨origin i, hy⟩)
  have hinter (i) : range (F i) ∩ W = range (fun z => F i (z, 0)) := by
    apply subset_antisymm
    · intro y hy
      exact (hends i).2.2.2.2.1 ▸ ⟨((Set.ext_iff.mp (hErange i) y).mpr hy.1), hWK hy.2⟩
    · intro y hy
      obtain ⟨z, rfl⟩ := hy
      exact ⟨mem_range_self _, hbaseW i (mem_range_self _)⟩
  have hsphereClosed (j : ι) : IsClosed (range (fun z => (neck j).map (z, level j))) := by
    apply IsCompact.isClosed
    apply isCompact_range
    have hlen : (4 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (neck j).eps_pos).mpr (by linarith [(neck j).eps_small])
    exact (neck j).map.contMDiffOn_toFun.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const)
      (fun z => (neck j).domain ⟨mem_univ _, by constructor <;>
        linarith [(abs_le.mp (hlevel j)).1, (abs_le.mp (hlevel j)).2]⟩)
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) zero_le_one)
  have hcomponents (i : Fin m) (y : M) (hy : y ∈ E i) :
      connectedComponentIn (interior W)ᶜ y = E i := by
    obtain ⟨hsm, hinj, hproper, hembed, hIK, hdiv, p, nk, A, hp, hA, hfirst, hcontrol⟩ := hends i
    let R : Set M := ⋃ j : {j : ι // j ≠ origin i}, range (fun z => (neck j.val).map (z, level j.val))
    have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => hsphereClosed j.val)
    have hfrontR : frontier W = range (fun z => F i (z, 0)) ∪ R := by
      rw [hbaseRange, hfront]
      ext z
      constructor
      · intro hz
        obtain ⟨j, hj⟩ := mem_iUnion.mp hz
        by_cases heq : j = origin i
        · subst j
          exact Or.inl hj
        · exact Or.inr (mem_iUnion.mpr ⟨⟨j, heq⟩, hj⟩)
      · rintro (hz | hz)
        · exact mem_iUnion.mpr ⟨origin i, hz⟩
        · obtain ⟨j, hj⟩ := mem_iUnion.mp hz
          exact mem_iUnion.mpr ⟨j.val, hj⟩
    have hdis : Disjoint (range (fun z => F i (z, 0))) R := by
      rw [hbaseRange, disjoint_iUnion_right]
      intro j
      exact hpair (Ne.symm j.property)
    have hFinj : Function.Injective (F i) := by
      intro z w h
      have heq := hinj (show (z.1, z.2.val) ∈ univ ×ˢ Ici (0 : ℝ) from
        ⟨mem_univ _, z.2.property⟩) (show (w.1, w.2.val) ∈ univ ×ˢ Ici (0 : ℝ) from
        ⟨mem_univ _, w.2.property⟩) h
      have hfst : z.1 = w.1 := congrArg (fun q : Sphere 2 × ℝ => q.1) heq
      have hsnd : z.2.val = w.2.val := congrArg (fun q : Sphere 2 × ℝ => q.2) heq
      exact Prod.ext hfst (Subtype.ext hsnd)
    have hopen : IsOpen (F i '' (univ ×ˢ Ioi (0 : ℝ≥0))) := by
      let V : TopologicalSpace.Opens Cylinder :=
        ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
      have hh := _root_.Manifold.isOpen_range_of_isSmoothEmbedding (by simp [ThreeSpace]) hembed
      have heq : range (fun z : V => Θ i z) = F i '' (univ ×ˢ Ioi (0 : ℝ≥0)) := by
        ext z
        constructor
        · rintro ⟨⟨⟨q, t⟩, hqt⟩, rfl⟩
          exact ⟨(q, ⟨t, hqt.2.le⟩), ⟨mem_univ _, hqt.2⟩, rfl⟩
        · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
          exact ⟨⟨(q, t.val), mem_univ _, ht⟩, rfl⟩
      exact heq ▸ hh
    rw [hErange]
    exact DifferentialGeometry.Topology.connectedComponentIn_closed_exterior_eq_range_half_cylinder
      (F i) hproper hFinj hopen A.toOpenPartialHomeomorph hA hfirst hWreg hR hfrontR hdis
      (hinter i) ((hErange i) ▸ hy)
  have hbaseConnected (i) : IsPreconnected (E i ∩ W) := by
    rw [hErange, hinter]
    exact isPreconnected_range ((hends i).2.2.1.continuous.comp
      (continuous_id.prodMk continuous_const))
  exact DifferentialGeometry.Topology.isCompact_closed_exterior_component_of_connected_intersections
    K hK E (by rw [hcover]; exact subset_univ _) hcomponents hbaseConnected hp hq hne

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonCircleParametrization
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactIncidentEdges
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTargetCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}

private theorem space_restrict_section34CompactSimplexRim (hsub : IsSubdivision K' K)
    (s : Section34CompactSimplexIndex K 3) :
    (restrict K' (section34CompactSimplexRim s.1)).space = section34CompactSimplexRim s.1 := by
  have hRK : (restrict K (section34CompactSimplexRim s.1)).space =
      section34CompactSimplexRim s.1 := by
    apply restrict_space_of_eq_biUnion
    apply Subset.antisymm
    · intro x hx
      obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
      have hut : u ⊂ s.1 := hu
      have hne : u.Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        subst hne
        simp at hxu
      have huK := K.down_closed s.2.1 (Finset.ssubset_iff_subset_ne.mp hut).1 hne
      exact mem_iUnion₂.mpr ⟨u, ⟨huK, fun y hy => mem_iUnion₂.mpr ⟨u, hu, hy⟩⟩, hxu⟩
    · exact iUnion₂_subset fun u hu => hu.2
  have h := (hsub.restrict (restrict K (section34CompactSimplexRim s.1))
    (restrict_faces_subset K _)).1
  rwa [hRK] at h

theorem exists_cycle_order_compact_face_vertex_balls
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src)) (s : Section34CompactSimplexIndex K 3) :
    ∃ (n : ℕ) (v : Fin (n + 3) → Section34CompactVertexIndex K K'),
      Function.Injective v ∧
      (∀ w, Section34Incident w.1 s.1 ↔ ∃ i, v i = w) ∧
      (∀ i j, i ≠ j → ((SimpleGraph.cycleGraph (n + 3)).Adj i j ↔
        (section34CompactVertexBallImage src f₁ (v i) ∩
          section34CompactVertexBallImage src f₁ (v j)).Nonempty)) ∧
      (∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j →
        ∃ e : Section34CompactEdgeIndex K K', Section34Incident e.1 s.1 ∧
          section34CompactSplitDiskImage src f₁ e =
            section34CompactVertexBallImage src f₁ (v i) ∩
              section34CompactVertexBallImage src f₁ (v j)) ∧
      (∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 s.1 →
        ∃ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j ∧
          section34CompactSplitDiskImage src f₁ e =
            section34CompactVertexBallImage src f₁ (v i) ∩
              section34CompactVertexBallImage src f₁ (v j)) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        section34CompactVertexBallImage src f₁ (v i) ∩
          section34CompactVertexBallImage src f₁ (v j) ∩
            section34CompactVertexBallImage src f₁ (v k) = ∅) ∧
      (⋃ i, section34CompactVertexBallImage src f₁ (v i)) =
        section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s := by
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨-, -, hK'fin, -, hsub, -, hcell, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hvertexEdge, hends, -⟩ := id hcut
  let L := restrict K' (section34CompactSimplexRim s.1)
  have hLsp : L.space = section34CompactSimplexRim s.1 :=
    space_restrict_section34CompactSimplexRim hsub s
  have : Finite K'.faces := hK'fin.to_subtype
  have : Finite L.faces := (restrict_faces_finite K' _).to_subtype
  have hLsph : IsPLSphere 1 L.space := by
    rw [hLsp]
    exact isPLSphere_one_section34CompactSimplexRim s.2.1 s.2.2
  have hLman : IsCombinatorialManifold 1 L := IsPLSphere.isCombinatorialManifold hLsph
  have hconn := edgeGraph_connected_of_isConnected_space L hLsph.isConnected
  let _ : Fintype L.vertices := (SimplicialComplex.finite_vertices L).fintype
  have hdeg : ∀ v, ((SimplicialComplex.edgeGraph L).neighborSet v).ncard = 2 :=
    ncard_neighborSet_edgeGraph_eq_two hLman
  let wv : L.vertices → Section34CompactVertexIndex K K' := fun v =>
    ⟨{(v : E3)}, v.2.1, Finset.card_singleton _,
      v.2.2.trans (section34CompactSimplexRim_subset_graphSkeleton s.2.1 s.2.2.le)⟩
  have hwvinj : Function.Injective wv := by
    intro a b hab
    apply Subtype.ext
    have h := congrArg Subtype.val hab
    exact Finset.singleton_inj.mp h
  have hwvinc : ∀ v, Section34Incident (wv v).1 s.1 := by
    intro v
    change (({(v : E3)} : Finset E3) : Set E3) ⊆ convexHull ℝ (s.1 : Set E3)
    rw [Finset.coe_singleton]
    exact singleton_subset_iff.mpr
      (section34CompactSimplexRim_subset s.1 (v.2.2 (subset_convexHull ℝ _ (by simp))))
  have hwvsurj : ∀ w : Section34CompactVertexIndex K K', Section34Incident w.1 s.1 →
      ∃ v, wv v = w := by
    intro w hw
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp w.2.2.1
    have haR : a ∈ section34CompactSimplexRim s.1 :=
      convexHull_inter_section34CompactGraphSkeleton_subset_rim s.2.1 s.2.2.ge
        ⟨hw (ha.symm ▸ Finset.mem_singleton_self a),
          w.2.2.2 (subset_convexHull ℝ _ (ha.symm ▸ Finset.mem_singleton_self a))⟩
    have haL : ({a} : Finset E3) ∈ L.faces := by
      refine ⟨ha ▸ w.2.1, ?_⟩
      simpa only [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff] using haR
    exact ⟨⟨a, haL⟩, Subtype.ext ha.symm⟩
  have hN : ∀ w, src (.vertexBall w) ⊆ section34CompactCutNeighborhood src :=
    fun w => subset_iUnion (fun w => src (.vertexBall w)) w
  have hmeet : ∀ v v',
      section34CompactVertexBallImage src f₁ (wv v) ∩
        section34CompactVertexBallImage src f₁ (wv v') =
          f₁ '' (src (.vertexBall (wv v)) ∩ src (.vertexBall (wv v'))) := by
    intro v v'
    exact (hf₁.bijOn.injOn.image_inter (hN _) (hN _)).symm
  have hadj : ∀ v v' : L.vertices, v ≠ v' →
      ((SimplicialComplex.edgeGraph L).Adj v v' ↔
        (section34CompactVertexBallImage src f₁ (wv v) ∩
          section34CompactVertexBallImage src f₁ (wv v')).Nonempty) := by
    intro v v' hvv
    rw [hmeet, Set.image_nonempty]
    constructor
    · rintro ⟨-, hvL⟩
      let e : Section34CompactEdgeIndex K K' :=
        ⟨{(v : E3), (v' : E3)}, hvL.1,
          Finset.card_pair (fun h => hvv (Subtype.ext h)),
          hvL.2.trans (section34CompactSimplexRim_subset_graphSkeleton s.2.1 s.2.2.le)⟩
      obtain ⟨u, u', huu, heu, hDu⟩ := hends e
      have hepair : (e.1 : Set E3) = ((wv v).1 : Set E3) ∪ ((wv v').1 : Set E3) := by
        simp only [e, wv, Finset.coe_pair, Finset.coe_singleton, singleton_union]
      have hu : u.1 ⊆ e.1 := by
        rw [← Finset.coe_subset, heu]
        exact subset_union_left
      have hu' : u'.1 ⊆ e.1 := by
        rw [← Finset.coe_subset, heu]
        exact subset_union_right
      obtain ⟨x, hx⟩ := (hcell (.splitDisk e)).nonempty
      rw [hDu] at hx
      rcases eq_or_eq_of_section34CompactVertexIndex_subset e hepair hu with rfl | rfl <;>
        rcases eq_or_eq_of_section34CompactVertexIndex_subset e hepair hu' with rfl | rfl
      · exact (huu rfl).elim
      · exact ⟨x, hx⟩
      · exact ⟨x, hx.2, hx.1⟩
      · exact (huu rfl).elim
    · intro hnon
      obtain ⟨e, he⟩ := hcut.exists_splitDisk_eq_inter_vertexBall
        (fun h => hvv (hwvinj h)) hnon
      obtain ⟨x, hx⟩ := hnon
      have hxD : x ∈ src (.splitDisk e) := he.symm ▸ hx
      have hv := hvertexEdge (wv v) e ⟨x, hx.1, hxD⟩
      have hv' := hvertexEdge (wv v') e ⟨x, hx.2, hxD⟩
      have heq : ({(v : E3), (v' : E3)} : Finset E3) = e.1 := by
        apply Finset.eq_of_subset_of_card_le
        · exact Finset.insert_subset_iff.mpr
            ⟨Finset.singleton_subset_iff.mp hv, hv'⟩
        · rw [e.2.2.1, Finset.card_pair (fun h => hvv (Subtype.ext h))]
      refine ⟨hvv, ?_⟩
      rw [heq]
      refine ⟨e.2.1, fun y hy => ?_⟩
      apply convexHull_inter_section34CompactGraphSkeleton_subset_rim s.2.1 s.2.2.ge
      refine ⟨convexHull_min ?_ (convex_convexHull ℝ _) hy, e.2.2.2 hy⟩
      rw [← heq, Finset.coe_pair]
      exact insert_subset_iff.mpr
        ⟨(hwvinc v) (by simp [wv]),
          singleton_subset_iff.mpr ((hwvinc v') (by simp [wv]))⟩
  obtain ⟨g⟩ := (SimplicialComplex.edgeGraph L).exists_cycleGraphIsoOfConnectedDegreeTwo hconn hdeg
  have h3 := (SimplicialComplex.edgeGraph L).three_le_card_of_connected_degree_two hconn hdeg
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card L.vertices = n + 3 := ⟨Fintype.card L.vertices - 3, by omega⟩
  rw [hn] at g
  let v := wv ∘ g
  have hvinj : Function.Injective v := hwvinj.comp g.injective
  have hvsurj : ∀ w, Section34Incident w.1 s.1 ↔ ∃ i, v i = w := by
    intro w
    constructor
    · intro hw
      obtain ⟨a, rfl⟩ := hwvsurj w hw
      obtain ⟨i, rfl⟩ := g.surjective a
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact hwvinc (g i)
  have hadjv : ∀ i j, i ≠ j → ((SimpleGraph.cycleGraph (n + 3)).Adj i j ↔
      (section34CompactVertexBallImage src f₁ (v i) ∩
        section34CompactVertexBallImage src f₁ (v j)).Nonempty) := by
    intro i j hij
    exact g.map_adj_iff.symm.trans (hadj (g i) (g j) (fun h => hij (g.injective h)))
  have heinc : ∀ e : Section34CompactEdgeIndex K K',
      ∀ i j, i ≠ j → section34CompactSplitDiskImage src f₁ e =
        section34CompactVertexBallImage src f₁ (v i) ∩
          section34CompactVertexBallImage src f₁ (v j) → Section34Incident e.1 s.1 := by
    intro e i j hij heq
    obtain ⟨x, hx⟩ := (hcut.isPLCellOn_splitDiskImage hf₁ e).nonempty
    have hxij := heq.subset hx
    have hi := hcut.subset_of_mem_splitDiskImage hf₁ hx hxij.1
    have hj := hcut.subset_of_mem_splitDiskImage hf₁ hx hxij.2
    have hpair : (v i).1 ∪ (v j).1 = e.1 := by
      apply Finset.eq_of_subset_of_card_le (Finset.union_subset hi hj)
      have hdis : Disjoint (v i).1 (v j).1 := by
        rw [Finset.disjoint_left]
        intro a hai haj
        obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (v i).2.2.1
        obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (v j).2.2.1
        have he : b = c := (Finset.mem_singleton.mp (hb ▸ hai)).symm.trans
          (Finset.mem_singleton.mp (hc ▸ haj))
        exact hij (hvinj (Subtype.ext (hb.trans (he ▸ hc.symm))))
      rw [Finset.card_union_of_disjoint hdis, (v i).2.2.1, (v j).2.2.1, e.2.2.1]
    change (e.1 : Set E3) ⊆ convexHull ℝ (s.1 : Set E3)
    rw [← hpair, Finset.coe_union]
    exact union_subset (hwvinc (g i)) (hwvinc (g j))
  refine ⟨n, v, hvinj, hvsurj, hadjv, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hnon := (hadjv i j hij.ne).mp hij
    dsimp only [v, Function.comp_apply] at hnon
    rw [hmeet] at hnon
    obtain ⟨e, he⟩ := hcut.exists_splitDisk_eq_inter_vertexBall
      (fun h => hij.ne (hvinj h)) (Set.image_nonempty.mp hnon)
    have heq : section34CompactSplitDiskImage src f₁ e =
        section34CompactVertexBallImage src f₁ (v i) ∩
          section34CompactVertexBallImage src f₁ (v j) := by
      change f₁ '' src (.splitDisk e) = _
      rw [he]
      exact hf₁.bijOn.injOn.image_inter (hN _) (hN _)
    exact ⟨e, heinc e i j hij.ne heq, heq⟩
  · intro e he
    obtain ⟨a, b, hab, heab, hD⟩ := hcut.splitDiskImage_eq_inter hf₁ e
    have ha : Section34Incident a.1 s.1 := by
      apply Subset.trans ?_ he
      rw [heab]
      exact subset_union_left
    have hb : Section34Incident b.1 s.1 := by
      apply Subset.trans ?_ he
      rw [heab]
      exact subset_union_right
    obtain ⟨i, rfl⟩ := (hvsurj a).mp ha
    obtain ⟨j, rfl⟩ := (hvsurj b).mp hb
    have hij : i ≠ j := fun h => hab (congrArg v h)
    refine ⟨i, j, (hadjv i j hij).mpr ?_, hD⟩
    rw [← hD]
    exact (hcut.isPLCellOn_splitDiskImage hf₁ e).nonempty
  · intro i j k hij hik hjk
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨⟨hxi, hxj⟩, hxk⟩
    obtain ⟨e, hxe⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ (hvinj.ne hij) hxi hxj
    obtain ⟨a, b, -, hab, -⟩ := hcut.splitDiskImage_eq_inter hf₁ e
    have hcases : ∀ w, x ∈ section34CompactVertexBallImage src f₁ w → w = a ∨ w = b :=
      fun w hx => eq_or_eq_of_section34CompactVertexIndex_subset e hab
        (hcut.subset_of_mem_splitDiskImage hf₁ hxe hx)
    rcases hcases _ hxi with hi | hi <;> rcases hcases _ hxj with hj | hj <;>
      rcases hcases _ hxk with hk | hk
    all_goals first
      | exact hij (hvinj (hi.trans hj.symm))
      | exact hik (hvinj (hi.trans hk.symm))
      | exact hjk (hvinj (hj.trans hk.symm))
  · apply Subset.antisymm
    · exact iUnion_subset fun i x hx =>
        mem_iUnion₂.mpr ⟨⟨(s, v i), (hvsurj _).mpr ⟨i, rfl⟩⟩, rfl, hx⟩
    · intro x hx
      obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hx
      have hinc : Section34Incident a.1.2.1 s.1 := ha ▸ a.2
      obtain ⟨i, hi⟩ := (hvsurj _).mp hinc
      exact mem_iUnion.mpr ⟨i, hi.symm ▸ hxa⟩

end DifferentialGeometry.Topology.PiecewiseLinear

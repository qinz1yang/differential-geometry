import DifferentialGeometry.Topology.PiecewiseLinear.OneManifoldClassification
import DifferentialGeometry.Topology.SimplicialComplex.ConnectedSpace

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def graphComponentVertices (K : Geometry.SimplicialComplex ℝ E)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) : Set E :=
  ((↑) : K.vertices → E) '' c.supp

def graphComponentComplex (K : Geometry.SimplicialComplex ℝ E)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s ∈ K.faces | (s : Set E) ⊆ graphComponentVertices K c}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hsc⟩
    refine ⟨K.nonempty_of_mem_faces hs, fun t hts ht => ⟨K.down_closed hs hts ht, ?_⟩⟩
    exact (Finset.coe_subset.mpr hts).trans hsc
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

theorem mem_graphComponentComplex_faces_iff (K : Geometry.SimplicialComplex ℝ E)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) {s : Finset E} :
    s ∈ (graphComponentComplex K c).faces ↔
      s ∈ K.faces ∧ (s : Set E) ⊆ graphComponentVertices K c :=
  Iff.rfl

theorem graphComponentComplex_faces_subset (K : Geometry.SimplicialComplex ℝ E)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) :
    (graphComponentComplex K c).faces ⊆ K.faces :=
  fun _ hs => hs.1

theorem graphComponentComplex_faces_finite (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) :
    (graphComponentComplex K c).faces.Finite :=
  Set.toFinite K.faces |>.subset (graphComponentComplex_faces_subset K c)

def graphComponentVertex (K : Geometry.SimplicialComplex ℝ E)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent)
    (v : c.supp) : (graphComponentComplex K c).vertices := by
  refine ⟨v.1, v.1.2, ?_⟩
  intro x hx
  have hxv : x = (v.1 : E) := by simpa using hx
  subst x
  exact ⟨v.1, v.2, rfl⟩

theorem graphComponentVertex_injective (K : Geometry.SimplicialComplex ℝ E)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) :
    Function.Injective (graphComponentVertex K c) := by
  intro u v huv
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : (graphComponentComplex K c).vertices => (z : E)) huv

theorem graphComponentVertex_surjective (K : Geometry.SimplicialComplex ℝ E)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) :
    Function.Surjective (graphComponentVertex K c) := by
  intro v
  have hv : (v : E) ∈ graphComponentVertices K c := v.2.2 (by simp)
  obtain ⟨w, hwc, hwv⟩ := hv
  refine ⟨⟨w, hwc⟩, ?_⟩
  apply Subtype.ext
  exact hwv

noncomputable def graphComponentVertexEquiv (K : Geometry.SimplicialComplex ℝ E)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) :
    c.supp ≃ (graphComponentComplex K c).vertices :=
  Equiv.ofBijective (graphComponentVertex K c)
    ⟨graphComponentVertex_injective K c, graphComponentVertex_surjective K c⟩

noncomputable def graphComponentNeighborEquiv (K : Geometry.SimplicialComplex ℝ E)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) (v : c.supp) :
    c.toSimpleGraph.neighborSet v ≃
      (SimplicialComplex.edgeGraph K).neighborSet v.1 where
  toFun w := ⟨w.1.1, w.2⟩
  invFun w := ⟨⟨w.1, c.mem_supp_of_adj_mem_supp v.2 w.2⟩, w.2⟩
  left_inv w := Subtype.ext (Subtype.ext (rfl : w.1.1 = w.1.1))
  right_inv w := Subtype.ext (rfl : w.1 = w.1)

open Classical in
noncomputable def graphComponentEdgeGraphIso (K : Geometry.SimplicialComplex ℝ E)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) :
    c.toSimpleGraph ≃g SimplicialComplex.edgeGraph (graphComponentComplex K c) where
  toEquiv := graphComponentVertexEquiv K c
  map_rel_iff' := by
    intro u v
    change (SimplicialComplex.edgeGraph (graphComponentComplex K c)).Adj
        (graphComponentVertex K c u) (graphComponentVertex K c v) ↔
      c.toSimpleGraph.Adj u v
    rw [c.toSimpleGraph_adj u.2 v.2]
    constructor
    · intro huv
      refine ⟨?_, huv.2.1⟩
      intro h
      apply huv.1
      apply Subtype.ext
      exact congrArg (fun z : K.vertices => (z : E)) h
    · intro huv
      refine ⟨?_, ⟨huv.2, ?_⟩⟩
      · intro h
        apply huv.1
        apply Subtype.ext
        exact congrArg (fun z : (graphComponentComplex K c).vertices => (z : E)) h
      · intro x hx
        simp only [Finset.coe_pair, mem_insert_iff, mem_singleton_iff] at hx
        rcases hx with hx | hx
        · exact ⟨u.1, u.2, hx.symm⟩
        · exact ⟨v.1, v.2, hx.symm⟩

theorem edgeGraph_graphComponentComplex_connected (K : Geometry.SimplicialComplex ℝ E)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) :
    (SimplicialComplex.edgeGraph (graphComponentComplex K c)).Connected :=
  (graphComponentEdgeGraphIso K c).connected_iff.mp c.connected_toSimpleGraph

open Classical in
theorem graphComponentEdgeGraph_neighborSet_ncard (K : Geometry.SimplicialComplex ℝ E)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) (v : c.supp) :
    ((SimplicialComplex.edgeGraph (graphComponentComplex K c)).neighborSet
        (graphComponentVertex K c v)).ncard =
      ((SimplicialComplex.edgeGraph K).neighborSet v.1).ncard := by
  calc
    ((SimplicialComplex.edgeGraph (graphComponentComplex K c)).neighborSet
        (graphComponentVertex K c v)).ncard =
        (c.toSimpleGraph.neighborSet v).ncard :=
      (Set.ncard_congr' ((graphComponentEdgeGraphIso K c).mapNeighborSet v)).symm
    _ = ((SimplicialComplex.edgeGraph K).neighborSet v.1).ncard :=
      Set.ncard_congr' (graphComponentNeighborEquiv K c v)

open Classical in
theorem graphComponentComplex_isManifoldWithBoundary
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 1 K)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) :
    IsCombinatorialManifoldWithBoundary 1 (graphComponentComplex K c) := by
  let _ : Finite (graphComponentComplex K c).faces :=
    (graphComponentComplex_faces_finite K c).to_subtype
  apply (isCombinatorialManifoldWithBoundary_one_iff (graphComponentComplex K c)).mpr
  refine ⟨fun s hs => hK.card_le K hs.1, ?_⟩
  intro x hx
  let v : (graphComponentComplex K c).vertices := ⟨x, hx⟩
  let w : c.supp := (graphComponentVertexEquiv K c).symm v
  have hvw : graphComponentVertex K c w = v :=
    (graphComponentVertexEquiv K c).apply_symm_apply v
  have hdegree := (isCombinatorialManifoldWithBoundary_one_iff K).mp hK |>.2 w.1 w.1.2
  have hdegree' :
      ((SimplicialComplex.edgeGraph K).neighborSet w.1).ncard = 1 ∨
        ((SimplicialComplex.edgeGraph K).neighborSet w.1).ncard = 2 := by
    rw [SimplicialComplex.ncard_neighborSet_edgeGraph]
    exact hdegree.imp Set.ncard_eq_one.mpr Set.ncard_eq_two.mpr
  have htransfer :
      ((SimplicialComplex.edgeGraph (graphComponentComplex K c)).neighborSet v).ncard =
        ((SimplicialComplex.edgeGraph K).neighborSet w.1).ncard := by
    rw [← hvw]
    exact graphComponentEdgeGraph_neighborSet_ncard K c w
  rw [← htransfer, SimplicialComplex.ncard_neighborSet_edgeGraph] at hdegree'
  exact hdegree'.imp Set.ncard_eq_one.mp Set.ncard_eq_two.mp

open Classical in
theorem graphComponentComplex_isPLSphere_or_isPLBall
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 1 K)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) :
    IsPLSphere 1 (graphComponentComplex K c).space ∨
      IsPLBall 1 (graphComponentComplex K c).space := by
  let _ : Finite (graphComponentComplex K c).faces :=
    (graphComponentComplex_faces_finite K c).to_subtype
  let G := SimplicialComplex.edgeGraph (graphComponentComplex K c)
  by_cases hleaf : ∃ v, (G.neighborSet v).ncard = 1
  · exact Or.inr <| isPLBall_one_of_edgeGraph_connected_of_exists_degree_one
      (graphComponentComplex K c) (graphComponentComplex_isManifoldWithBoundary K hK c)
        (edgeGraph_graphComponentComplex_connected K c) hleaf
  · apply Or.inl
    apply isPLSphere_one_of_edgeGraph_connected (graphComponentComplex K c)
    · apply (isCombinatorialManifold_one_iff (graphComponentComplex K c)).mpr
      refine ⟨fun s hs => (graphComponentComplex_isManifoldWithBoundary K hK c).card_le _ hs,
        ?_⟩
      intro x hx
      have hdegree :=
        (isCombinatorialManifoldWithBoundary_one_iff (graphComponentComplex K c)).mp
          (graphComponentComplex_isManifoldWithBoundary K hK c) |>.2 x hx
      rcases hdegree with hdegree | hdegree
      · exfalso
        apply hleaf
        refine ⟨⟨x, hx⟩, ?_⟩
        rw [SimplicialComplex.ncard_neighborSet_edgeGraph]
        exact Set.ncard_eq_one.mpr hdegree
      · exact hdegree
    · exact edgeGraph_graphComponentComplex_connected K c

theorem graphComponentComplex_space_subset (K : Geometry.SimplicialComplex ℝ E)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) :
    (graphComponentComplex K c).space ⊆ K.space :=
  space_mono_of_faces_subset (graphComponentComplex_faces_subset K c)

open Classical in
theorem space_eq_iUnion_graphComponentComplex (K : Geometry.SimplicialComplex ℝ E) :
    K.space = ⋃ c : (SimplicialComplex.edgeGraph K).ConnectedComponent,
      (graphComponentComplex K c).space := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
    obtain ⟨u, hus⟩ := K.nonempty_of_mem_faces hs
    have hu : u ∈ K.vertices :=
      K.down_closed hs (Finset.singleton_subset_iff.mpr hus) (Finset.singleton_nonempty u)
    let c := (SimplicialComplex.edgeGraph K).connectedComponentMk ⟨u, hu⟩
    apply mem_iUnion.mpr
    refine ⟨c, (graphComponentComplex K c).convexHull_subset_space ⟨hs, ?_⟩ hxs⟩
    intro w hws
    have hw : w ∈ K.vertices :=
      K.down_closed hs (Finset.singleton_subset_iff.mpr hws) (Finset.singleton_nonempty w)
    have hwc : (⟨w, hw⟩ : K.vertices) ∈ c.supp := by
      by_cases hwu : w = u
      · subst w
        exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      · apply c.mem_supp_of_adj_mem_supp
          SimpleGraph.ConnectedComponent.connectedComponentMk_mem
        refine ⟨fun h => hwu (congrArg Subtype.val h).symm, ?_⟩
        apply K.down_closed hs
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          exact hz.elim (fun h => h ▸ hus) (fun h => h ▸ hws)
        · simp
    exact ⟨⟨w, hw⟩, hwc, rfl⟩
  · apply iUnion_subset
    intro c
    exact graphComponentComplex_space_subset K c

open Classical in
theorem pairwise_disjoint_graphComponentComplex_space
    (K : Geometry.SimplicialComplex ℝ E) :
    Pairwise fun c d : (SimplicialComplex.edgeGraph K).ConnectedComponent =>
      Disjoint (graphComponentComplex K c).space (graphComponentComplex K d).space := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro x hxc hxd
  obtain ⟨s, hs, hxs⟩ := (graphComponentComplex K c).mem_space_iff.mp hxc
  obtain ⟨t, ht, hxt⟩ := (graphComponentComplex K d).mem_space_iff.mp hxd
  have hxst : x ∈ convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) := ⟨hxs, hxt⟩
  have hxinter := K.inter_subset_convexHull hs.1 ht.1 hxst
  obtain ⟨w, hws, hwt⟩ := convexHull_nonempty_iff.mp ⟨x, hxinter⟩
  obtain ⟨v, hvc, hvw⟩ := hs.2 hws
  obtain ⟨z, hzd, hzw⟩ := ht.2 hwt
  have hvz : v = z := Subtype.ext (hvw.trans hzw.symm)
  subst z
  exact hcd (SimpleGraph.ConnectedComponent.eq_of_common_vertex hvc hzd)

theorem graphComponentComplex_space_isConnected (K : Geometry.SimplicialComplex ℝ E)
    (c : (SimplicialComplex.edgeGraph K).ConnectedComponent) :
    IsConnected (graphComponentComplex K c).space :=
  isConnected_space_of_edgeGraph_connected (graphComponentComplex K c)
    (edgeGraph_graphComponentComplex_connected K c)

open Classical in
theorem exists_finite_isPLSphere_or_isPLBall_decomposition
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 1 K) :
    ∃ C : Set (Set E), C.Finite ∧
      (∀ S ∈ C, IsPLSphere 1 S ∨ IsPLBall 1 S) ∧
      C.PairwiseDisjoint id ∧ K.space = ⋃₀ C := by
  let _ : Finite K.vertices := (SimplicialComplex.finite_vertices K).to_subtype
  let F := fun c : (SimplicialComplex.edgeGraph K).ConnectedComponent =>
    (graphComponentComplex K c).space
  refine ⟨range F, Set.finite_range _, ?_, ?_, ?_⟩
  · rintro S ⟨c, rfl⟩
    exact graphComponentComplex_isPLSphere_or_isPLBall K hK c
  · rintro S ⟨c, rfl⟩ T ⟨d, rfl⟩ hne
    exact pairwise_disjoint_graphComponentComplex_space K
      (fun hcd => hne (congrArg F hcd))
  · simpa only [sUnion_range] using space_eq_iUnion_graphComponentComplex K

end DifferentialGeometry.Topology.PiecewiseLinear

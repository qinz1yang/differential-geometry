import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.NormalCell
import DifferentialGeometry.Topology.PiecewiseLinear.OneManifoldClassification
import DifferentialGeometry.Topology.SimplicialComplex.ConnectedSpace

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

namespace NormalSingularSetTriangulation

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM : Set M}

def branchVertices (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    Set (EuclideanSpace ℝ (Fin T.piece.ambientDim)) :=
  ((↑) : T.complex.vertices → EuclideanSpace ℝ (Fin T.piece.ambientDim)) '' c.supp

def branchComplex (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin T.piece.ambientDim)) where
  faces := {s ∈ T.complex.faces | (s : Set _) ⊆ T.branchVertices c}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hsc⟩
    refine ⟨T.complex.nonempty_of_mem_faces hs, fun t hts ht => ⟨T.complex.down_closed hs hts ht, ?_⟩⟩
    exact (Finset.coe_subset.mpr hts).trans hsc
  indep hs := T.complex.indep hs.1
  inter_subset_convexHull hs ht := T.complex.inter_subset_convexHull hs.1 ht.1

theorem mem_branchComplex_faces_iff
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) {s : Finset _} :
    s ∈ (T.branchComplex c).faces ↔
      s ∈ T.complex.faces ∧ (s : Set _) ⊆ T.branchVertices c :=
  Iff.rfl

theorem branchComplex_faces_subset
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    (T.branchComplex c).faces ⊆ T.complex.faces :=
  fun _ hs => hs.1

theorem branchComplex_faces_finite
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    (T.branchComplex c).faces.Finite :=
  T.finite_faces.subset (T.branchComplex_faces_subset c)

def branchVertex (T : NormalSingularSetTriangulation D BdM) (c : T.Branch)
    (v : c.supp) : (T.branchComplex c).vertices := by
  refine ⟨v.1, v.1.2, ?_⟩
  intro x hx
  have hxv : x = (v.1 : EuclideanSpace ℝ (Fin T.piece.ambientDim)) := by simpa using hx
  subst x
  exact ⟨v.1, v.2, rfl⟩

theorem branchVertex_injective
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    Function.Injective (T.branchVertex c) := by
  intro u v huv
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun z : (T.branchComplex c).vertices =>
      (z : EuclideanSpace ℝ (Fin T.piece.ambientDim))) huv

theorem branchVertex_surjective
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    Function.Surjective (T.branchVertex c) := by
  intro v
  have hv : (v : EuclideanSpace ℝ (Fin T.piece.ambientDim)) ∈ T.branchVertices c :=
    v.2.2 (by simp)
  obtain ⟨w, hwc, hwv⟩ := hv
  refine ⟨⟨w, hwc⟩, ?_⟩
  apply Subtype.ext
  exact hwv

noncomputable def branchVertexEquiv
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    c.supp ≃ (T.branchComplex c).vertices :=
  Equiv.ofBijective (T.branchVertex c) ⟨T.branchVertex_injective c, T.branchVertex_surjective c⟩

@[simp]
theorem branchVertexEquiv_apply
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) (v : c.supp) :
    T.branchVertexEquiv c v = T.branchVertex c v :=
  rfl

noncomputable def connectedComponentNeighborEquiv
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) (v : c.supp) :
    c.toSimpleGraph.neighborSet v ≃
      (SimplicialComplex.edgeGraph T.complex).neighborSet v.1 where
  toFun w := ⟨w.1.1, w.2⟩
  invFun w :=
    ⟨⟨w.1, c.mem_supp_of_adj_mem_supp v.2 w.2⟩, w.2⟩
  left_inv w := Subtype.ext (Subtype.ext (rfl : w.1.1 = w.1.1))
  right_inv w := Subtype.ext (rfl : w.1 = w.1)

open Classical in
noncomputable def branchEdgeGraphIso
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    c.toSimpleGraph ≃g SimplicialComplex.edgeGraph (T.branchComplex c) where
  toEquiv := T.branchVertexEquiv c
  map_rel_iff' := by
    intro u v
    change (SimplicialComplex.edgeGraph (T.branchComplex c)).Adj
        (T.branchVertex c u) (T.branchVertex c v) ↔ c.toSimpleGraph.Adj u v
    rw [c.toSimpleGraph_adj u.2 v.2]
    constructor
    · intro huv
      refine ⟨?_, huv.2.1⟩
      intro h
      apply huv.1
      apply Subtype.ext
      exact congrArg
        (fun z : T.complex.vertices =>
          (z : EuclideanSpace ℝ (Fin T.piece.ambientDim))) h
    · intro huv
      refine ⟨?_, ⟨huv.2, ?_⟩⟩
      · intro h
        apply huv.1
        apply Subtype.ext
        exact congrArg
          (fun z : (T.branchComplex c).vertices =>
            (z : EuclideanSpace ℝ (Fin T.piece.ambientDim))) h
      · intro x hx
        simp only [Finset.coe_pair, mem_insert_iff, mem_singleton_iff] at hx
        rcases hx with hx | hx
        · exact ⟨u.1, u.2, hx.symm⟩
        · exact ⟨v.1, v.2, hx.symm⟩

theorem edgeGraph_branchComplex_connected
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    (SimplicialComplex.edgeGraph (T.branchComplex c)).Connected :=
  (T.branchEdgeGraphIso c).connected_iff.mp c.connected_toSimpleGraph

open Classical in
theorem branchEdgeGraph_neighborSet_ncard
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) (v : c.supp) :
    ((SimplicialComplex.edgeGraph (T.branchComplex c)).neighborSet (T.branchVertex c v)).ncard =
      ((SimplicialComplex.edgeGraph T.complex).neighborSet v.1).ncard := by
  calc
    ((SimplicialComplex.edgeGraph (T.branchComplex c)).neighborSet
        (T.branchVertex c v)).ncard =
        (c.toSimpleGraph.neighborSet v).ncard :=
      (Set.ncard_congr' ((T.branchEdgeGraphIso c).mapNeighborSet v)).symm
    _ = ((SimplicialComplex.edgeGraph T.complex).neighborSet v.1).ncard :=
      Set.ncard_congr' (T.connectedComponentNeighborEquiv c v)

open Classical in
theorem branchComplex_isManifoldWithBoundary
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    IsCombinatorialManifoldWithBoundary 1 (T.branchComplex c) := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  let _ : Finite (T.branchComplex c).faces := (T.branchComplex_faces_finite c).to_subtype
  apply (isCombinatorialManifoldWithBoundary_one_iff (T.branchComplex c)).mpr
  refine ⟨fun s hs => T.isManifoldWithBoundary.card_le T.complex hs.1, ?_⟩
  intro x hx
  let v : (T.branchComplex c).vertices := ⟨x, hx⟩
  let w : c.supp := (T.branchVertexEquiv c).symm v
  have hvw : T.branchVertex c w = v := (T.branchVertexEquiv c).apply_symm_apply v
  have hdegree := T.neighborSet_ncard_eq_one_or_two w.1
  have htransfer :
      ((SimplicialComplex.edgeGraph (T.branchComplex c)).neighborSet v).ncard =
        ((SimplicialComplex.edgeGraph T.complex).neighborSet w.1).ncard := by
    rw [← hvw]
    exact T.branchEdgeGraph_neighborSet_ncard c w
  rw [← htransfer] at hdegree
  rw [SimplicialComplex.ncard_neighborSet_edgeGraph] at hdegree
  exact hdegree.imp Set.ncard_eq_one.mp Set.ncard_eq_two.mp

open Classical in
theorem branchComplex_isManifold
    (T : NormalSingularSetTriangulation D BdM) {c : T.Branch}
    (hc : ¬T.IsBoundaryBranch c) :
    IsCombinatorialManifold 1 (T.branchComplex c) := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  let _ : Finite (T.branchComplex c).faces := (T.branchComplex_faces_finite c).to_subtype
  apply (isCombinatorialManifold_one_iff (T.branchComplex c)).mpr
  refine ⟨fun s hs => T.isManifoldWithBoundary.card_le T.complex hs.1, ?_⟩
  intro x hx
  let v : (T.branchComplex c).vertices := ⟨x, hx⟩
  let w : c.supp := (T.branchVertexEquiv c).symm v
  have hvw : T.branchVertex c w = v := (T.branchVertexEquiv c).apply_symm_apply v
  have hdegree := T.neighborSet_ncard_eq_two_of_not_isBoundaryBranch hc w.2
  have htransfer :
      ((SimplicialComplex.edgeGraph (T.branchComplex c)).neighborSet v).ncard =
        ((SimplicialComplex.edgeGraph T.complex).neighborSet w.1).ncard := by
    rw [← hvw]
    exact T.branchEdgeGraph_neighborSet_ncard c w
  rw [← htransfer, SimplicialComplex.ncard_neighborSet_edgeGraph] at hdegree
  exact Set.ncard_eq_two.mp hdegree

theorem branchComplex_space_isConnected
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    IsConnected (T.branchComplex c).space :=
  isConnected_space_of_edgeGraph_connected (T.branchComplex c)
    (T.edgeGraph_branchComplex_connected c)

open Classical in
theorem branchComplex_isPLSphere
    (T : NormalSingularSetTriangulation D BdM) {c : T.Branch}
    (hc : ¬T.IsBoundaryBranch c) :
    IsPLSphere 1 (T.branchComplex c).space := by
  let _ : Finite (T.branchComplex c).faces := (T.branchComplex_faces_finite c).to_subtype
  exact isPLSphere_one_of_edgeGraph_connected (T.branchComplex c)
    (T.branchComplex_isManifold hc) (T.edgeGraph_branchComplex_connected c)

open Classical in
theorem branchComplex_isPLBall
    (T : NormalSingularSetTriangulation D BdM) {c : T.Branch}
    (hc : T.IsBoundaryBranch c) :
    IsPLBall 1 (T.branchComplex c).space := by
  let _ : Finite (T.branchComplex c).faces := (T.branchComplex_faces_finite c).to_subtype
  apply isPLBall_one_of_edgeGraph_connected_of_exists_degree_one (T.branchComplex c)
    (T.branchComplex_isManifoldWithBoundary c) (T.edgeGraph_branchComplex_connected c)
  obtain ⟨v, hvc, hdegree⟩ := T.exists_degree_one_vertex_of_isBoundaryBranch hc
  let w : c.supp := ⟨v, hvc⟩
  refine ⟨T.branchVertex c w, ?_⟩
  rw [T.branchEdgeGraph_neighborSet_ncard c w]
  exact hdegree

open Classical in
theorem branchComplex_space_isPolyhedron
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    IsPolyhedron (T.branchComplex c).space := by
  let _ : Finite (T.branchComplex c).faces := (T.branchComplex_faces_finite c).to_subtype
  exact isPolyhedron_space (T.branchComplex c)

def branchCarrier (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) : Set M :=
  T.piece.piece.map '' (T.branchComplex c).space

theorem branchComplex_space_subset
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    (T.branchComplex c).space ⊆ T.complex.space :=
  space_mono_of_faces_subset (T.branchComplex_faces_subset c)

theorem branchComplex_space_subset_piece
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    (T.branchComplex c).space ⊆ T.piece.piece.complex.space :=
  space_mono_of_faces_subset ((T.branchComplex_faces_subset c).trans T.faces_subset)

open Classical in
theorem space_eq_iUnion_branchComplex
    (T : NormalSingularSetTriangulation D BdM) :
    T.complex.space = ⋃ c : T.Branch, (T.branchComplex c).space := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := T.complex.mem_space_iff.mp hx
    obtain ⟨u, hus⟩ := T.complex.nonempty_of_mem_faces hs
    have hu : u ∈ T.complex.vertices :=
      T.complex.down_closed hs (Finset.singleton_subset_iff.mpr hus)
        (Finset.singleton_nonempty u)
    let c : T.Branch :=
      (SimplicialComplex.edgeGraph T.complex).connectedComponentMk ⟨u, hu⟩
    apply mem_iUnion.mpr
    refine ⟨c, (T.branchComplex c).convexHull_subset_space ⟨hs, ?_⟩ hxs⟩
    intro w hws
    have hw : w ∈ T.complex.vertices :=
      T.complex.down_closed hs (Finset.singleton_subset_iff.mpr hws)
        (Finset.singleton_nonempty w)
    have hwc : (⟨w, hw⟩ : T.complex.vertices) ∈ c.supp := by
      by_cases hwu : w = u
      · subst w
        exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      · apply c.mem_supp_of_adj_mem_supp
          SimpleGraph.ConnectedComponent.connectedComponentMk_mem
        refine ⟨fun h => hwu (congrArg Subtype.val h).symm, ?_⟩
        apply T.complex.down_closed hs
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          exact hz.elim (fun h => h ▸ hus) (fun h => h ▸ hws)
        · simp
    exact ⟨⟨w, hw⟩, hwc, rfl⟩
  · apply iUnion_subset
    intro c
    exact T.branchComplex_space_subset c

open Classical in
theorem pairwise_disjoint_branchComplex_space
    (T : NormalSingularSetTriangulation D BdM) :
    Pairwise fun c d : T.Branch => Disjoint (T.branchComplex c).space (T.branchComplex d).space := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro x hxc hxd
  obtain ⟨s, hs, hxs⟩ := (T.branchComplex c).mem_space_iff.mp hxc
  obtain ⟨t, ht, hxt⟩ := (T.branchComplex d).mem_space_iff.mp hxd
  have hxst : x ∈ convexHull ℝ (s : Set _) ∩ convexHull ℝ (t : Set _) := ⟨hxs, hxt⟩
  have hxinter := T.complex.inter_subset_convexHull hs.1 ht.1 hxst
  obtain ⟨w, hws, hwt⟩ := convexHull_nonempty_iff.mp ⟨x, hxinter⟩
  obtain ⟨v, hvc, hvw⟩ := hs.2 hws
  obtain ⟨z, hzd, hzw⟩ := ht.2 hwt
  have hvz : v = z := Subtype.ext (hvw.trans hzw.symm)
  subst z
  exact hcd (SimpleGraph.ConnectedComponent.eq_of_common_vertex hvc hzd)

theorem branchCarrier_subset_doublePointSet
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    T.branchCarrier c ⊆ doublePointSet D D.domain := by
  rw [← T.map_space]
  exact image_mono (T.branchComplex_space_subset c)

theorem branchCarrier_isConnected
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    IsConnected (T.branchCarrier c) :=
  (T.branchComplex_space_isConnected c).image T.piece.piece.map
    (T.piece.piece.continuousOn.mono (T.branchComplex_space_subset_piece c))

theorem iUnion_branchCarrier
    (T : NormalSingularSetTriangulation D BdM) :
    ⋃ c : T.Branch, T.branchCarrier c = doublePointSet D D.domain := by
  apply Subset.antisymm
  · apply iUnion_subset
    intro c
    exact T.branchCarrier_subset_doublePointSet c
  · intro y hy
    have hyimage : y ∈ T.piece.piece.map '' T.complex.space := by
      rw [T.map_space]
      exact hy
    obtain ⟨x, hx, rfl⟩ := hyimage
    rw [T.space_eq_iUnion_branchComplex] at hx
    obtain ⟨c, hxc⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨c, ⟨x, hxc, rfl⟩⟩

theorem pairwise_disjoint_branchCarrier
    (T : NormalSingularSetTriangulation D BdM) :
    Pairwise fun c d : T.Branch => Disjoint (T.branchCarrier c) (T.branchCarrier d) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hxc, rfl⟩ ⟨z, hzd, hzx⟩
  have hxz : x = z := T.piece.piece.bijOn.injOn
    (T.branchComplex_space_subset_piece c hxc)
    (T.branchComplex_space_subset_piece d hzd) hzx.symm
  subst z
  exact Set.disjoint_left.mp (T.pairwise_disjoint_branchComplex_space hcd) hxc hzd

def branchSet (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    Set (doublePointSet D D.domain) :=
  ((↑) : doublePointSet D D.domain → M) ⁻¹' T.branchCarrier c

theorem iUnion_branchSet
    (T : NormalSingularSetTriangulation D BdM) :
    ⋃ c : T.Branch, T.branchSet c = univ := by
  apply eq_univ_iff_forall.mpr
  intro y
  have hy : (y : M) ∈ ⋃ c : T.Branch, T.branchCarrier c := by
    rw [T.iUnion_branchCarrier]
    exact y.2
  obtain ⟨c, hyc⟩ := mem_iUnion.mp hy
  exact mem_iUnion.mpr ⟨c, hyc⟩

theorem pairwise_disjoint_branchSet
    (T : NormalSingularSetTriangulation D BdM) :
    Pairwise fun c d : T.Branch => Disjoint (T.branchSet c) (T.branchSet d) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro y hyc hyd
  exact Set.disjoint_left.mp (T.pairwise_disjoint_branchCarrier hcd) hyc hyd

theorem image_branchSet
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    ((↑) : doublePointSet D D.domain → M) '' T.branchSet c = T.branchCarrier c := by
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact hy
  · intro y hy
    exact ⟨⟨y, T.branchCarrier_subset_doublePointSet c hy⟩, hy, rfl⟩

theorem branchSet_isConnected
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    IsConnected (T.branchSet c) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy⟩ := (T.branchCarrier_isConnected c).nonempty
    exact ⟨⟨y, T.branchCarrier_subset_doublePointSet c hy⟩, hy⟩
  · apply IsInducing.subtypeVal.isPreconnected_image.mp
    rw [T.image_branchSet c]
    exact (T.branchCarrier_isConnected c).isPreconnected

end NormalSingularSetTriangulation

end DifferentialGeometry.Topology.PiecewiseLinear

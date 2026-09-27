import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSubcomplexComplement
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorConnected
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem preconnected_left_of_closed_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hunion : IsPreconnected (A ∪ B)) (hinter : IsConnected (A ∩ B)) : IsPreconnected A := by
  apply isPreconnected_iff_subset_of_disjoint_closed.mpr
  intro P Q hP hQ hcover hdis
  have hcase {P Q : Set X} (hP : IsClosed P) (hQ : IsClosed Q)
      (hcover : A ⊆ P ∪ Q) (hdis : A ∩ (P ∩ Q) = ∅) (hJP : A ∩ B ⊆ P) : A ⊆ P := by
    have hcover' : A ∪ B ⊆ (A ∩ P ∪ B) ∪ (A ∩ Q) := by
      rintro x (hxA | hxB)
      · rcases hcover hxA with hxP | hxQ
        · exact Or.inl (Or.inl ⟨hxA, hxP⟩)
        · exact Or.inr ⟨hxA, hxQ⟩
      · exact Or.inl (Or.inr hxB)
    have hdis' : (A ∪ B) ∩ ((A ∩ P ∪ B) ∩ (A ∩ Q)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨-, hxP | hxB, hxQ⟩
      · exact (hdis.subset ⟨hxP.1, hxP.2, hxQ.2⟩).elim
      · exact (hdis.subset ⟨hxQ.1, hJP ⟨hxQ.1, hxB⟩, hxQ.2⟩).elim
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hunion
        (A ∩ P ∪ B) (A ∩ Q) ((hA.inter hP).union hB) (hA.inter hQ) hcover' hdis' with h | h
    · intro x hx
      rcases h (Or.inl hx) with hxP | hxB
      · exact hxP.2
      · exact hJP ⟨hx, hxB⟩
    · obtain ⟨x, hxA, hxB⟩ := hinter.nonempty
      exact False.elim ((hdis.subset ⟨hxA, hJP ⟨hxA, hxB⟩, (h (Or.inl hxA)).2⟩).elim)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hinter.isPreconnected P Q hP hQ
      (inter_subset_left.trans hcover) (by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact (hdis.subset ⟨hx.1.1, hx.2⟩).elim) with h | h
  · exact Or.inl (hcase hP hQ hcover hdis h)
  · exact Or.inr (hcase hQ hP (by simpa only [union_comm] using hcover)
      (by simpa only [inter_comm P Q] using hdis) h)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifold.isConnected_sdiff_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space)
    {D : Set E} (hD : IsPLBall 2 D) (hDK : D ⊆ K.space) : IsConnected (K.space \ D) := by
  classical
  obtain ⟨r, hr⟩ := hD
  let A := closure (K.space \ D)
  let J := r '' stdSimplexBoundary 2
  have hmeet : D ∩ A = J := hK.inter_closure_sdiff_eq_image_stdSimplexBoundary K hr hDK
  have hAS : A ⊆ K.space := closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  have hcover : A ∪ D = K.space := by
    apply Subset.antisymm (union_subset hAS hDK)
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inr hxD
    · exact Or.inl (subset_closure ⟨hx, hxD⟩)
  have hJ : IsConnected J := hr.isPLSphere_image_stdSimplexBoundary.isConnected
  have hA : IsConnected A := by
    refine ⟨hJ.nonempty.mono (hmeet.symm.subset.trans inter_subset_right), ?_⟩
    apply preconnected_left_of_closed_union isClosed_closure
      (show IsPLBall 2 D from ⟨r, hr⟩).isPolyhedron.isClosed (hcover.symm ▸ hconn.isPreconnected)
    rwa [inter_comm, hmeet]
  obtain ⟨T, hTfin, hTD⟩ := (show IsPLBall 2 D from ⟨r, hr⟩).isPolyhedron.exists_simplicialComplex
  let _ : Finite T.faces := hTfin.to_subtype
  have hT : IsPLBall 2 T.space := hTD.symm ▸ (show IsPLBall 2 D from ⟨r, hr⟩)
  obtain ⟨R, hRfin, hR, hRA, hRJ⟩ :=
    hK.exists_isCombinatorialManifoldWithBoundary_closure_sdiff_two
      hT.isCombinatorialManifoldWithBoundary (hTD.subset.trans hDK)
  let _ : Finite R.faces := hRfin.to_subtype
  rw [hTD] at hRA
  have hboundary : (boundaryComplex 2 T).space = J := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex T (hTD.symm ▸ hr),
      simplexBoundary_stdVertices_space]
  rw [hboundary] at hRJ
  have hRconn : IsConnected R.space := hRA.symm ▸ hA
  have hcore := hR.isConnected_sdiff_boundaryComplex_space hRconn
  rw [hRA, hRJ] at hcore
  have heq : A \ J = K.space \ D := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨hAS hx.1, fun hxD => hx.2 (hmeet.subset ⟨hxD, hx.1⟩)⟩
    · intro x hx
      exact ⟨subset_closure hx, fun hxJ => hx.2 (hmeet.symm.subset hxJ).1⟩
  exact heq ▸ hcore

theorem IsCombinatorialManifold.inter_eq_disk_of_frontier_inter_subset
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space)
    {C D : Set E} (hD : IsPLBall 2 D) (hDK : D ⊆ K.space) (hDC : D ⊆ C)
    (hfront : frontier C ∩ K.space ⊆ D) (hout : (K.space \ C).Nonempty) :
    K.space ∩ C = D := by
  have hc := (hK.isConnected_sdiff_disk K hconn hD hDK).isPreconnected
  have havoid : Disjoint (K.space \ D) (frontier Cᶜ) := by
    rw [frontier_compl]
    exact disjoint_left.mpr fun x hx hxC => hx.2 (hfront ⟨hxC, hx.1⟩)
  obtain ⟨x, hxK, hxC⟩ := hout
  have hsub : K.space \ D ⊆ Cᶜ := IsPreconnected.subset_of_disjoint_frontier hc
    ⟨x, ⟨hxK, fun hxD => hxC (hDC hxD)⟩, hxC⟩ havoid
  apply Subset.antisymm
  · intro y hy
    by_contra hyD
    exact hsub ⟨hy.1, hyD⟩ hy.2
  · exact subset_inter hDK hDC

end DifferentialGeometry.Topology.PiecewiseLinear

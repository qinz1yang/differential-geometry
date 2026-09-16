import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronLocalConnectedness
import DifferentialGeometry.Topology.Connected.TwoSided

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.closure_interior_preimage {n : ℕ}
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hA : IsCombinatorialManifoldWithBoundary n A) (hAK : A.space ⊆ K.space) :
    closure (interior (((↑) : K.space → E) ⁻¹' A.space)) =
      ((↑) : K.space → E) ⁻¹' A.space := by
  have hclosure (B : Set E) : closure (((↑) : K.space → E) ⁻¹' B) =
      ((↑) : K.space → E) ⁻¹' closure (K.space ∩ B) := by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      Subtype.image_preimage_coe]
  rw [interior_eq_compl_closure_compl, ← preimage_compl, hclosure, ← preimage_compl, hclosure]
  change ((↑) : K.space → E) ⁻¹' closure (K.space \ closure (K.space \ A.space)) =
    ((↑) : K.space → E) ⁻¹' A.space
  rw [hK.closure_sdiff_closure_sdiff_eq K A hA hAK]

open Classical in
theorem inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary {n : ℕ}
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAK : A.space ⊆ K.space)
    (hdis : Disjoint A.space (boundaryComplex (n + 1) K).space) :
    A.space ∩ closure (K.space \ A.space) = (boundaryComplex (n + 1) A).space := by
  apply Subset.antisymm (inter_closure_sdiff_subset_boundaryComplex K A hK hA hAK)
  intro x hx
  have hxA := boundaryComplex_space_subset (n + 1) A hx
  refine ⟨hxA, ?_⟩
  by_contra hxnot
  have hnhds : A.space ∈ 𝓝[K.space] x := by
    have hO := isClosed_closure.isOpen_compl.mem_nhds hxnot
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hO] with y hyK hyO
    by_contra hyA
    exact hyO (subset_closure ⟨hyK, hyA⟩)
  exact disjoint_left.mp hdis hxA
    ((mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin K A hK hA hAK hxA hnhds).mp hx)

open Classical in
theorem frontier_preimage_space_eq_preimage_boundaryComplex {n : ℕ}
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAK : A.space ⊆ K.space)
    (hdis : Disjoint A.space (boundaryComplex (n + 1) K).space) :
    frontier (((↑) : K.space → E) ⁻¹' A.space) =
      ((↑) : K.space → E) ⁻¹' (boundaryComplex (n + 1) A).space := by
  have hclosed : IsClosed (((↑) : K.space → E) ⁻¹' A.space) :=
    (isPolyhedron_space A).isClosed.preimage continuous_subtype_val
  rw [frontier_eq_closure_inter_closure, hclosed.closure_eq, ← preimage_compl,
    Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
    Subtype.image_preimage_coe, ← preimage_inter]
  exact congrArg (preimage ((↑) : K.space → E))
    (inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary K A hK hA hAK hdis)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isTwoSided_boundaryComplex {n : ℕ}
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAK : A.space ⊆ K.space)
    (hdis : Disjoint A.space (boundaryComplex (n + 1) K).space) :
    Topology.IsTwoSided (((↑) : K.space → E) ⁻¹' (boundaryComplex (n + 1) A).space) := by
  classical
  let B := boundaryComplex (n + 1) A
  let _ : Finite B.faces := (boundaryComplex_faces_finite (n + 1) A).to_subtype
  let _ : LocallyConnectedSpace B.space := locallyConnectedSpace_space B
  have hBR : B.space ⊆ range ((↑) : K.space → E) := by
    rw [Subtype.range_coe]
    exact (boundaryComplex_space_subset (n + 1) A).trans hAK
  let e : (((↑) : K.space → E) ⁻¹' B.space) ≃ₜ B.space :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hBR
  let _ : LocallyConnectedSpace (((↑) : K.space → E) ⁻¹' B.space) :=
    e.isOpenEmbedding.locallyConnectedSpace
  have hfront := frontier_preimage_space_eq_preimage_boundaryComplex K A hK hA hAK hdis
  let _ : LocallyConnectedSpace (frontier (((↑) : K.space → E) ⁻¹' A.space)) := by
    rw [hfront]
    infer_instance
  have h := Topology.isTwoSided_frontier (hK.closure_interior_preimage K A hA hAK)
  rwa [hfront] at h

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isTwoSided_of_union_boundary_components {n : ℕ}
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAK : A.space ⊆ K.space)
    (hdis : Disjoint A.space (boundaryComplex (n + 1) K).space) {S : Set E}
    (hS : S ⊆ (boundaryComplex (n + 1) A).space)
    (hcomponents : ∀ x ∈ S, connectedComponentIn (boundaryComplex (n + 1) A).space x ⊆ S) :
    Topology.IsTwoSided (((↑) : K.space → E) ⁻¹' S) := by
  apply (hK.isTwoSided_boundaryComplex K A hA hAK hdis).of_union_components (preimage_mono hS)
  intro x hx y hy
  exact hcomponents x hx (connectedComponentIn_mono (x : E)
    (image_preimage_subset ((↑) : K.space → E) (boundaryComplex (n + 1) A).space)
    (continuous_subtype_val.continuousOn.mapsTo_connectedComponentIn (hS hx) hy))

end DifferentialGeometry.Topology.PiecewiseLinear

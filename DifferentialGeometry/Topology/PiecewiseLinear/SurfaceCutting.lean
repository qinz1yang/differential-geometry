/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComponentClosure
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComplement
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplex
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation
import DifferentialGeometry.Topology.PiecewiseLinear.Bicollar
import DifferentialGeometry.Topology.Connected.ClosedCover
import DifferentialGeometry.Topology.BicollarNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem exists_connectedComponentComplex_space_eq_of_closed_partition
    (K : Geometry.SimplicialComplex ℝ E) {S T : Set E}
    (hS : IsClosed S) (hT : IsClosed T) (hconn : IsConnected S)
    (hdis : Disjoint S T) (hcover : K.space = S ∪ T) :
    ∃ c : ConnectedComponents K.space, (connectedComponentComplex K c).space = S := by
  obtain ⟨x, hx⟩ := hconn.nonempty
  have hxK : x ∈ K.space := hcover.symm.subset (Or.inl hx)
  refine ⟨ConnectedComponents.mk (⟨x, hxK⟩ : K.space), ?_⟩
  rw [connectedComponentComplex_mk, restrict_connectedComponentIn_space]
  change connectedComponentIn K.space x = S
  rw [hcover]
  have hsdiff : S \ T = S := sdiff_eq_left.mpr hdis
  have h := connectedComponentIn_sdiff_inter_eq_sdiff hS hT
    (hsdiff.symm ▸ hconn.isPreconnected) ⟨hx, disjoint_left.mp hdis hx⟩
  simpa only [hdis.inter_eq, sdiff_empty, hsdiff] using h

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_manifold_pair_of_separating_surface
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) (hB : Disjoint L.space (boundaryComplex 3 K).space)
    (hconnK : IsPreconnected K.space) (hconnL : IsConnected L.space)
    (hsep : ¬ IsPreconnected (K.space \ L.space)) :
    ∃ (A B : Geometry.SimplicialComplex ℝ E) (hAfin : A.faces.Finite) (hBfin : B.faces.Finite),
      letI := hAfin.to_subtype
      letI := hBfin.to_subtype
      IsCombinatorialManifoldWithBoundary 3 A ∧ IsCombinatorialManifoldWithBoundary 3 B ∧
      IsConnected A.space ∧ IsConnected B.space ∧
      A.space ∪ B.space = K.space ∧ A.space ∩ B.space = L.space ∧
      (boundaryComplex 3 A).space = L.space ∪ (A.space ∩ (boundaryComplex 3 K).space) ∧
      (boundaryComplex 3 B).space = L.space ∪ (B.space ∩ (boundaryComplex 3 K).space) ∧
      (∃ c : ConnectedComponents (boundaryComplex 3 A).space,
        (PiecewiseLinear.connectedComponentComplex (boundaryComplex 3 A) c).space = L.space) ∧
      (∃ c : ConnectedComponents (boundaryComplex 3 B).space,
        (PiecewiseLinear.connectedComponentComplex (boundaryComplex 3 B) c).space = L.space) := by
  obtain ⟨a, ha, b, hb, hdis, _, hcover, hmeet⟩ :=
    hK.exists_connectedComponentIn_pair_sdiff_of_separating_surface
      hL hLK hB hconnK hconnL hsep
  obtain ⟨A, hAfin, hAspace⟩ :=
    (isPolyhedron_closure_connectedComponentIn_sdiff_of_subset K L hLK a).exists_simplicialComplex
  obtain ⟨B, hBfin, hBspace⟩ :=
    (isPolyhedron_closure_connectedComponentIn_sdiff_of_subset K L hLK b).exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  have hmeet' : closure (connectedComponentIn (K.space \ L.space) b) ∩
      closure (connectedComponentIn (K.space \ L.space) a) = L.space := by rwa [inter_comm]
  have hA := isCombinatorialManifoldWithBoundary_of_space_eq_closure_connectedComponentIn_sdiff
    hK hL hLK hB hdis hmeet A hAspace
  have hBman := isCombinatorialManifoldWithBoundary_of_space_eq_closure_connectedComponentIn_sdiff
    hK hL hLK hB hdis.symm hmeet' B hBspace
  have hAbd := boundaryComplex_space_of_space_eq_closure_connectedComponentIn_sdiff
    hK hL hLK hB hdis hmeet A hAspace
  have hBbd := boundaryComplex_space_of_space_eq_closure_connectedComponentIn_sdiff
    hK hL hLK hB hdis.symm hmeet' B hBspace
  refine ⟨A, B, hAfin, hBfin, hA, hBman, ?_, ?_, ?_, ?_, hAbd, hBbd, ?_, ?_⟩
  · rw [hAspace]
    exact (isConnected_connectedComponentIn_iff.mpr ha).closure
  · rw [hBspace]
    exact (isConnected_connectedComponentIn_iff.mpr hb).closure
  · rwa [hAspace, hBspace]
  · rwa [hAspace, hBspace]
  · exact exists_connectedComponentComplex_space_eq_of_closed_partition (boundaryComplex 3 A)
      (isPolyhedron_space L).isClosed
      ((isPolyhedron_space A).isClosed.inter (isPolyhedron_space (boundaryComplex 3 K)).isClosed)
      hconnL (hB.mono_right inter_subset_right) hAbd
  · exact exists_connectedComponentComplex_space_eq_of_closed_partition (boundaryComplex 3 B)
      (isPolyhedron_space L).isClosed
      ((isPolyhedron_space B).isClosed.inter (isPolyhedron_space (boundaryComplex 3 K)).isClosed)
      hconnL (hB.mono_right inter_subset_right) hBbd

open Classical in
theorem IsCombinatorialManifold.not_isPreconnected_sdiff_of_subset_interior
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hdim : Module.finrank ℝ E = 3)
    (hconn : IsConnected L.space) {S : Set E} (hLS : L.space ⊆ interior S) :
    ¬ IsPreconnected (S \ L.space) := by
  obtain ⟨a, _, b, _, hdis, hcover, _, hmeet, _, _⟩ :=
    hL.exists_connectedComponentIn_pair_compl L hdim hconn
  let A := connectedComponentIn L.spaceᶜ a
  let B := connectedComponentIn L.spaceᶜ b
  have hA : IsOpen A := (isPolyhedron_space L).isClosed.isOpen_compl.connectedComponentIn
  have hB : IsOpen B := (isPolyhedron_space L).isClosed.isOpen_compl.connectedComponentIn
  obtain ⟨x, hx⟩ := hconn.nonempty
  have hxS : S ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp (hLS hx)
  have hxAB := hmeet.symm.subset hx
  obtain ⟨p, hpS, hpA⟩ := (mem_closure_iff_nhds.mp hxAB.1) S hxS
  obtain ⟨q, hqS, hqB⟩ := (mem_closure_iff_nhds.mp hxAB.2) S hxS
  intro hpre
  obtain ⟨z, _, hzA, hzB⟩ := hpre A B hA hB
    (fun z hz => hcover.symm.subset hz.2)
    ⟨p, ⟨hpS, connectedComponentIn_subset L.spaceᶜ a hpA⟩, hpA⟩
    ⟨q, ⟨hqS, connectedComponentIn_subset L.spaceᶜ b hqB⟩, hqB⟩
  exact disjoint_left.mp hdis hzA hzB

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_manifold_pair_of_surface_interior
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hdim : Module.finrank ℝ E = 3)
    (hLK : L.space ⊆ K.space \ (boundaryComplex 3 K).space)
    (hconnK : IsPreconnected K.space) (hconnL : IsConnected L.space) :
    ∃ (A B : Geometry.SimplicialComplex ℝ E) (hAfin : A.faces.Finite) (hBfin : B.faces.Finite),
      letI := hAfin.to_subtype
      letI := hBfin.to_subtype
      IsCombinatorialManifoldWithBoundary 3 A ∧ IsCombinatorialManifoldWithBoundary 3 B ∧
      IsConnected A.space ∧ IsConnected B.space ∧ IsOrientable 3 A ∧ IsOrientable 3 B ∧
      A.space ∪ B.space = K.space ∧ A.space ∩ B.space = L.space ∧
      (boundaryComplex 3 A).space = L.space ∪ (A.space ∩ (boundaryComplex 3 K).space) ∧
      (boundaryComplex 3 B).space = L.space ∪ (B.space ∩ (boundaryComplex 3 K).space) ∧
      (∃ c : ConnectedComponents (boundaryComplex 3 A).space,
        (PiecewiseLinear.connectedComponentComplex (boundaryComplex 3 A) c).space = L.space) ∧
      (∃ c : ConnectedComponents (boundaryComplex 3 B).space,
        (PiecewiseLinear.connectedComponentComplex (boundaryComplex 3 B) c).space = L.space) := by
  have hLint : L.space ⊆ interior K.space := by
    intro x hx
    have h := hLK hx
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK] at h
    exact not_not.mp (fun hn => h.2 ⟨subset_closure h.1, hn⟩)
  have hsep := hL.not_isPreconnected_sdiff_of_subset_interior L hdim hconnL hLint
  obtain ⟨A, B, hAfin, hBfin, hA, hB, hAc, hBc, hcover, hmeet, hAbd, hBbd, hcA, hcB⟩ :=
    hK.exists_manifold_pair_of_separating_surface hL (hLK.trans sdiff_subset)
      (disjoint_left.mpr (fun _ hx hy => (hLK hx).2 hy)) hconnK hconnL hsep
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  obtain ⟨T, _, hTcard, hKT⟩ := exists_affineIndependent_openSimplex_superset 3 hdim
    (isPolyhedron_space K).isCompact.isBounded
  have hsub : K.space ⊆ convexHull ℝ (T : Set E) := hKT.trans (openSimplex_subset_convexHull T)
  have hAo := isOrientable_of_space_subset_convexHull A hA T hTcard
    ((subset_union_left.trans hcover.subset).trans hsub)
  have hBo := isOrientable_of_space_subset_convexHull B hB T hTcard
    ((subset_union_right.trans hcover.subset).trans hsub)
  exact ⟨A, B, hAfin, hBfin, hA, hB, hAc, hBc, hAo, hBo,
    hcover, hmeet, hAbd, hBbd, hcA, hcB⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_twoSidedCollar_of_interior_surface
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) (hBd : Disjoint L.space (boundaryComplex 3 K).space)
    (htwo : IsTwoSided (((↑) : K.space → E) ⁻¹' L.space))
    {U : Set E} (hU : U ∈ 𝓝ˢ[K.space] L.space) :
    ∃ c : ThreeManifold.TwoSidedCollar (Set.inclusion hLK),
      range (((↑) : K.space → E) ∘ c.toFun) ⊆ U := by
  let _ : CompactSpace L.space := isCompact_iff_compactSpace.mp (isPolyhedron_space L).isCompact
  obtain ⟨W, ρ, _, hWK, hWU, hWnhds, hρ, hzero⟩ := hK.exists_bicollar hL hLK hBd htwo hU
  have hWK' : W ⊆ K.space := hWK.trans sdiff_subset
  let q : L.space × Icc (-1 : ℝ) 1 ≃ₜ W :=
    (Homeomorph.Set.prod L.space (Icc (-1 : ℝ) 1)).symm.trans hρ.homeomorph
  let k : L.space × Icc (-1 : ℝ) 1 → K.space := Set.inclusion hWK' ∘ q
  have hk : _root_.Topology.IsEmbedding k :=
    (_root_.Topology.IsEmbedding.inclusion hWK').comp q.isEmbedding
  have hkzero : ∀ s : L.space, k (s, ⟨0, by norm_num⟩) = Set.inclusion hLK s := by
    intro s
    exact Subtype.ext (hzero s.val s.property)
  have hkrange : range k = ((↑) : K.space → E) ⁻¹' W := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact (q z).property
    · intro hy
      obtain ⟨z, hz⟩ := q.surjective ⟨y.val, hy⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change (q z).val = y.val
      exact congrArg Subtype.val hz
  have herange : range (Set.inclusion hLK) = ((↑) : K.space → E) ⁻¹' L.space := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact z.property
    · intro hy
      exact ⟨⟨y.val, hy⟩, rfl⟩
  have hknhds : range k ∈ 𝓝ˢ (range (Set.inclusion hLK)) := by
    rw [hkrange, herange]
    apply mem_nhdsSet_subtype_iff_nhdsSetWithin.mpr
    simpa only [Subtype.image_preimage_coe, inter_eq_right.mpr hWK',
      inter_eq_right.mpr hLK] using hWnhds
  obtain ⟨c, hc⟩ := exists_twoSidedCollar_of_closedInterval zero_lt_one k hk hkzero hknhds
  refine ⟨c, ?_⟩
  rintro y ⟨z, rfl⟩
  exact hWU (hkrange.subset (hc ⟨z, rfl⟩))

end DifferentialGeometry.Topology.PiecewiseLinear

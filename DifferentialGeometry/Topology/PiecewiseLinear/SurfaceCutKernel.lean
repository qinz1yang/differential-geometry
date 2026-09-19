/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCutting
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorConnected
import DifferentialGeometry.Topology.SimplicialComplex.GeometricConnectivity
import DifferentialGeometry.Topology.FundamentalGroup.BicollarBoundary

/-! Fundamental-group kernels into finite manifolds cut along an interior surface. -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
private theorem isConnected_sdiff_and_closure_eq_of_inter_subset_boundary
    {n : ℕ} {A : Geometry.SimplicialComplex ℝ E} [Finite A.faces]
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAc : IsConnected A.space)
    {T : Set E} (hT : A.space ∩ T ⊆ (boundaryComplex (n + 1) A).space) :
    IsConnected (A.space \ T) ∧ closure (A.space \ T) = A.space := by
  have hsub : A.space \ (boundaryComplex (n + 1) A).space ⊆ A.space \ T :=
    fun _ hx => ⟨hx.1, fun h => hx.2 (hT ⟨hx.1, h⟩)⟩
  exact ⟨(hA.isConnected_sdiff_boundaryComplex_space hAc).subset_closure hsub
    (sdiff_subset.trans hA.space_subset_closure_sdiff_boundaryComplex_space),
    Subset.antisymm (closure_minimal sdiff_subset (isPolyhedron_space A).isClosed)
      (hA.space_subset_closure_sdiff_boundaryComplex_space.trans (closure_mono hsub))⟩

open Classical in
theorem closure_collar_component_eq_of_manifold_pair
    {K L A B : Geometry.SimplicialComplex ℝ E} [Finite A.faces] [Finite B.faces]
    (hA : IsCombinatorialManifoldWithBoundary 3 A)
    (hB : IsCombinatorialManifoldWithBoundary 3 B)
    (hAc : IsConnected A.space) (hBc : IsConnected B.space)
    (hcover : A.space ∪ B.space = K.space) (hmeet : A.space ∩ B.space = L.space)
    (hAbd : L.space ⊆ (boundaryComplex 3 A).space)
    (hBbd : L.space ⊆ (boundaryComplex 3 B).space)
    (hLK : L.space ⊆ K.space) (c : ThreeManifold.TwoSidedCollar (Set.inclusion hLK))
    (y : c.complement) :
    closure (Subtype.val '' connectedComponent y) = ((↑) : K.space → E) ⁻¹' A.space ∨
      closure (Subtype.val '' connectedComponent y) = ((↑) : K.space → E) ⁻¹' B.space := by
  let P : Set K.space := ((↑) : K.space → E) ⁻¹' A.space
  let Q : Set K.space := ((↑) : K.space → E) ⁻¹' B.space
  have hAK : A.space ⊆ K.space := subset_union_left.trans hcover.subset
  have hBK : B.space ⊆ K.space := subset_union_right.trans hcover.subset
  obtain ⟨hAP, hAcl⟩ := isConnected_sdiff_and_closure_eq_of_inter_subset_boundary
    hA hAc (hmeet.subset.trans hAbd)
  obtain ⟨hBQ, hBcl⟩ := isConnected_sdiff_and_closure_eq_of_inter_subset_boundary
    hB hBc ((inter_comm B.space A.space).trans hmeet |>.subset.trans hBbd)
  have hPc : IsPreconnected (P \ Q) := by
    rw [show P \ Q = ((↑) : K.space → E) ⁻¹' (A.space \ B.space) from rfl]
    apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    simpa only [Subtype.image_preimage_coe,
      inter_eq_right.mpr (sdiff_subset.trans hAK)] using hAP.isPreconnected
  have hQc : IsPreconnected (Q \ P) := by
    rw [show Q \ P = ((↑) : K.space → E) ⁻¹' (B.space \ A.space) from rfl]
    apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    simpa only [Subtype.image_preimage_coe,
      inter_eq_right.mpr (sdiff_subset.trans hBK)] using hBQ.isPreconnected
  have hPcl : closure (P \ Q) = P := by
    rw [_root_.Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    change ((↑) : K.space → E) ⁻¹' closure
      (((↑) : K.space → E) '' (((↑) : K.space → E) ⁻¹' (A.space \ B.space))) = P
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr (sdiff_subset.trans hAK), hAcl]
  have hQcl : closure (Q \ P) = Q := by
    rw [_root_.Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    change ((↑) : K.space → E) ⁻¹' closure
      (((↑) : K.space → E) '' (((↑) : K.space → E) ⁻¹' (B.space \ A.space))) = Q
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr (sdiff_subset.trans hBK), hBcl]
  have hrange : Set.range (Set.inclusion hLK) = ((↑) : K.space → E) ⁻¹' L.space := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact z.property
    · intro hx
      exact ⟨⟨x.val, hx⟩, rfl⟩
  have hPQ : c.complement = (P ∪ Q) \ (P ∩ Q) := by
    change (Set.range (Set.inclusion hLK))ᶜ =
      (((↑) : K.space → E) ⁻¹' A.space ∪ ((↑) : K.space → E) ⁻¹' B.space) \
        (((↑) : K.space → E) ⁻¹' A.space ∩ ((↑) : K.space → E) ⁻¹' B.space)
    rw [hrange, ← preimage_union, ← preimage_inter, hcover, hmeet]
    simp only [Subtype.coe_preimage_self, compl_eq_univ_sdiff]
  rw [← connectedComponentIn_eq_image y.property]
  have h := closure_connectedComponentIn_sdiff_inter_eq_or_eq
    ((isPolyhedron_space A).isClosed.preimage continuous_subtype_val)
    ((isPolyhedron_space B).isClosed.preimage continuous_subtype_val)
    hPc hQc hPcl hQcl (hPQ.subset y.property)
  have hcomp := congrArg (fun T : Set K.space => closure (connectedComponentIn T y.val)) hPQ
  exact h.imp hcomp.trans hcomp.trans

open Classical in
theorem exists_nontrivial_fundamentalGroup_kernel_of_manifold_pair
    {K L A B : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    [Finite A.faces] [Finite B.faces] [SimplyConnectedSpace K.space]
    [LocallyPathConnectedSpace K.space]
    (hA : IsCombinatorialManifoldWithBoundary 3 A)
    (hB : IsCombinatorialManifoldWithBoundary 3 B)
    (hAc : IsConnected A.space) (hBc : IsConnected B.space)
    (hcover : A.space ∪ B.space = K.space) (hmeet : A.space ∩ B.space = L.space)
    (hAbd : L.space ⊆ (boundaryComplex 3 A).space)
    (hBbd : L.space ⊆ (boundaryComplex 3 B).space)
    (hLc : IsConnected L.space) (hLn : ¬ SimplyConnectedSpace L.space)
    (hLK : L.space ⊆ K.space) (c : ThreeManifold.TwoSidedCollar (Set.inclusion hLK))
    (s : L.space) :
    ∃ g : FundamentalGroup L.space s, g ≠ 1 ∧
      ((∃ hLA : L.space ⊆ A.space,
          FundamentalGroup.map (⟨Set.inclusion hLA, continuous_inclusion hLA⟩ :
            C(L.space, A.space)) s g = 1) ∨
        ∃ hLB : L.space ⊆ B.space,
          FundamentalGroup.map (⟨Set.inclusion hLB, continuous_inclusion hLB⟩ :
            C(L.space, B.space)) s g = 1) := by
  let _ : CompactSpace L.space := isCompact_iff_compactSpace.mp (isPolyhedron_space L).isCompact
  let _ : PathConnectedSpace L.space := isPathConnected_iff_pathConnectedSpace.mp
    (SimplicialComplex.isPathConnected_geometricSpace L hLc)
  have hLA : L.space ⊆ A.space := hmeet.symm.subset.trans inter_subset_left
  have hLB : L.space ⊆ B.space := hmeet.symm.subset.trans inter_subset_right
  have hcomponent := closure_collar_component_eq_of_manifold_pair
    hA hB hAc hBc hcover hmeet hAbd hBbd hLK c
  obtain ⟨g, hg, hside⟩ :=
    c.exists_nontrivial_fundamentalGroup_kernel_boundary_of_simplyConnectedSpace hLn s
  have transfer {R : Geometry.SimplicialComplex ℝ E} {Z : Set K.space}
      (f : C(L.space, Z)) (hf : ∀ x, (f x).val = Set.inclusion hLK x)
      (hZ : Z = ((↑) : K.space → E) ⁻¹' R.space) (hLR : L.space ⊆ R.space)
      (hnull : FundamentalGroup.map f s g = 1) :
      FundamentalGroup.map (⟨Set.inclusion hLR, continuous_inclusion hLR⟩ :
        C(L.space, R.space)) s g = 1 := by
    let d : C(Z, R.space) :=
      ⟨fun x => ⟨x.val.val, hZ.subset x.property⟩,
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
    have heq : (⟨Set.inclusion hLR, continuous_inclusion hLR⟩ : C(L.space, R.space)) =
        d.comp f := by
      ext x
      exact (congrArg Subtype.val (hf x)).symm
    rw [heq]
    change Path.Homotopic.Quotient.map g _ = .refl _
    rw [Path.Homotopic.Quotient.map_comp]
    change FundamentalGroup.map d _ (FundamentalGroup.map f s g) = 1
    rw [hnull, map_one]
  refine ⟨g, hg, ?_⟩
  rcases hside with hn | hp
  · rcases hcomponent c.negativePoint with hAn | hBn
    · exact Or.inl ⟨hLA, transfer c.negativeBoundaryInclusion (fun _ => rfl) hAn hLA hn⟩
    · exact Or.inr ⟨hLB, transfer c.negativeBoundaryInclusion (fun _ => rfl) hBn hLB hn⟩
  · rcases hcomponent c.positivePoint with hAp | hBp
    · exact Or.inl ⟨hLA, transfer c.positiveBoundaryInclusion (fun _ => rfl) hAp hLA hp⟩
    · exact Or.inr ⟨hLB, transfer c.positiveBoundaryInclusion (fun _ => rfl) hBp hLB hp⟩

open Classical in
theorem exists_boundary_component_kernel_of_manifold_pair
    {K L A B : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    [Finite A.faces] [Finite B.faces] [SimplyConnectedSpace K.space]
    [LocallyPathConnectedSpace K.space]
    (hA : IsCombinatorialManifoldWithBoundary 3 A)
    (hB : IsCombinatorialManifoldWithBoundary 3 B)
    (hAc : IsConnected A.space) (hBc : IsConnected B.space)
    (hcover : A.space ∪ B.space = K.space) (hmeet : A.space ∩ B.space = L.space)
    (cA : ConnectedComponents (boundaryComplex 3 A).space)
    (cB : ConnectedComponents (boundaryComplex 3 B).space)
    (hCA : (connectedComponentComplex (boundaryComplex 3 A) cA).space = L.space)
    (hCB : (connectedComponentComplex (boundaryComplex 3 B) cB).space = L.space)
    (hLc : IsConnected L.space) (hLn : ¬ SimplyConnectedSpace L.space)
    (hLK : L.space ⊆ K.space) (c : ThreeManifold.TwoSidedCollar (Set.inclusion hLK))
    (s : L.space) :
    (∃ (hsub : (connectedComponentComplex (boundaryComplex 3 A) cA).space ⊆ A.space)
        (x : (connectedComponentComplex (boundaryComplex 3 A) cA).space)
        (g : FundamentalGroup (connectedComponentComplex (boundaryComplex 3 A) cA).space x),
      g ≠ 1 ∧ FundamentalGroup.map (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
        C((connectedComponentComplex (boundaryComplex 3 A) cA).space, A.space)) x g = 1) ∨
    ∃ (hsub : (connectedComponentComplex (boundaryComplex 3 B) cB).space ⊆ B.space)
        (x : (connectedComponentComplex (boundaryComplex 3 B) cB).space)
        (g : FundamentalGroup (connectedComponentComplex (boundaryComplex 3 B) cB).space x),
      g ≠ 1 ∧ FundamentalGroup.map (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
        C((connectedComponentComplex (boundaryComplex 3 B) cB).space, B.space)) x g = 1 := by
  have hAbd : L.space ⊆ (boundaryComplex 3 A).space := by
    rw [← hCA, connectedComponentComplex_space]
    rintro _ ⟨p, _, rfl⟩
    exact p.property
  have hBbd : L.space ⊆ (boundaryComplex 3 B).space := by
    rw [← hCB, connectedComponentComplex_space]
    rintro _ ⟨p, _, rfl⟩
    exact p.property
  obtain ⟨g, hg, hside⟩ := exists_nontrivial_fundamentalGroup_kernel_of_manifold_pair
    hA hB hAc hBc hcover hmeet hAbd hBbd hLc hLn hLK c s
  rcases hside with ⟨hLA, hnull⟩ | ⟨hLB, hnull⟩
  · left
    rw [hCA]
    exact ⟨hLA, s, g, hg, hnull⟩
  · right
    rw [hCB]
    exact ⟨hLB, s, g, hg, hnull⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_boundary_component_kernel_of_interior_surface
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    [SimplyConnectedSpace K.space]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hdim : Module.finrank ℝ E = 3)
    (hLint : L.space ⊆ K.space \ (boundaryComplex 3 K).space)
    (hLc : IsConnected L.space) (s : L.space) (g : FundamentalGroup L.space s) (hg : g ≠ 1)
    {U : Set E} (hU : U ∈ 𝓝ˢ[K.space] L.space) :
    ∃ (hLK : L.space ⊆ K.space) (c : ThreeManifold.TwoSidedCollar (Set.inclusion hLK)),
      range (((↑) : K.space → E) ∘ c.toFun) ⊆ U ∧
      ∃ (R : Geometry.SimplicialComplex ℝ E) (hRfin : R.faces.Finite),
        letI := hRfin.to_subtype
        IsCombinatorialManifoldWithBoundary 3 R ∧ IsConnected R.space ∧ IsOrientable 3 R ∧
        R.space ⊆ K.space ∧
        (boundaryComplex 3 R).space = L.space ∪ (R.space ∩ (boundaryComplex 3 K).space) ∧
        ∃ d : ConnectedComponents (boundaryComplex 3 R).space,
          (PiecewiseLinear.connectedComponentComplex (boundaryComplex 3 R) d).space = L.space ∧
          ∃ (hsub : (PiecewiseLinear.connectedComponentComplex (boundaryComplex 3 R) d).space ⊆
                R.space)
            (x : (PiecewiseLinear.connectedComponentComplex (boundaryComplex 3 R) d).space)
            (a : FundamentalGroup
              (PiecewiseLinear.connectedComponentComplex (boundaryComplex 3 R) d).space x),
            a ≠ 1 ∧ FundamentalGroup.map (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
              C((PiecewiseLinear.connectedComponentComplex (boundaryComplex 3 R) d).space,
                R.space)) x a = 1 := by
  let _ : LocallyPathConnectedSpace K.space :=
    SimplicialComplex.locallyPathConnectedSpace_geometricSpace K
  have hKc : IsPreconnected K.space :=
    isPreconnected_iff_preconnectedSpace.mpr inferInstance
  obtain ⟨A, B, hAfin, hBfin, hA, hB, hAc, hBc, hAo, hBo, hcover, hmeet,
    hAbd, hBbd, ⟨cA, hCA⟩, ⟨cB, hCB⟩⟩ :=
      hK.exists_manifold_pair_of_surface_interior hL hdim hLint hKc hLc
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  have hLK : L.space ⊆ K.space := hLint.trans sdiff_subset
  have hLi : L.space ⊆ interior K.space := by
    intro x hx
    have h := hLint hx
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK] at h
    exact not_not.mp (fun hn => h.2 ⟨subset_closure h.1, hn⟩)
  have htwo := (hL.isTwoSided L hdim hLc).preimage_of_isInducing
    _root_.Topology.IsInducing.subtypeVal (by
      rw [Subtype.range_val]
      exact subset_interior_iff_mem_nhdsSet.mp hLi)
  obtain ⟨c, hc⟩ := hK.exists_twoSidedCollar_of_interior_surface hL hLK
    (disjoint_left.mpr (fun _ hx hy => (hLint hx).2 hy)) htwo hU
  have hLn : ¬ SimplyConnectedSpace L.space := by
    intro h
    let _ := h
    exact hg (Subsingleton.elim _ _)
  have hkernel := exists_boundary_component_kernel_of_manifold_pair
    hA hB hAc hBc hcover hmeet cA cB hCA hCB hLc hLn hLK c s
  refine ⟨hLK, c, hc, ?_⟩
  rcases hkernel with ⟨hsub, x, a, ha, hnull⟩ | ⟨hsub, x, a, ha, hnull⟩
  · exact ⟨A, hAfin, hA, hAc, hAo, subset_union_left.trans hcover.subset,
      hAbd, cA, hCA, hsub, x, a, ha, hnull⟩
  · exact ⟨B, hBfin, hB, hBc, hBo, subset_union_right.trans hcover.subset,
      hBbd, cB, hCB, hsub, x, a, ha, hnull⟩

end DifferentialGeometry.Topology.PiecewiseLinear

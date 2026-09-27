/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCutting
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorConnected
import DifferentialGeometry.Topology.SimplicialComplex.GeometricConnectivity
import DifferentialGeometry.Topology.FundamentalGroup.CollaredClosedCover
import DifferentialGeometry.Topology.FundamentalGroup.SimplyConnected

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
private theorem isConnected_preimage_sdiff_and_closure_eq_of_inter_subset_boundary
    {n : ℕ} {K A : Geometry.SimplicialComplex ℝ E} [Finite A.faces]
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAc : IsConnected A.space)
    {T : Set E} (hT : A.space ∩ T ⊆ (boundaryComplex (n + 1) A).space)
    (hAK : A.space ⊆ K.space) :
    IsConnected (((↑) : K.space → E) ⁻¹' (A.space \ T)) ∧
      closure (((↑) : K.space → E) ⁻¹' (A.space \ T)) =
        ((↑) : K.space → E) ⁻¹' A.space := by
  obtain ⟨hc, hcl⟩ := isConnected_sdiff_and_closure_eq_of_inter_subset_boundary hA hAc hT
  constructor
  · refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hc.nonempty
      exact ⟨⟨x, hAK hx.1⟩, hx⟩
    · apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      simpa only [Subtype.image_preimage_coe,
        inter_eq_right.mpr (sdiff_subset.trans hAK)] using hc.isPreconnected
  · rw [_root_.Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      Subtype.image_preimage_coe, inter_eq_right.mpr (sdiff_subset.trans hAK), hcl]

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
  obtain ⟨hPc, hPcl⟩ := isConnected_preimage_sdiff_and_closure_eq_of_inter_subset_boundary
    hA hAc (hmeet.subset.trans hAbd) hAK
  obtain ⟨hQc, hQcl⟩ := isConnected_preimage_sdiff_and_closure_eq_of_inter_subset_boundary
    hB hBc ((inter_comm B.space A.space).trans hmeet |>.subset.trans hBbd) hBK
  have hPQ : c.complement = (P ∪ Q) \ (P ∩ Q) := by
    change (Set.range (Set.inclusion hLK))ᶜ =
      (((↑) : K.space → E) ⁻¹' A.space ∪ ((↑) : K.space → E) ⁻¹' B.space) \
        (((↑) : K.space → E) ⁻¹' A.space ∩ ((↑) : K.space → E) ⁻¹' B.space)
    rw [Set.range_inclusion, ← preimage_union, ← preimage_inter, hcover, hmeet]
    simp only [Subtype.coe_preimage_self, compl_eq_univ_sdiff]
    rfl
  rw [← connectedComponentIn_eq_image y.property]
  have h := closure_connectedComponentIn_sdiff_inter_eq_or_eq
    ((isPolyhedron_space A).isClosed.preimage continuous_subtype_val)
    ((isPolyhedron_space B).isClosed.preimage continuous_subtype_val)
    hPc.isPreconnected hQc.isPreconnected hPcl hQcl (hPQ.subset y.property)
  have hcomp := congrArg (fun T : Set K.space => closure (connectedComponentIn T y.val)) hPQ
  exact h.imp hcomp.trans hcomp.trans

open Classical in
theorem exists_nontrivial_fundamentalGroup_kernel_of_manifold_pair_of_map_eq_one
    {K L A B : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    [Finite A.faces] [Finite B.faces]
    (hA : IsCombinatorialManifoldWithBoundary 3 A)
    (hB : IsCombinatorialManifoldWithBoundary 3 B)
    (hAc : IsConnected A.space) (hBc : IsConnected B.space)
    (hcover : A.space ∪ B.space = K.space) (hmeet : A.space ∩ B.space = L.space)
    (hAbd : L.space ⊆ (boundaryComplex 3 A).space)
    (hBbd : L.space ⊆ (boundaryComplex 3 B).space)
    (hLc : IsConnected L.space)
    (hLK : L.space ⊆ K.space) (c : ThreeManifold.TwoSidedCollar (Set.inclusion hLK))
    (s : L.space) (g : FundamentalGroup L.space s) (hg : g ≠ 1)
    (hnull : FundamentalGroup.map (⟨Set.inclusion hLK, continuous_inclusion hLK⟩ :
      C(L.space, K.space)) s g = 1) :
    ∃ g : FundamentalGroup L.space s, g ≠ 1 ∧
      ((∃ hLA : L.space ⊆ A.space,
          FundamentalGroup.map (⟨Set.inclusion hLA, continuous_inclusion hLA⟩ :
            C(L.space, A.space)) s g = 1) ∨
        ∃ hLB : L.space ⊆ B.space,
          FundamentalGroup.map (⟨Set.inclusion hLB, continuous_inclusion hLB⟩ :
            C(L.space, B.space)) s g = 1) := by
  let _ : PathConnectedSpace L.space := isPathConnected_iff_pathConnectedSpace.mp
    (SimplicialComplex.isPathConnected_geometricSpace L hLc)
  let P : Set K.space := ((↑) : K.space → E) ⁻¹' A.space
  let Q : Set K.space := ((↑) : K.space → E) ⁻¹' B.space
  have hAK : A.space ⊆ K.space := subset_union_left.trans hcover.subset
  have hBK : B.space ⊆ K.space := subset_union_right.trans hcover.subset
  obtain ⟨_, hPcl⟩ := isConnected_preimage_sdiff_and_closure_eq_of_inter_subset_boundary
    hA hAc (hmeet.subset.trans hAbd) hAK
  obtain ⟨_, hQcl⟩ := isConnected_preimage_sdiff_and_closure_eq_of_inter_subset_boundary
    hB hBc ((inter_comm B.space A.space).trans hmeet |>.subset.trans hBbd) hBK
  let eP : P ≃ₜ A.space :=
    _root_.Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange (by
      rw [Subtype.range_val]
      exact hAK)
  let eQ : Q ≃ₜ B.space :=
    _root_.Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange (by
      rw [Subtype.range_val]
      exact hBK)
  let _ : PathConnectedSpace A.space := isPathConnected_iff_pathConnectedSpace.mp
    (SimplicialComplex.isPathConnected_geometricSpace A hAc)
  let _ : PathConnectedSpace B.space := isPathConnected_iff_pathConnectedSpace.mp
    (SimplicialComplex.isPathConnected_geometricSpace B hBc)
  let _ : PathConnectedSpace P := eP.symm.surjective.pathConnectedSpace eP.symm.continuous
  let _ : PathConnectedSpace Q := eQ.symm.surjective.pathConnectedSpace eQ.symm.continuous
  have hPQ : P ∪ Q = univ := by
    change ((↑) : K.space → E) ⁻¹' A.space ∪ ((↑) : K.space → E) ⁻¹' B.space = univ
    rw [← preimage_union, hcover, Subtype.coe_preimage_self]
  have hPQmeet : P ∩ Q = Set.range (Set.inclusion hLK) := by
    change ((↑) : K.space → E) ⁻¹' A.space ∩ ((↑) : K.space → E) ⁻¹' B.space = _
    rw [← preimage_inter, hmeet, Set.range_inclusion]
    rfl
  have hLA : L.space ⊆ A.space := hmeet.symm.subset.trans inter_subset_left
  have hLB : L.space ⊆ B.space := hmeet.symm.subset.trans inter_subset_right
  obtain ⟨a, ha, hside⟩ :=
    c.exists_nontrivial_fundamentalGroup_kernel_of_closed_cover hPQ hPQmeet hPcl hQcl
      s g hg hnull
  have transfer {R : Geometry.SimplicialComplex ℝ E} {Z : Set K.space}
      (f : C(L.space, Z)) (hf : ∀ x, (f x).val = Set.inclusion hLK x)
      (hZ : Z = ((↑) : K.space → E) ⁻¹' R.space) (hLR : L.space ⊆ R.space)
      (hfn : FundamentalGroup.map f s a = 1) :
      FundamentalGroup.map (⟨Set.inclusion hLR, continuous_inclusion hLR⟩ :
        C(L.space, R.space)) s a = 1 := by
    let d : C(Z, R.space) :=
      ⟨fun x => ⟨x.val.val, hZ.subset x.property⟩,
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
    have heq : (⟨Set.inclusion hLR, continuous_inclusion hLR⟩ : C(L.space, R.space)) =
        d.comp f := by
      ext x
      exact (congrArg Subtype.val (hf x)).symm
    rw [heq]
    change Path.Homotopic.Quotient.map a _ = .refl _
    rw [Path.Homotopic.Quotient.map_comp]
    change FundamentalGroup.map d _ (FundamentalGroup.map f s a) = 1
    rw [hfn, map_one]
  refine ⟨a, ha, ?_⟩
  rcases hside with hn | hp
  · exact Or.inl ⟨hLA, transfer _ (fun _ => rfl) rfl hLA hn⟩
  · exact Or.inr ⟨hLB, transfer _ (fun _ => rfl) rfl hLB hp⟩

open Classical in
theorem exists_nontrivial_fundamentalGroup_kernel_of_manifold_pair
    {K L A B : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    [Finite A.faces] [Finite B.faces] [SimplyConnectedSpace K.space]
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
  let _ : PathConnectedSpace L.space := isPathConnected_iff_pathConnectedSpace.mp
    (SimplicialComplex.isPathConnected_geometricSpace L hLc)
  obtain ⟨g, hg⟩ := exists_fundamentalGroup_ne_one_of_not_simplyConnectedSpace hLn s
  exact exists_nontrivial_fundamentalGroup_kernel_of_manifold_pair_of_map_eq_one
    hA hB hAc hBc hcover hmeet hAbd hBbd hLc hLK c s g hg (Subsingleton.elim _ _)

open Classical in
theorem exists_boundary_component_kernel_of_manifold_pair_of_map_eq_one
    {K L A B : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    [Finite A.faces] [Finite B.faces]
    (hA : IsCombinatorialManifoldWithBoundary 3 A)
    (hB : IsCombinatorialManifoldWithBoundary 3 B)
    (hAc : IsConnected A.space) (hBc : IsConnected B.space)
    (hcover : A.space ∪ B.space = K.space) (hmeet : A.space ∩ B.space = L.space)
    (cA : ConnectedComponents (boundaryComplex 3 A).space)
    (cB : ConnectedComponents (boundaryComplex 3 B).space)
    (hCA : (connectedComponentComplex (boundaryComplex 3 A) cA).space = L.space)
    (hCB : (connectedComponentComplex (boundaryComplex 3 B) cB).space = L.space)
    (hLc : IsConnected L.space)
    (hLK : L.space ⊆ K.space) (c : ThreeManifold.TwoSidedCollar (Set.inclusion hLK))
    (s : L.space) (g : FundamentalGroup L.space s) (hg : g ≠ 1)
    (hnull : FundamentalGroup.map (⟨Set.inclusion hLK, continuous_inclusion hLK⟩ :
      C(L.space, K.space)) s g = 1) :
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
  obtain ⟨a, ha, hside⟩ := exists_nontrivial_fundamentalGroup_kernel_of_manifold_pair_of_map_eq_one
    hA hB hAc hBc hcover hmeet hAbd hBbd hLc hLK c s g hg hnull
  rcases hside with ⟨hLA, hnull⟩ | ⟨hLB, hnull⟩
  · left
    rw [hCA]
    exact ⟨hLA, s, a, ha, hnull⟩
  · right
    rw [hCB]
    exact ⟨hLB, s, a, ha, hnull⟩

open Classical in
theorem exists_boundary_component_kernel_of_manifold_pair
    {K L A B : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    [Finite A.faces] [Finite B.faces] [SimplyConnectedSpace K.space]
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
  let _ : PathConnectedSpace L.space := isPathConnected_iff_pathConnectedSpace.mp
    (SimplicialComplex.isPathConnected_geometricSpace L hLc)
  obtain ⟨g, hg⟩ := exists_fundamentalGroup_ne_one_of_not_simplyConnectedSpace hLn s
  exact exists_boundary_component_kernel_of_manifold_pair_of_map_eq_one
    hA hB hAc hBc hcover hmeet cA cB hCA hCB hLc hLK c s g hg (Subsingleton.elim _ _)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_boundary_component_kernel_of_interior_inclusion
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hdim : Module.finrank ℝ E = 3)
    (hLint : L.space ⊆ K.space \ (boundaryComplex 3 K).space)
    (hKc : IsPreconnected K.space) (hLc : IsConnected L.space)
    (s : L.space) (g : FundamentalGroup L.space s) (hg : g ≠ 1)
    (hnull : FundamentalGroup.map
      (⟨Set.inclusion (hLint.trans sdiff_subset), continuous_inclusion _⟩ :
        C(L.space, K.space)) s g = 1)
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
  have hkernel := exists_boundary_component_kernel_of_manifold_pair_of_map_eq_one
    hA hB hAc hBc hcover hmeet cA cB hCA hCB hLc hLK c s g hg hnull
  refine ⟨hLK, c, hc, ?_⟩
  rcases hkernel with ⟨hsub, x, a, ha, hnull⟩ | ⟨hsub, x, a, ha, hnull⟩
  · exact ⟨A, hAfin, hA, hAc, hAo, subset_union_left.trans hcover.subset,
      hAbd, cA, hCA, hsub, x, a, ha, hnull⟩
  · exact ⟨B, hBfin, hB, hBc, hBo, subset_union_right.trans hcover.subset,
      hBbd, cB, hCB, hsub, x, a, ha, hnull⟩

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
  exact hK.exists_boundary_component_kernel_of_interior_inclusion hL hdim hLint
    (isPreconnected_iff_preconnectedSpace.mpr inferInstance) hLc s g hg
    (Subsingleton.elim _ _) hU

end DifferentialGeometry.Topology.PiecewiseLinear

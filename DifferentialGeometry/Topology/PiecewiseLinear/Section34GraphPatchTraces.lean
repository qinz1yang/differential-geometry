/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphBoundaryDisks
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphEdgeDensity
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldRelativeTopology
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
private theorem vertex_inter_residual_mem_closure_boundary_sdiff
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hA : IsCombinatorialManifoldWithBoundary 3 A) (hAK : A.faces ⊆ K.faces)
    {x : E} (hxA : {x} ∈ A.faces)
    (hxR : {x} ∈ (subcomplexGeneratedBy K A.facesᶜ).faces) :
    x ∈ closure ((boundaryComplex 3 A).space \ (boundaryComplex 3 K).space) := by
  classical
  let B := boundaryComplex 3 A
  let D := boundaryComplex 3 K
  let I := restrict B D.space
  let LA := SimplicialComplex.geometricLink A {x}
  let LK := SimplicialComplex.geometricLink K {x}
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 A).to_subtype
  let _ : Finite D.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  let _ : Finite LA.faces :=
    ((Set.toFinite A.faces).subset (geometricLink_faces_subset A {x})).to_subtype
  let _ : Finite LK.faces :=
    ((Set.toFinite K.faces).subset (geometricLink_faces_subset K {x})).to_subtype
  have hBA : B.faces ⊆ A.faces := boundaryComplex_faces_subset 3 A
  have hBK : B.faces ⊆ K.faces := hBA.trans hAK
  have hDK : D.faces ⊆ K.faces := boundaryComplex_faces_subset 3 K
  have hLAK : LA.space ⊆ LK.space := space_mono_of_faces_subset
    (fun _ ht => ⟨ht.1, ht.2.1, hAK ht.2.2⟩)
  have hnot := not_geometricLink_space_subset_of_mem_subcomplexGeneratedBy_compl K A hAK
    hxA hxR
  have hxspace : x ∈ A.space := A.subset_space hxA (Finset.mem_singleton_self x)
  have hxres : x ∈ closure (K.space \ A.space) := by
    rw [closure_space_sdiff_space_eq_subcomplexGeneratedBy K K A Subset.rfl hAK]
    exact (subcomplexGeneratedBy K A.facesᶜ).subset_space hxR (Finset.mem_singleton_self x)
  have hxB : x ∈ B.space := inter_closure_sdiff_space_subset_boundaryComplex K A hK hA hAK
    ⟨hxspace, hxres⟩
  by_contra hxcl
  have hDnear : D.space ∈ 𝓝[B.space] x := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isClosed_closure.isOpen_compl.mem_nhds hxcl)]
      with y hyB hycl
    by_contra hyD
    exact hycl (subset_closure ⟨hyB, hyD⟩)
  have hxD : x ∈ D.space := mem_of_mem_nhdsWithin hxB hDnear
  have hIspace : I.space = B.space ∩ D.space :=
    restrict_space_eq_inter_of_faces_subset K B D hBK hDK
  have hInear : I.space ∈ 𝓝[B.space] x := by
    rw [hIspace]
    exact Filter.inter_mem self_mem_nhdsWithin hDnear
  have hlink := geometricLink_eq_of_space_mem_nhdsWithin (restrict_faces_subset B D.space)
    hInear
  have hID : I.faces ⊆ D.faces := fun _ hs =>
    ((mem_restrict_faces_iff_of_faces_subset K B D hBK hDK).mp hs).2
  have hbound : (boundaryComplex 2 LA).space ⊆ (boundaryComplex 2 LK).space := by
    rw [← geometricLink_boundaryComplex, ← geometricLink_boundaryComplex, ← hlink]
    exact space_mono_of_faces_subset fun _ hs => ⟨hs.1, hs.2.1, hID hs.2.2⟩
  have hAball : IsPLBall 2 LA.space :=
    (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision A A hA
      (IsSubdivision.refl _) hxA).mpr hxB
  have hKball : IsPLBall 2 LK.space :=
    (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision K K hK
      (IsSubdivision.refl _) (hAK hxA)).mpr hxD
  have hbdEq := eq_of_subset_of_isPLSphere
    (isPLSphere_boundaryComplex_space_of_isPLBall LA hAball)
    (isPLSphere_boundaryComplex_space_of_isPLBall LK hKball) hbound
  have heq := eq_of_isPLBall_of_boundaryComplex_subset LK hKball hAball hLAK
    (hbdEq.symm.subset.trans (boundaryComplex_space_subset 2 LA))
  exact hnot heq.symm.subset

open Classical in
theorem inter_closure_sdiff_eq_closure_boundary_sdiff_three
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hA : IsCombinatorialManifoldWithBoundary 3 A) (hAK : A.space ⊆ K.space) :
    A.space ∩ closure (K.space \ A.space) =
      closure ((boundaryComplex 3 A).space \ (boundaryComplex 3 K).space) := by
  classical
  apply Subset.antisymm
  · rintro x ⟨hxA, hxR⟩
    obtain ⟨R, hR, hRfin, hxRvertex⟩ := exists_isSubdivision_singleton_mem K (hAK hxA)
    let _ : Finite R.faces := hRfin.to_subtype
    obtain ⟨T, hT, hTfin, hTA⟩ := exists_isSubdivision_restrict_isSubdivision R A
      (hR.space_eq.symm ▸ hAK)
    let _ : Finite T.faces := hTfin.to_subtype
    let B := restrict T A.space
    let C := subcomplexGeneratedBy T B.facesᶜ
    let _ : Finite B.faces := (restrict_faces_finite T A.space).to_subtype
    have hBT := restrict_faces_subset T A.space
    have hxT : {x} ∈ T.faces := hT.singleton_mem hxRvertex
    have hxB : {x} ∈ B.faces := ⟨hxT, by simpa using hxA⟩
    have hCspace : C.space = closure (K.space \ A.space) := by
      rw [show C = subcomplexGeneratedBy T B.facesᶜ from rfl,
        ← closure_space_sdiff_space_eq_subcomplexGeneratedBy T T B Subset.rfl hBT,
        hTA.space_eq, hT.space_eq, hR.space_eq]
    have hxC : {x} ∈ C.faces := mem_faces_of_mem_openSimplex_of_mem_space
      (subcomplexGeneratedBy_faces_subset T B.facesᶜ) hxT (mem_openSimplex_singleton x)
      (hCspace.symm ▸ hxR)
    have hx := vertex_inter_residual_mem_closure_boundary_sdiff T B
      (hK.of_isSubdivision (hT.trans hR)) (hA.of_isSubdivision hTA) hBT hxB hxC
    rwa [boundaryComplex_space_of_isSubdivision K T hK (hT.trans hR),
      boundaryComplex_space_of_isSubdivision A B hA hTA] at hx
  · let _ : Finite (boundaryComplex 3 A).faces :=
      (boundaryComplex_faces_finite 3 A).to_subtype
    apply closure_minimal _ ((isPolyhedron_space A).isClosed.inter isClosed_closure)
    rintro x ⟨hxB, hxKbd⟩
    refine ⟨boundaryComplex_space_subset 3 A hxB, ?_⟩
    by_contra hxcl
    have hnear : A.space ∈ 𝓝[K.space] x := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (isClosed_closure.isOpen_compl.mem_nhds hxcl)]
        with y hyK hycl
      by_contra hyA
      exact hycl (subset_closure ⟨hyK, hyA⟩)
    exact hxKbd ((mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin K A hK hA hAK
      (boundaryComplex_space_subset 3 A hxB) hnear).mp hxB)

open Classical in
private theorem closure_disk_boundary_sdiff_subset_complement_family
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) {ι : Type*} [Finite ι]
    (D : ι → Geometry.SimplicialComplex ℝ E) (hDfin : ∀ i, (D i).faces.Finite)
    (hD : ∀ i, IsPLBall 2 (D i).space) (hDS : ∀ i, (D i).space ⊆ S.space)
    (hdis : Pairwise fun i j => Disjoint (D i).space (D j).space)
    {A : Set E} (hA : IsClosed A) (i : ι) :
    closure ((boundaryComplex 2 (D i)).space \ A) ⊆
      closure (S.space \ (A ∪ ⋃ j, (D j).space)) := by
  classical
  let _ : Finite (D i).faces := (hDfin i).to_subtype
  obtain ⟨r, hr⟩ := hD i
  have hbd := hS.inter_closure_sdiff_eq_image_stdSimplexBoundary S hr (hDS i)
  rw [hr.image_stdSimplexBoundary_eq_boundaryComplex (D i) rfl] at hbd
  let O := ⋃ j : {j : ι // j ≠ i}, (D j.1).space
  have hO : IsClosed O := isClosed_iUnion_of_finite fun j => by
    let _ : Finite (D j.1).faces := (hDfin j.1).to_subtype
    exact (isPolyhedron_space (D j.1)).isClosed
  apply closure_minimal _ isClosed_closure
  rintro x ⟨hxB, hxA⟩
  have hxD := boundaryComplex_space_subset 2 (D i) hxB
  have hxO : x ∉ O := by
    intro hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
    exact disjoint_left.mp (hdis j.2.symm) hxD hxj
  have hxcl : x ∈ closure (S.space \ (D i).space) := (hbd.symm ▸ hxB).2
  have hxlocal := (hA.isOpen_compl.inter hO.isOpen_compl).inter_closure
    ⟨⟨hxA, hxO⟩, hxcl⟩
  apply closure_mono (fun y hy => ?_) hxlocal
  refine ⟨hy.2.1, ?_⟩
  rintro (hyA | hyD)
  · exact hy.1.1 hyA
  · obtain ⟨j, hyj⟩ := mem_iUnion.mp hyD
    by_cases hji : j = i
    · exact hy.2.2 (hji ▸ hyj)
    · exact hy.1.2 (mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩)

open Classical in
theorem graphDualCell_free_boundary_subset_residual
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (hv : {v} ∈ L.faces) :
    closure ((boundaryComplex 3 (graphDualCell K L v)).space \
      (((graphDualCell K L v).space ∩ (boundaryComplex 3 K).space) ∪
        ⋃ e : {e : Finset E // e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e},
          (splittingDisk K e.1 (hL e.2.1)).space)) ⊆
      (graphDualCell K L v).space ∩ closure (K.space \ (derivedNeighborhood K L).space) := by
  classical
  let C := graphDualCell K L v
  let N := derivedNeighborhood K L
  let _ : Finite C.faces := (graphDualCell_faces_finite K L v).to_subtype
  let _ : Finite L.faces := ((Set.toFinite K.faces).subset hL).to_subtype
  let V := {w : E // {w} ∈ L.faces ∧ w ≠ v}
  have hVfin : {w : E | {w} ∈ L.faces ∧ w ≠ v}.Finite :=
    (SimplicialComplex.finite_vertices L).subset fun _ hw => hw.1
  let _ : Finite V := hVfin.to_subtype
  let O := ⋃ w : V, (graphDualCell K L w.1).space
  have hOc : IsClosed O := isClosed_iUnion_of_finite fun w => by
    let _ : Finite (graphDualCell K L w.1).faces :=
      (graphDualCell_faces_finite K L w.1).to_subtype
    exact (isPolyhedron_space _).isClosed
  have hC : IsPLBall 3 C.space := hK.isPLBall_graphDualCell K L hL hcard hv
  have hCK : C.space ⊆ K.space :=
    (graphDualCell_space_subset K L v).trans (derivedNeighborhood_space_subset K L)
  have hcover : N.space ⊆ C.space ∪ O := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp ((iUnion_graphDualCell_space K L hL).symm ▸ hx)
    by_cases hwv : w = v
    · exact Or.inl (show x ∈ (graphDualCell K L v).space from hwv ▸ hxw)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨w, hw, hwv⟩, hxw⟩)
  apply closure_minimal _ ((isPolyhedron_space C).isClosed.inter isClosed_closure)
  rintro x ⟨hxB, hxD⟩
  have hxC := boundaryComplex_space_subset 3 C hxB
  have hxKbd : x ∉ (boundaryComplex 3 K).space := fun hx => hxD (Or.inl ⟨hxC, hx⟩)
  have hxO : x ∉ O := by
    intro hx
    obtain ⟨w, hxw⟩ := mem_iUnion.mp hx
    have hvw : v ≠ w.1 := Ne.symm w.2.2
    have he : {v, w.1} ∈ L.faces := by
      by_contra he
      have hem := graphDualCell_space_inter_eq_empty K L hL hcard hv w.2.1 hvw he
      have hi : x ∈ (graphDualCell K L v).space ∩ (graphDualCell K L w.1).space :=
        ⟨hxC, hxw⟩
      rw [hem] at hi
      exact hi
    have hxE := (graphDualCell_space_inter K L hL hcard hvw he).subset ⟨hxC, hxw⟩
    exact hxD (Or.inr (mem_iUnion.mpr
      ⟨⟨{v, w.1}, he, Finset.card_pair hvw, Finset.mem_insert_self _ _⟩, hxE⟩))
  refine ⟨hxC, ?_⟩
  by_contra hxR
  have hNnear : N.space ∈ 𝓝[K.space] x := by
    have hO := isClosed_closure.isOpen_compl.mem_nhds hxR
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hO] with y hyK hyO
    by_contra hyN
    exact hyO (subset_closure ⟨hyK, hyN⟩)
  have hCnear : C.space ∈ 𝓝[K.space] x := by
    filter_upwards [hNnear, mem_nhdsWithin_of_mem_nhds (hOc.isOpen_compl.mem_nhds hxO)]
      with y hyN hyO
    exact (hcover hyN).resolve_right hyO
  exact hxKbd ((mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin K C hK
    hC.isCombinatorialManifoldWithBoundary hCK hxC hCnear).mp hxB)

open Classical in
theorem graphDualCell_inter_residual_subset_boundary
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (hv : {v} ∈ L.faces) :
    (graphDualCell K L v).space ∩ closure (K.space \ (derivedNeighborhood K L).space) ⊆
      (boundaryComplex 3 (graphDualCell K L v)).space := by
  let C := graphDualCell K L v
  let _ : Finite C.faces := (graphDualCell_faces_finite K L v).to_subtype
  have hC := hK.isPLBall_graphDualCell K L hL hcard hv
  have hCN := graphDualCell_space_subset K L v
  exact (inter_subset_inter_right C.space (closure_mono (sdiff_subset_sdiff_right hCN))).trans
    (inter_closure_sdiff_subset_boundaryComplex K C hK hC.isCombinatorialManifoldWithBoundary
      (hCN.trans (derivedNeighborhood_space_subset K L)))

open Classical in
private theorem graphDualCell_inter_residual_eq_free_boundary_of_split_density
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (hv : {v} ∈ L.faces)
    (hden : ∀ e : {e : Finset E // e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e},
      (splittingDisk K e.1 (hL e.2.1)).space ∩
          closure (K.space \ (derivedNeighborhood K L).space) ⊆
        closure ((boundaryComplex 2 (splittingDisk K e.1 (hL e.2.1))).space \
          (boundaryComplex 3 K).space)) :
    (graphDualCell K L v).space ∩ closure (K.space \ (derivedNeighborhood K L).space) =
      closure ((boundaryComplex 3 (graphDualCell K L v)).space \
        (((graphDualCell K L v).space ∩ (boundaryComplex 3 K).space) ∪
          ⋃ e : {e : Finset E // e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e},
            (splittingDisk K e.1 (hL e.2.1)).space)) := by
  classical
  let C := graphDualCell K L v
  let S := boundaryComplex 3 C
  let I := {e : Finset E // e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e}
  let D : I → Geometry.SimplicialComplex ℝ E := fun e => splittingDisk K e.1 (hL e.2.1)
  let _ : Finite C.faces := (graphDualCell_faces_finite K L v).to_subtype
  let _ : Finite S.faces := (boundaryComplex_faces_finite 3 C).to_subtype
  let _ : Finite (boundaryComplex 3 K).faces :=
    (boundaryComplex_faces_finite 3 K).to_subtype
  have hIfin : {e : Finset E | e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e}.Finite :=
    (Set.toFinite K.faces).subset fun _ he => hL he.1
  let _ : Finite I := hIfin.to_subtype
  have hDfin (e : I) : (D e).faces.Finite := splittingDisk_faces_finite K (hL e.2.1)
  have hC : IsPLBall 3 C.space := hK.isPLBall_graphDualCell K L hL hcard hv
  have hS : IsCombinatorialManifold 2 S :=
    isCombinatorialManifold_boundaryComplex C hC.isCombinatorialManifoldWithBoundary
  have hD (e : I) : IsPLBall 2 (D e).space :=
    hK.isPLBall_splittingDisk K (hL e.2.1) e.2.2.1 (by omega)
  have hDS (e : I) : (D e).space ⊆ S.space :=
    hK.splittingDisk_subset_boundary_graphDualCell K L hL hcard e.2.1 e.2.2.1 e.2.2.2
  have hdis : Pairwise fun e f : I => Disjoint (D e).space (D f).space := by
    intro e f hef
    exact disjoint_splittingDisk_space K (hL e.2.1) (hL f.2.1)
      (fun heq => hef (Subtype.ext heq)) (e.2.2.1.trans f.2.2.1.symm)
  have hfree : S.space \ ((boundaryComplex 3 K).space ∪ ⋃ e : I, (D e).space) =
      S.space \ ((C.space ∩ (boundaryComplex 3 K).space) ∪ ⋃ e : I, (D e).space) := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1, fun hx' => hx.2 (hx'.imp And.right id)⟩
    · rintro ⟨hxS, hx⟩
      exact ⟨hxS, fun hx' => hx (hx'.imp
        (fun hxB => ⟨boundaryComplex_space_subset 3 C hxS, hxB⟩) id)⟩
  apply Subset.antisymm _ (graphDualCell_free_boundary_subset_residual K L hK hL hcard hv)
  rintro x ⟨hxC, hxR⟩
  change x ∈ closure (S.space \ ((C.space ∩ (boundaryComplex 3 K).space) ∪
    ⋃ e : I, (D e).space))
  rw [← hfree]
  by_cases hxD : x ∈ ⋃ e : I, (D e).space
  · obtain ⟨e, hxe⟩ := mem_iUnion.mp hxD
    exact closure_disk_boundary_sdiff_subset_complement_family S hS D hDfin hD hDS hdis
      (isPolyhedron_space (boundaryComplex 3 K)).isClosed e (hden e ⟨hxe, hxR⟩)
  · have hxcl : x ∈ closure (S.space \ (boundaryComplex 3 K).space) := by
      rw [← inter_closure_sdiff_eq_closure_boundary_sdiff_three K C hK
        hC.isCombinatorialManifoldWithBoundary
          ((graphDualCell_space_subset K L v).trans (derivedNeighborhood_space_subset K L))]
      exact ⟨hxC, closure_mono
        (sdiff_subset_sdiff_right (graphDualCell_space_subset K L v)) hxR⟩
    have hclosed : IsClosed (⋃ e : I, (D e).space) := isClosed_iUnion_of_finite fun e => by
      let _ : Finite (D e).faces := (hDfin e).to_subtype
      exact (isPolyhedron_space (D e)).isClosed
    have hxlocal := hclosed.isOpen_compl.inter_closure ⟨hxD, hxcl⟩
    apply closure_mono (fun y hy => ?_) hxlocal
    exact ⟨hy.2.1, fun h => h.elim hy.2.2 hy.1⟩

open Classical in
theorem graphDualCell_inter_residual_eq_free_boundary
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hL : L.faces ⊆ (boundaryComplex 3 K).faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (hv : {v} ∈ L.faces) :
    (graphDualCell K L v).space ∩ closure (K.space \ (derivedNeighborhood K L).space) =
      closure ((boundaryComplex 3 (graphDualCell K L v)).space \
        (((graphDualCell K L v).space ∩ (boundaryComplex 3 K).space) ∪
          ⋃ e : {e : Finset E // e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e},
            (splittingDisk K e.1 (boundaryComplex_faces_subset 3 K (hL e.2.1))).space)) := by
  have hLK := hL.trans (boundaryComplex_faces_subset 3 K)
  apply graphDualCell_inter_residual_eq_free_boundary_of_split_density K L hK hLK hcard hv
  intro e
  exact splittingDisk_inter_residual_subset_closure_boundary_sdiff_boundary K L hK hLK
    e.2.1 (hL e.2.1) e.2.2.1 (fun s hs => e.2.2.1.symm ▸ hcard s hs)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_graphDualCell_inter_residual
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hL : L.faces ⊆ (boundaryComplex 3 K).faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (hv : {v} ∈ L.faces) :
    IsPLBall 2 ((graphDualCell K L v).space ∩
      closure (K.space \ (PiecewiseLinear.derivedNeighborhood K L).space)) := by
  classical
  let I := {e : Finset E // e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e}
  have hIfin : {e : Finset E | e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e}.Finite :=
    (Set.toFinite K.faces).subset fun _ he => boundaryComplex_faces_subset 3 K (hL he.1)
  let _ : Finite I := hIfin.to_subtype
  let _ : Fintype I := Fintype.ofFinite I
  rw [graphDualCell_inter_residual_eq_free_boundary K L hK hL hcard hv]
  simpa only [Finset.mem_univ, iUnion_true] using
    hK.isPLBall_graphDualCell_free_boundary K L hL hcard hv (Finset.univ : Finset I)

end DifferentialGeometry.Topology.PiecewiseLinear

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryComplement
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellBoundaryRemainder
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellIncidence
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellResidualTrace
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldComplement
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldRelativeTopology

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem mem_faces_of_dualCell_inter_subcomplex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K A : Geometry.SimplicialComplex ℝ E) (hAK : A.faces ⊆ K.faces)
    {e : Finset E} (he : e ∈ K.faces) {x : E}
    (hxD : x ∈ (dualCell K e he).space) (hxA : x ∈ A.space) : e ∈ A.faces := by
  have hxAb : x ∈ (barycentricSubdivision A).space :=
    (barycentricSubdivision_isSubdivision A).space_eq.symm ▸ hxA
  obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (barycentricSubdivision A) hxAb
  have huD := mem_faces_of_mem_openSimplex_of_mem_space (dualCell_faces_subset K he)
    (barycentricSubdivision_faces_subset hAK hu) hxu hxD
  obtain ⟨d, hd, hne, rfl⟩ := hu
  have hsub := (mem_dualCell_faces_iff_of_flag he (hd.of_le hAK) hne).mp huD
  obtain ⟨s, hs⟩ := hne
  exact A.down_closed (hd.mem_faces hs) (hsub s hs) (K.nonempty_of_mem_faces he)

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
private theorem exists_outer_boundary_parametrization_and_residual
    (M K L : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hLK : L.faces ⊆ K.faces) (hcard : ∀ s ∈ L.faces, s.card ≤ 2)
    (hint : K.space ⊆ interior M.space) {v : E3} (hv : {v} ∈ L.faces)
    (hvbd : {v} ∈ (boundaryComplex 3 K).faces) :
    let Q := subcomplexGeneratedBy M K.facesᶜ
    let G := restrict L Q.space
    let I := {e : Finset E3 // e ∈ L.faces ∧ e.card = 2}
    let U := K.space ∪ ⋃ e : I, (splittingDisk M e.1 (hKM (hLK e.2.1))).space
    ∃ q : (Fin 3 → ℝ) → E3,
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
        (closure (frontier (graphDualCell M L v).space \ U)) ∧
      q '' stdSimplexBoundary 2 =
        closure (frontier (graphDualCell M L v).space \ U) ∩ U ∧
      closure (frontier (graphDualCell M L v).space \ U) =
        (graphDualCell Q G v).space ∩ closure (Q.space \ (derivedNeighborhood Q G).space) := by
  dsimp only
  let dNative : DecidableEq E3 := inferInstance
  let : DecidableEq E3 := Classical.decEq E3
  have hBK : @boundaryComplex E3 _ _ dNative 3 K = boundaryComplex 3 K :=
    congrArg (fun d : DecidableEq E3 => @boundaryComplex E3 _ _ d 3 K)
      (Subsingleton.elim _ _)
  have hvbdLocal : {v} ∈ (boundaryComplex 3 K).faces := hBK ▸ hvbd
  let _ : Finite K.faces := ((Set.toFinite M.faces).subset hKM).to_subtype
  let Q := subcomplexGeneratedBy M K.facesᶜ
  let G := restrict L Q.space
  let C := graphDualCell M L v
  let A := graphDualCell Q G v
  let F := boundaryComplex 3 A
  let I := {e : Finset E3 // e ∈ L.faces ∧ e.card = 2}
  let J := {e : Finset E3 // e ∈ G.faces ∧ e.card = 2 ∧ v ∈ e}
  have hLM : L.faces ⊆ M.faces := hLK.trans hKM
  have hQM : Q.faces ⊆ M.faces := subcomplexGeneratedBy_faces_subset M K.facesᶜ
  let U := K.space ∪ ⋃ e : I, (splittingDisk M e.1 (hLM e.2.1)).space
  let _ : Finite Q.faces := (subcomplexGeneratedBy_faces_finite M K.facesᶜ).to_subtype
  let _ : Finite C.faces := (graphDualCell_faces_finite M L v).to_subtype
  let _ : Finite A.faces := (graphDualCell_faces_finite Q G v).to_subtype
  have hKsp : K.space ⊆ M.space := space_mono_of_faces_subset hKM
  have hQsp : Q.space = closure (M.space \ K.space) := by
    exact (closure_space_sdiff_space_eq_subcomplexGeneratedBy M M K Subset.rfl hKM).symm
  have hMbd : (boundaryComplex 3 M).space = frontier M.space :=
    (frontier_space_eq_boundaryComplex_space (n := 2) hM).symm
  have hdis : Disjoint K.space (boundaryComplex 3 M).space := by
    rw [hMbd]
    exact disjoint_left.mpr fun x hxK hxB => hxB.2 (hint hxK)
  have htrace : IsCombinatorialManifoldWithBoundary 2
      (restrict K (boundaryComplex 3 M).space) := by
    intro x hx
    exact (disjoint_left.mp hdis
      (K.subset_space hx.1 (Finset.mem_singleton_self _)) (hx.2 (by simp))).elim
  have hQ : IsCombinatorialManifoldWithBoundary 3 Q := hM.complement M K hK hKM htrace
  have hKQ : K.space ∩ Q.space = (boundaryComplex 3 K).space := by
    rw [hQsp]
    exact inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary M K hM hK hKsp hdis
  have hKQbd : K.space ∩ Q.space ⊆ (boundaryComplex 3 Q).space :=
    inter_space_complement_subset_boundaryComplex M K Q hM hK hKsp hQ hQsp
  have hQbd : (boundaryComplex 3 Q).space ⊆ (boundaryComplex 3 M).space ∪ K.space := by
    rw [show Q = subcomplexGeneratedBy M K.facesᶜ from rfl,
      boundaryComplex_complement_space M K hM hK hKM hQ]
    apply union_subset
    · exact (closure_minimal sdiff_subset
        (isPolyhedron_space (boundaryComplex 3 M)).isClosed).trans subset_union_left
    · exact (closure_minimal
        (sdiff_subset.trans (boundaryComplex_space_subset 3 K))
        (isPolyhedron_space K).isClosed).trans subset_union_right
  have hvQsp : v ∈ Q.space := by
    have hvKbd := (boundaryComplex 3 K).subset_space hvbdLocal (Finset.mem_singleton_self _)
    exact (hKQ.symm ▸ hvKbd).2
  have hvQ : {v} ∈ Q.faces := mem_faces_of_mem_openSimplex_of_mem_space hQM (hLM hv)
    (by simpa only [Finset.centroid_singleton, id_eq] using
      centroid_mem_openSimplex (Finset.singleton_nonempty v)) hvQsp
  have hGQ : G.faces ⊆ Q.faces := by
    intro s hs
    exact ((mem_restrict_faces_iff_of_faces_subset M L Q hLM hQM).mp hs).2
  have hGB : G.faces ⊆ (boundaryComplex 3 Q).faces := by
    intro s hs
    have hcs : s.centroid ℝ id ∈ convexHull ℝ (s : Set E3) :=
      s.centroid_mem_convexHull (L.nonempty_of_mem_faces hs.1)
    apply mem_faces_of_mem_openSimplex_of_mem_space (boundaryComplex_faces_subset 3 Q)
      (hGQ hs) (centroid_mem_openSimplex_of_mem_faces Q s (hGQ hs))
    exact hKQbd ⟨K.convexHull_subset_space (hLK hs.1) hcs, hs.2 hcs⟩
  have hvG : {v} ∈ G.faces := ⟨hv, by simpa using hvQsp⟩
  have hGcard : ∀ s ∈ G.faces, s.card ≤ 2 := fun s hs => hcard s hs.1
  have hC : IsPLBall 3 C.space := hM.isPLBall_graphDualCell M L hLM hcard hv
  have hA : IsPLBall 3 A.space := hQ.isPLBall_graphDualCell Q G hGQ hGcard hvG
  have hCA : C.space ∩ Q.space = A.space :=
    graphDualCell_space_inter_subcomplex_restrict M Q L hQM hLM hvQ
  have hAC : A.space ⊆ C.space := hCA.symm.subset.trans inter_subset_left
  have hAQ : A.space ⊆ Q.space := hCA.symm.subset.trans inter_subset_right
  have hCM : C.space ⊆ M.space :=
    (graphDualCell_space_subset M L v).trans (derivedNeighborhood_space_subset M L)
  have hCint : C.space ⊆ interior M.space :=
    (graphDualCell_space_subset M L v).trans
      (derivedNeighborhood_space_subset_interior (n := 2) (by simp)
        hM hLM ((space_mono_of_faces_subset hLK).trans hint))
  have hCnotB : ∀ x ∈ C.space, x ∉ (boundaryComplex 3 M).space := by
    intro x hxC hxB
    exact (hMbd ▸ hxB).2 (hCint hxC)
  let UQ := (boundaryComplex 3 Q).space ∪
    ⋃ e : J, (splittingDisk Q e.1 (hGQ e.2.1)).space
  have hremove : ∀ x ∈ A.space, x ∈ UQ ↔ x ∈ U := by
    intro x hxA
    have hxC := hAC hxA
    have hxQ := hAQ hxA
    constructor
    · rintro (hxB | hxD)
      · exact Or.inl ((hQbd hxB).resolve_left (hCnotB x hxC))
      · obtain ⟨e, hxe⟩ := mem_iUnion.mp hxD
        right
        refine mem_iUnion.mpr ⟨⟨e.1, e.2.1.1, e.2.2.1⟩, ?_⟩
        have heq := splittingDisk_space_inter_subcomplex M Q hQM (hGQ e.2.1)
        exact (heq.symm ▸ hxe).1
    · rintro (hxK | hxD)
      · exact Or.inl (hKQbd ⟨hxK, hxQ⟩)
      · obtain ⟨e, hxe⟩ := mem_iUnion.mp hxD
        have heQ : e.1 ∈ Q.faces := mem_faces_of_dualCell_inter_subcomplex M Q hQM
          (hLM e.2.1) (splittingDisk_space_subset_dualCell M (hLM e.2.1) hxe) hxQ
        have heG : e.1 ∈ G.faces := ⟨e.2.1, Q.convexHull_subset_space heQ⟩
        have hve : v ∈ e.1 := mem_of_graphDualCell_inter_splittingDisk_nonempty M L
          (hLM hv) (hLM e.2.1) ⟨x, hxC, hxe⟩
        right
        refine mem_iUnion.mpr ⟨⟨e.1, heG, e.2.2, hve⟩, ?_⟩
        rw [← splittingDisk_space_inter_subcomplex M Q hQM heQ]
        exact ⟨hxe, hxQ⟩
  have hboundary : ∀ x ∈ A.space, x ∉ K.space →
      (x ∈ F.space ↔ x ∈ frontier C.space) := by
    intro x hxA hxK
    have hnhds : A.space ∈ 𝓝[C.space] x := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds ((isPolyhedron_space K).isClosed.isOpen_compl.mem_nhds hxK)]
        with y hyC hyK
      rw [← hCA]
      exact ⟨hyC, hQsp.symm ▸ subset_closure ⟨hCM hyC, hyK⟩⟩
    have h := mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin C A
      hC.isCombinatorialManifoldWithBoundary hA.isCombinatorialManifoldWithBoundary
      hAC hxA hnhds
    rwa [← frontier_space_eq_boundaryComplex_space (n := 2)
      hC.isCombinatorialManifoldWithBoundary] at h
  have hfree : F.space \ UQ = frontier C.space \ U := by
    ext x
    constructor
    · rintro ⟨hxF, hxUQ⟩
      have hxA := boundaryComplex_space_subset 3 A hxF
      have hxU : x ∉ U := fun h => hxUQ ((hremove x hxA).mpr h)
      exact ⟨(hboundary x hxA (fun h => hxU (Or.inl h))).mp hxF, hxU⟩
    · rintro ⟨hxF, hxU⟩
      have hxC := hC.isPolyhedron.isClosed.frontier_subset hxF
      have hxK : x ∉ K.space := fun h => hxU (Or.inl h)
      have hxQ : x ∈ Q.space := hQsp.symm ▸ subset_closure ⟨hCM hxC, hxK⟩
      have hxA : x ∈ A.space := hCA ▸ ⟨hxC, hxQ⟩
      exact ⟨(hboundary x hxA hxK).mpr hxF,
        fun h => hxU ((hremove x hxA).mp h)⟩
  obtain ⟨q, hq, hqb⟩ :=
    hQ.exists_isPLHomeomorphOn_graphDualCell_boundary_remainder Q G hGB hGcard hvG
  change IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (closure (F.space \ UQ)) at hq
  change q '' stdSimplexBoundary 2 = closure (F.space \ UQ) ∩ UQ at hqb
  have hOutA : closure (F.space \ UQ) ⊆ A.space :=
    closure_minimal (sdiff_subset.trans (boundaryComplex_space_subset 3 A))
      hA.isPolyhedron.isClosed
  have hmeet : closure (F.space \ UQ) ∩ UQ = closure (F.space \ UQ) ∩ U := by
    ext x
    exact and_congr_right fun hx => hremove x (hOutA hx)
  rw [hmeet, hfree] at hqb
  rw [hfree] at hq
  have hres := graphDualCell_inter_residual_eq_boundary_remainder Q G hQ hGQ hGcard hvG
  change A.space ∩ closure (Q.space \ (derivedNeighborhood Q G).space) =
    closure (F.space \ UQ) at hres
  rw [hfree] at hres
  have hNQ : @derivedNeighborhood E3 _ _ dNative Q G = derivedNeighborhood Q G :=
    congrArg (fun d : DecidableEq E3 => @derivedNeighborhood E3 _ _ d Q G)
      (Subsingleton.elim _ _)
  refine ⟨q, hq, hqb, ?_⟩
  rw [hNQ]
  exact hres.symm

open Classical in
theorem exists_isPLHomeomorphOn_graphDualCell_outer_boundary
    (M K L : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hLK : L.faces ⊆ K.faces) (hcard : ∀ s ∈ L.faces, s.card ≤ 2)
    (hint : K.space ⊆ interior M.space) {v : E3} (hv : {v} ∈ L.faces)
    (hvbd : {v} ∈ (boundaryComplex 3 K).faces) :
    let I := {e : Finset E3 // e ∈ L.faces ∧ e.card = 2}
    let U := K.space ∪ ⋃ e : I, (splittingDisk M e.1 (hKM (hLK e.2.1))).space
    ∃ q : (Fin 3 → ℝ) → E3,
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
        (closure (frontier (graphDualCell M L v).space \ U)) ∧
      q '' stdSimplexBoundary 2 =
        closure (frontier (graphDualCell M L v).space \ U) ∩ U := by
  obtain ⟨q, hq, hqb, -⟩ := exists_outer_boundary_parametrization_and_residual
    M K L hM hK hKM hLK hcard hint hv hvbd
  exact ⟨q, hq, hqb⟩

open Classical in
theorem graphDualCell_outer_boundary_eq_residual
    (M K L : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hLK : L.faces ⊆ K.faces) (hcard : ∀ s ∈ L.faces, s.card ≤ 2)
    (hint : K.space ⊆ interior M.space) {v : E3} (hv : {v} ∈ L.faces)
    (hvbd : {v} ∈ (boundaryComplex 3 K).faces) :
    let Q := subcomplexGeneratedBy M K.facesᶜ
    let G := restrict L Q.space
    let I := {e : Finset E3 // e ∈ L.faces ∧ e.card = 2}
    let U := K.space ∪ ⋃ e : I, (splittingDisk M e.1 (hKM (hLK e.2.1))).space
    closure (frontier (graphDualCell M L v).space \ U) =
      (graphDualCell Q G v).space ∩ closure (Q.space \ (derivedNeighborhood Q G).space) := by
  obtain ⟨-, -, -, hres⟩ := exists_outer_boundary_parametrization_and_residual
    M K L hM hK hKM hLK hcard hint hv hvbd
  exact hres

end DifferentialGeometry.Topology.PiecewiseLinear

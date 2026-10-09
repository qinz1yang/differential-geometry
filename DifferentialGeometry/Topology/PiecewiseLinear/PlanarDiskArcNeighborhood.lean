/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitBoundaryTrace
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodPolygon
import DifferentialGeometry.Topology.PiecewiseLinear.DisplacedArcConnected
import DifferentialGeometry.Topology.PiecewiseLinear.JoinTransport

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

open Classical in
private theorem derivedNeighborhood_restrict_core
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K A B : Geometry.SimplicialComplex ℝ E) (hAK : A.faces ⊆ K.faces)
    (hBK : B.faces ⊆ K.faces) :
    derivedNeighborhood B A = derivedNeighborhood B (restrict A B.space) := by
  classical
  ext s
  constructor
  · rintro ⟨D, hD, hDne, hmeet, rfl⟩
    refine ⟨D, hD, hDne, ?_, rfl⟩
    intro e he
    obtain ⟨t, ht, hte⟩ := hmeet e he
    have hcent : t.centroid ℝ id ∈ B.space := by
      rw [← (barycentricSubdivision_isSubdivision B).space_eq]
      exact (barycentricSubdivision B).convexHull_subset_space (hD.mem_faces he)
        (subset_convexHull ℝ _ hte)
    have htB := mem_faces_of_mem_openSimplex_of_mem_space hBK (hAK ht)
      (centroid_mem_openSimplex (A.nonempty_of_mem_faces ht)) hcent
    exact ⟨t, ⟨ht, B.convexHull_subset_space htB⟩, hte⟩
  · intro hs
    exact derivedNeighborhood_faces_mono Subset.rfl (restrict_faces_subset A B.space) hs

open Classical in
private theorem derivedNeighborhood_inter_boundaryComplex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n m : ℕ} (K A B : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite B.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hB : IsCombinatorialManifoldWithBoundary (m + 1) B)
    (hBK : B.faces ⊆ K.faces)
    (hNdis : Disjoint (derivedNeighborhood K A).space (boundaryComplex (n + 1) K).space)
    (hQdis : Disjoint (derivedNeighborhood B A).space (boundaryComplex (m + 1) B).space) :
    (derivedNeighborhood B A).space ∩
        (boundaryComplex (n + 1) (derivedNeighborhood K A)).space =
      (boundaryComplex (m + 1) (derivedNeighborhood B A)).space := by
  classical
  let N := derivedNeighborhood K A
  let Q := derivedNeighborhood B A
  let _ : Finite N.faces := (derivedNeighborhood_faces_finite K A).to_subtype
  let _ : Finite Q.faces := (derivedNeighborhood_faces_finite B A).to_subtype
  have hNK : N.space ⊆ K.space := derivedNeighborhood_space_subset K A
  have hQB : Q.space ⊆ B.space := derivedNeighborhood_space_subset B A
  have hQN : Q.space ⊆ N.space := by
    intro x hx
    exact ((derivedNeighborhood_space_inter_subcomplex K B A hBK).symm.subset hx).1
  have hboundaryN := inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary
    K N hK (hK.derivedNeighborhood A) hNK hNdis
  have hboundaryQ := inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary
    B Q hB (hB.derivedNeighborhood A) hQB hQdis
  have htrace := space_inter_closure_sdiff_derivedNeighborhood_eq K A B hBK
  rw [← hboundaryN, ← hboundaryQ, ← htrace]
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨hxQ, -, hxC⟩
    exact ⟨hxQ, hQB hxQ, hxC⟩
  · rintro ⟨hxQ, -, hxC⟩
    exact ⟨hxQ, hQN hxQ, hxC⟩

theorem IsPLBall.exists_isPLBall_neighborhood_with_arc_traces
    {ι : Type*} [Finite ι] {D U : Set Plane} (hD : IsPLBall 2 D)
    (hU : IsOpen U) (hDU : D ⊆ U) (A : ι → Set Plane)
    (q : ι → (Fin 2 → ℝ) → Plane)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) (A i))
    (hDA : ∀ i, IsPLBall 1 (D ∩ A i))
    (hends : ∀ i, Disjoint D (q i '' stdSimplexBoundary 1)) :
    ∃ Q : Set Plane, IsPLBall 2 Q ∧ D ⊆ interior Q ∧ Q ⊆ U ∧
      ∀ i, IsPLBall 1 (A i ∩ Q) ∧
        ∀ r : (Fin 2 → ℝ) → Plane,
          IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) (A i ∩ Q) →
          r '' stdSimplexBoundary 1 = A i ∩ frontier Q := by
  classical
  let _ : DecidableEq Plane := Classical.decEq _
  have hA (i : ι) : IsPLBall 1 (A i) := ⟨q i, hq i⟩
  have hcompact : IsCompact (D ∪ ⋃ i, A i) :=
    hD.isPolyhedron.isCompact.union (isCompact_iUnion (fun i => (hA i).isPolyhedron.isCompact))
  obtain ⟨r, hr⟩ := hcompact.isBounded.subset_ball (0 : Plane)
  obtain ⟨T, hT, hTcard, hTP⟩ := exists_affineIndependent_openSimplex_superset 2
    (by simp) (isBounded_ball (x := (0 : Plane)) (r := r))
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hKspace : K.space = convexHull ℝ (T : Set Plane) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hKball : IsPLBall 2 K.space := by
    rw [hKspace]
    exact isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hinside : D ∪ ⋃ i, A i ⊆ interior K.space := by
    apply hr.trans
    apply interior_maximal _ isOpen_ball
    rw [hKspace]
    exact hTP.trans (openSimplex_subset_convexHull T)
  let H := ⋃ i, q i '' stdSimplexBoundary 1
  have hH : IsClosed H := isClosed_iUnion_of_finite (fun i =>
    (hq i).isPLSphere_image_stdSimplexBoundary.isPolyhedron.isClosed)
  let W := U ∩ interior K.space ∩ Hᶜ
  have hW : IsOpen W := (hU.inter isOpen_interior).inter hH.isOpen_compl
  have hDW : D ⊆ W := by
    intro x hx
    refine ⟨⟨hDU hx, hinside (Or.inl hx)⟩, ?_⟩
    intro hxH
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxH
    exact disjoint_left.mp (hends i) hx hxi
  let P : Option ι → Set Plane
    | none => D
    | some i => A i
  have hP : ∀ i, IsPolyhedron (P i) := by
    rintro (_ | i)
    · exact hD.isPolyhedron
    · exact (hA i).isPolyhedron
  have hPK : ∀ i, P i ⊆ K.space := by
    rintro (_ | i) x hx
    · exact interior_subset (hinside (Or.inl hx))
    · exact interior_subset (hinside (Or.inr (mem_iUnion.mpr ⟨i, hx⟩)))
  let V : Bool → Set Plane
    | false => W
    | true => Dᶜ
  have hV : ∀ i, IsOpen (((↑) : K.space → Plane) ⁻¹' V i) := by
    intro i
    cases i
    · exact hW.preimage continuous_subtype_val
    · exact hD.isPolyhedron.isClosed.isOpen_compl.preimage continuous_subtype_val
  have hcover : K.space ⊆ ⋃ i, V i := by
    intro x _
    by_cases hx : x ∈ D
    · exact mem_iUnion.mpr ⟨false, hDW hx⟩
    · exact mem_iUnion.mpr ⟨true, hx⟩
  obtain ⟨R, hRK, hRfin, hPR, hstars⟩ :=
    exists_isSubdivision_subcomplexes_closedStars_subset_cover K P hP hPK V hV hcover
  let _ : Finite R.faces := hRfin.to_subtype
  let L := restrict R D
  let _ : Finite L.faces := (restrict_faces_finite R D).to_subtype
  have hLD : L.space = D := hPR none
  have hLR : L.faces ⊆ R.faces := restrict_faces_subset R D
  have hRball : IsPLBall 2 R.space := hRK.space_eq.symm ▸ hKball
  have hLball : IsPLBall 2 L.space := hLD.symm ▸ hD
  let N := derivedNeighborhood R L
  let _ : Finite N.faces := (derivedNeighborhood_faces_finite R L).to_subtype
  have hNball : IsPLBall 2 N.space := by
    have hm := hRball.isCombinatorialManifoldWithBoundary
    exact hm.isPLBall_derivedNeighborhood_of_isGlueIso_planar_subcomplex_in_surface
      hLR hLball (isGlueIso_id L)
  have hstars₂ : ∀ s ∈ (secondDerived R).faces,
      ∃ i, (⋃ v ∈ s, closedStar (secondDerived R) v) ⊆ V i :=
    (secondDerived_isSubdivision R).closedStars_subset_cover hstars
  have hNW : N.space ⊆ W := by
    change (derivedNeighborhood R L).space ⊆ W
    rw [← iUnion_derivedNeighborhoodCell_space R L hLR]
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    have hc : {s.centroid ℝ id} ∈ (secondDerived R).faces :=
      (barycentricSubdivision_isSubdivision (barycentricSubdivision R)).singleton_mem
        (singleton_centroid_mem_barycentricSubdivision R (hLR hs))
    obtain ⟨i, hi⟩ := hstars₂ _ hc
    have hi' : closedStar (secondDerived R) (s.centroid ℝ id) ⊆ V i := by
      simpa only [Finset.set_biUnion_singleton] using hi
    cases i
    · exact hi' (derivedNeighborhoodCell_space_eq_closedStar R (hLR hs) ▸ hxs)
    · have hcent : s.centroid ℝ id ∈ D :=
        hLD ▸ L.convexHull_subset_space hs (s.centroid_mem_convexHull (L.nonempty_of_mem_faces hs))
      exact (hi' (mem_closedStar_self _ hc) hcent).elim
  have hDN : D ⊆ interior N.space := by
    intro x hx
    apply mem_interior_iff_mem_nhds.mpr
    have hn := derivedNeighborhood_mem_nhdsWithin hLR (hLD.symm ▸ hx)
    have hRnhds : R.space ∈ 𝓝 x := by
      rw [hRK.space_eq]
      exact mem_interior_iff_mem_nhds.mp (hinside (Or.inl hx))
    rwa [nhdsWithin_eq_nhds.mpr hRnhds] at hn
  have hNdis : Disjoint N.space (boundaryComplex 2 R).space := by
    rw [← frontier_space_eq_boundaryComplex_space hRball.isCombinatorialManifoldWithBoundary]
    exact disjoint_left.mpr fun x hx hxb => hxb.2 (by
      rw [hRK.space_eq]
      exact (hNW hx).1.2)
  refine ⟨N.space, hNball, hDN, fun x hx => (hNW hx).1.1, ?_⟩
  intro i
  let B := restrict R (A i)
  let _ : Finite B.faces := (restrict_faces_finite R (A i)).to_subtype
  have hBA : B.space = A i := hPR (some i)
  have hBR : B.faces ⊆ R.faces := restrict_faces_subset R (A i)
  let C := restrict L B.space
  let _ : Finite C.faces := (restrict_faces_finite L B.space).to_subtype
  have hCspace : C.space = D ∩ A i := by
    rw [restrict_space_eq_inter_of_faces_subset R L B hLR hBR, hLD, hBA]
  have hCB : C.faces ⊆ B.faces := by
    intro s hs
    exact mem_faces_of_mem_openSimplex_of_mem_space hBR (hLR hs.1)
      (centroid_mem_openSimplex (L.nonempty_of_mem_faces hs.1))
      (hs.2 (s.centroid_mem_convexHull (L.nonempty_of_mem_faces hs.1)))
  have hCball : IsPLBall 1 C.space := hCspace.symm ▸ hDA i
  let Q := derivedNeighborhood B L
  let _ : Finite Q.faces := (derivedNeighborhood_faces_finite B L).to_subtype
  have hQtrace : Q.space = A i ∩ N.space := by
    rw [inter_comm, ← hBA]
    exact (derivedNeighborhood_space_inter_subcomplex R B L hBR).symm
  have hQeq : Q = derivedNeighborhood B C := derivedNeighborhood_restrict_core R L B hLR hBR
  have hQconn : IsConnected Q.space := by
    rw [hQeq]
    exact isConnected_derivedNeighborhood_space hCB hCball.isConnected
  have hCQ : C.space ⊆ Q.space := by
    rw [hQeq]
    exact subcomplex_space_subset_derivedNeighborhood hCB
  have hQball : IsPLBall 1 Q.space :=
    (hA i).isPLBall_one_of_isCompact_of_isConnected (isPolyhedron_space Q).isCompact hQconn
      (hCball.nontrivial.mono hCQ)
      ((derivedNeighborhood_space_subset B L).trans hBA.subset)
  have hqB : IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) B.space := hBA.symm ▸ hq i
  have hBball : IsPLBall 1 B.space := ⟨q i, hqB⟩
  have hBbd : (boundaryComplex 1 B).space = q i '' stdSimplexBoundary 1 := by
    simpa only [simplexBoundary_stdVertices_space] using
      boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex B hqB
  have hQdis : Disjoint Q.space (boundaryComplex 1 B).space := by
    rw [hBbd]
    refine disjoint_left.mpr fun x hx hxend => ?_
    have hxN := (hQtrace ▸ hx).2
    exact (hNW hxN).2 (mem_iUnion.mpr ⟨i, hxend⟩)
  have hbd := derivedNeighborhood_inter_boundaryComplex R L B
    hRball.isCombinatorialManifoldWithBoundary hBball.isCombinatorialManifoldWithBoundary
      hBR hNdis hQdis
  refine ⟨hQtrace ▸ hQball, ?_⟩
  intro s hs
  have hsQ : IsPLHomeomorphOn s (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) Q.space := hQtrace.symm ▸ hs
  have hsbd : (boundaryComplex 1 Q).space = s '' stdSimplexBoundary 1 := by
    simpa only [simplexBoundary_stdVertices_space] using
      boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex Q hsQ
  rw [← hsbd, ← hbd, ← frontier_space_eq_boundaryComplex_space
    hNball.isCombinatorialManifoldWithBoundary, hQtrace]
  ext x
  exact ⟨fun hx => ⟨hx.1.1, hx.2⟩,
    fun hx => ⟨⟨hx.1, hNball.isPolyhedron.isClosed.frontier_subset hx.2⟩, hx.2⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear

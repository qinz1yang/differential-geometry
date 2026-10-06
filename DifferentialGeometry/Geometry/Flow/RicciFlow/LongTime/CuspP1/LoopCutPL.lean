/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCutting
import DifferentialGeometry.Topology.PiecewiseLinear.MobiusEmbedding

set_option autoImplicit false

open Set Topology DifferentialGeometry.Topology.PiecewiseLinear

namespace GC.LongTime.CuspP1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A preconnected subset of `K \ L` lies in `R` or misses `R`, when `R` is closed and `R \ L`
is open in `K`. -/
theorem subset_or_disjoint_LTP3 {K L R S : Set E} (hRc : IsClosed R)
    (hopen : ∀ x ∈ R \ L, R ∈ 𝓝[K] x)
    (hS : IsPreconnected S) (hSK : S ⊆ K) (hSL : Disjoint S L) :
    S ⊆ R ∨ Disjoint S R := by
  classical
  choose O hO hxO hOR using fun x : ↥(R \ L) => mem_nhdsWithin.mp (hopen x.1 x.2)
  let v : Set E := ⋃ x : ↥(R \ L), O x
  have hv : IsOpen v := isOpen_iUnion hO
  by_cases hmeet : (S ∩ R).Nonempty
  · left
    by_contra hnot
    obtain ⟨z, hzS, hzR⟩ := not_subset.mp hnot
    obtain ⟨w, hwS, hwR⟩ := hmeet
    obtain ⟨y, hy, hyv, hyR⟩ := hS v Rᶜ hv hRc.isOpen_compl
      (fun s hs => by
        by_cases h : s ∈ R
        · exact Or.inl (mem_iUnion.mpr ⟨⟨s, h, fun hl => disjoint_left.mp hSL hs hl⟩,
            hxO _⟩)
        · exact Or.inr h)
      ⟨w, hwS, mem_iUnion.mpr ⟨⟨w, hwR, fun hl => disjoint_left.mp hSL hwS hl⟩, hxO _⟩⟩
      ⟨z, hzS, hzR⟩
    obtain ⟨⟨x, hx⟩, hyx⟩ := mem_iUnion.mp hyv
    exact hyR (hOR ⟨x, hx⟩ ⟨hyx, hSK hy⟩)
  · right
    exact disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hmeet)
end


open Classical in
/-- Local one-sided ball pair at a point `p ∈ L ∩ R`. -/
theorem exists_side_ball_pair_LTP3
    {K L R : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) (hB : Disjoint L.space (boundaryComplex 3 K).space)
    (hRK : R.space ⊆ K.space)
    (hopen : ∀ x ∈ R.space \ L.space, R.space ∈ 𝓝[K.space] x)
    (hdense : ∀ p ∈ L.space ∩ R.space, p ∈ closure (R.space \ L.space))
    (hone : ∀ p ∈ L.space ∩ R.space, p ∈ closure (K.space \ R.space))
    {p : E} (hp : p ∈ L.space ∩ R.space) :
    ∃ C D : Set E, IsPLBall 3 C ∧ IsPLBall 3 D ∧ C ⊆ R.space ∧ C ∈ 𝓝[R.space] p ∧
      D ⊆ K.space ∧ p ∈ C ∩ D ∧ IsPLBall 2 (C ∩ D) ∧
      ∃ N ∈ 𝓝[K.space] p, L.space ∩ N ⊆ C := by
  have hRc : IsClosed R.space := (isPolyhedron_space R).isClosed
  obtain ⟨W, -, hW, hWnhds, htrace, x, -, y, -, -, hcover, hX, hY, hclcover, hclmeet⟩ :=
    hK.exists_isPLBall_neighborhood_pair_sdiff hL hLK hp.1
      (fun hpB => disjoint_left.mp hB hp.1 hpB) Filter.univ_mem
  have hWK : W ⊆ K.space := hW.trans inter_subset_left
  set X := connectedComponentIn (W \ L.space) x with hXdef
  set Y := connectedComponentIn (W \ L.space) y with hYdef
  have hXs : X ⊆ W \ L.space := connectedComponentIn_subset _ _
  have hYs : Y ⊆ W \ L.space := connectedComponentIn_subset _ _
  have hXdis : Disjoint X L.space := disjoint_left.mpr fun z hz hzL => (hXs hz).2 hzL
  have hYdis : Disjoint Y L.space := disjoint_left.mpr fun z hz hzL => (hYs hz).2 hzL
  have hXc : IsPreconnected X := isPreconnected_connectedComponentIn
  have hYc : IsPreconnected Y := isPreconnected_connectedComponentIn
  have hX2 := subset_or_disjoint_LTP3 hRc hopen hXc ((hXs.trans sdiff_subset).trans hWK) hXdis
  have hY2 := subset_or_disjoint_LTP3 hRc hopen hYc ((hYs.trans sdiff_subset).trans hWK) hYdis
  have hpL := hp.1
  have hpR := hp.2
  have hpX := hclmeet.symm.subset ⟨mem_of_mem_nhdsWithin (hLK hpL) hWnhds, hpL⟩
  -- a point of `R \ L` near `p` lies in `X ∪ Y`
  have hnear : ∀ {z : E}, z ∈ W → z ∈ K.space → z ∉ L.space → z ∈ X ∪ Y := fun hz hzK hzL =>
    hcover.symm.subset ⟨hz, hzL⟩
  obtain ⟨O, hO, hpO, hOW⟩ := mem_nhdsWithin.mp hWnhds
  have hdn : ∃ q ∈ O, q ∈ R.space \ L.space := by
    obtain ⟨q, hqO, hqR⟩ := mem_closure_iff.mp (hdense p hp) O hO hpO
    exact ⟨q, hqO, hqR⟩
  have hon : ∃ q ∈ O, q ∈ K.space \ R.space := by
    obtain ⟨q, hqO, hqR⟩ := mem_closure_iff.mp (hone p hp) O hO hpO
    exact ⟨q, hqO, hqR⟩
  obtain ⟨q, hqO, hqR, hqL⟩ := hdn
  obtain ⟨q', hq'O, hq'K, hq'R⟩ := hon
  have hqXY := hnear (hOW ⟨hqO, hRK hqR⟩) (hRK hqR) hqL
  -- one of the two sides is in `R`
  have hKc : IsClosed K.space := (isPolyhedron_space K).isClosed
  have hpW : p ∈ W := mem_of_mem_nhdsWithin (hLK hpL) hWnhds
  have hcl : closure X ∩ closure Y = W ∩ L.space := hclmeet
  have hcov : X ∪ Y = W \ L.space := hcover
  have hWR : W ∈ 𝓝[R.space] p := nhdsWithin_mono p hRK hWnhds
  have finish : ∀ (P Q : Set E), P ∪ Q = W \ L.space → closure P ∩ closure Q = W ∩ L.space →
      Q ⊆ K.space → P ⊆ R.space → Disjoint Q R.space → IsPLBall 3 (closure P) →
      IsPLBall 3 (closure Q) →
      ∃ C D : Set E, IsPLBall 3 C ∧ IsPLBall 3 D ∧ C ⊆ R.space ∧ C ∈ 𝓝[R.space] p ∧
        D ⊆ K.space ∧ p ∈ C ∩ D ∧ IsPLBall 2 (C ∩ D) ∧
          ∃ N ∈ 𝓝[K.space] p, L.space ∩ N ⊆ C := by
    intro P Q hPQ hPQcl hQK hPR hQR hPb hQb
    refine ⟨closure P, closure Q, hPb, hQb, closure_minimal hPR hRc, ?_,
      closure_minimal hQK hKc, hPQcl.symm ▸ ⟨hpW, hpL⟩, hPQcl.symm ▸ htrace,
      W, hWnhds, fun z hz => (hPQcl.symm.subset ⟨hz.2, hz.1⟩).1⟩
    apply Filter.mem_of_superset (Filter.inter_mem hWR self_mem_nhdsWithin)
    rintro z ⟨hzW, hzR⟩
    by_cases hzL : z ∈ L.space
    · exact (hPQcl.symm.subset ⟨hzW, hzL⟩).1
    · rcases hPQ.symm.subset ⟨hzW, hzL⟩ with hzP | hzQ
      · exact subset_closure hzP
      · exact (disjoint_left.mp hQR hzQ hzR).elim
  have hXK : X ⊆ K.space := (hXs.trans sdiff_subset).trans hWK
  have hYK : Y ⊆ K.space := (hYs.trans sdiff_subset).trans hWK
  by_cases hXR : X ⊆ R.space
  · have hYR : Disjoint Y R.space := by
      refine hY2.resolve_left fun hYR => ?_
      have hq'W : q' ∈ W := hOW ⟨hq'O, hq'K⟩
      by_cases hq'L : q' ∈ L.space
      · exact hq'R (closure_minimal hXR hRc (hcl.symm.subset ⟨hq'W, hq'L⟩).1)
      · rcases hcov.symm.subset ⟨hq'W, hq'L⟩ with h | h
        · exact hq'R (hXR h)
        · exact hq'R (hYR h)
    exact finish X Y hcov hcl hYK hXR hYR hX hY
  · have hXd : Disjoint X R.space := hX2.resolve_left hXR
    have hYR : Y ⊆ R.space := by
      rcases hqXY with h | h
      · exact (disjoint_left.mp hXd h hqR).elim
      · exact (hY2.resolve_right (fun hd => disjoint_left.mp hd h hqR))
    exact finish Y X (by rw [union_comm]; exact hcov) (by rw [inter_comm]; exact hcl)
      hXK hYR hXd hY hX

open Classical in
/-- **P3 core.** A one-sided closed piece `R` of a 3-manifold complex `K` cut along a
2-manifold polyhedron `L ⊆ int K` is a combinatorial 3-manifold with boundary
`(L ∩ R) ∪ (R ∩ ∂K)`.  The three side hypotheses are exactly what a bicollar with
`σ p ∈ W ↔ 0 ≤ s`, `W` closed, `W \ torus ⊆ interior W` provides (LT-P1/LT-P2). -/
theorem isCombinatorialManifoldWithBoundary_of_oneSided_LTP3
    {K L R : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) (hB : Disjoint L.space (boundaryComplex 3 K).space)
    (hRK : R.space ⊆ K.space)
    (hopen : ∀ x ∈ R.space \ L.space, R.space ∈ 𝓝[K.space] x)
    (hdense : ∀ p ∈ L.space ∩ R.space, p ∈ closure (R.space \ L.space))
    (hone : ∀ p ∈ L.space ∩ R.space, p ∈ closure (K.space \ R.space)) :
    IsCombinatorialManifoldWithBoundary 3 R ∧
      (boundaryComplex 3 R).space = (L.space ∩ R.space) ∪ (R.space ∩ (boundaryComplex 3 K).space) := by
  have hman : IsCombinatorialManifoldWithBoundary 3 R := by
    apply isCombinatorialManifoldWithBoundary_of_isPLBall_neighborhoods R
    intro p hp
    by_cases hpL : p ∈ L.space
    · obtain ⟨C, D, hC, -, hsub, hnhds, -, -, -, -⟩ :=
        exists_side_ball_pair_LTP3 hK hL hLK hB hRK hopen hdense hone ⟨hpL, hp⟩
      exact ⟨C, hC, hsub, hnhds⟩
    · obtain ⟨C, hC, hsub, hnhds⟩ :=
        hK.exists_isPLBall_subset_of_mem_nhdsWithin (hRK hp) (hopen p ⟨hp, hpL⟩)
      exact ⟨C, hC, hsub.trans inter_subset_right, nhdsWithin_mono p hRK hnhds⟩
  refine ⟨hman, ?_⟩
  apply Subset.antisymm
  · intro p hp
    have hpR := boundaryComplex_space_subset 3 R hp
    by_cases hpL : p ∈ L.space
    · exact Or.inl ⟨hpL, hpR⟩
    · exact Or.inr ⟨hpR, (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin
        K R hK hman hRK hpR (hopen p ⟨hpR, hpL⟩)).mp hp⟩
  · rintro p (⟨hpL, hpR⟩ | ⟨hpR, hpB⟩)
    · obtain ⟨C, D, hC, hD, hsub, hnhds, hDK, hpI, hI, -⟩ :=
        exists_side_ball_pair_LTP3 hK hL hLK hB hRK hopen hdense hone ⟨hpL, hpR⟩
      obtain ⟨Q, hQfin, hQC⟩ := hC.isPolyhedron.exists_simplicialComplex
      let _ : Finite Q.faces := hQfin.to_subtype
      have hQ : IsPLBall 3 Q.space := hQC.symm ▸ hC
      have hQR : Q.space ⊆ R.space := by rwa [hQC]
      have hQnhds : Q.space ∈ 𝓝[R.space] p := by rwa [hQC]
      have hpQ : p ∈ Q.space := hQC.symm.subset hpI.1
      have hpB : p ∈ (boundaryComplex 3 Q).space :=
        hK.inter_subset_boundaryComplex_of_isPLBall Q hQ (hQR.trans hRK) hD hDK
          (by rwa [hQC]) ⟨hpQ, hpI.2⟩
      exact (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin R Q hman
        hQ.isCombinatorialManifoldWithBoundary hQR hpQ hQnhds).mp hpB
    · exact inter_boundaryComplex_space_subset_of_subset K R hK hman hRK ⟨hpR, hpB⟩

open Classical in
/-- A closed subset `W` of `K` that is open away from `L` and the closure of its part off `L`
is a polyhedron. -/
theorem isPolyhedron_of_clopen_sdiff_LTP3
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hLK : L.space ⊆ K.space) {W : Set E} (hWK : W ⊆ K.space) (hWc : IsClosed W)
    (hopen : ∀ x ∈ W \ L.space, W ∈ 𝓝[K.space] x)
    (hdense : ∀ p ∈ L.space ∩ W, p ∈ closure (W \ L.space)) : IsPolyhedron W := by
  obtain ⟨T, hT, hTfin, hTL⟩ := exists_isSubdivision_restrict_isSubdivision K L hLK
  let _ : Finite T.faces := hTfin.to_subtype
  let A := restrict T L.space
  let Z := restrict T W
  let _ : Finite A.faces := (restrict_faces_finite T L.space).to_subtype
  let _ : Finite Z.faces := (restrict_faces_finite T W).to_subtype
  have hA : A.space = L.space := hTL.space_eq
  have hTK : T.space = K.space := hT.space_eq
  have hAT : A.faces ⊆ T.faces := restrict_faces_subset T L.space
  have hZc : IsClosed Z.space := (isPolyhedron_space Z).isClosed
  have hdiff : W \ L.space ⊆ Z.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex T (hTK.symm ▸ hWK hx.1)
    have hsA : s ∉ A.faces := fun h => hx.2 (hA ▸ A.convexHull_subset_space h
      (openSimplex_subset_convexHull s hxs))
    have hopenS : openSimplex s ⊆ K.space \ L.space := fun y hy =>
      ⟨hTK ▸ T.convexHull_subset_space hs (openSimplex_subset_convexHull s hy),
        hA ▸ notMem_space_of_notMem_faces hAT hs hsA hy⟩
    have hSW : openSimplex s ⊆ W := by
      rcases subset_or_disjoint_LTP3 hWc hopen (convex_openSimplex s).isPreconnected
        (hopenS.trans sdiff_subset) (disjoint_left.mpr fun y hy hyL => (hopenS hy).2 hyL) with h | h
      · exact h
      · exact (disjoint_left.mp h hxs hx.1).elim
    have hsZ : s ∈ Z.faces := ⟨hs, (convexHull_subset_closure_openSimplex
      (T.nonempty_of_mem_faces hs)).trans (closure_minimal hSW hWc)⟩
    exact Z.convexHull_subset_space hsZ (openSimplex_subset_convexHull s hxs)
  have hWZ : W ⊆ Z.space := by
    intro x hx
    by_cases hxL : x ∈ L.space
    · exact closure_minimal hdiff hZc (hdense x ⟨hxL, hx⟩)
    · exact hdiff ⟨hx, hxL⟩
  have : Z.space = W := Subset.antisymm (restrict_space_subset T W) hWZ
  exact this ▸ isPolyhedron_space Z

open Classical in
/-- **P3 (cutting lemma, subset form).**  Let `K` be a finite combinatorial 3-manifold complex,
`L ⊆ K` a combinatorial 2-manifold polyhedron missing `∂K`, and `W ⊆ K` closed with
(i) `W \ L` open in `K`, (ii) `L ∩ W ⊆ closure (W \ L)`, (iii) `L ∩ W ⊆ closure (K \ W)`.
Then `W` is the space of a finite combinatorial 3-manifold with boundary
`(L ∩ W) ∪ (W ∩ ∂K)`, orientable if `K` is. -/
theorem exists_manifold_of_oneSided_LTP3
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) (hB : Disjoint L.space (boundaryComplex 3 K).space)
    {W : Set E} (hWK : W ⊆ K.space) (hWc : IsClosed W)
    (hopen : ∀ x ∈ W \ L.space, W ∈ 𝓝[K.space] x)
    (hdense : ∀ p ∈ L.space ∩ W, p ∈ closure (W \ L.space))
    (hone : ∀ p ∈ L.space ∩ W, p ∈ closure (K.space \ W)) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (hfin : R.faces.Finite),
      letI := hfin.to_subtype
      R.space = W ∧ IsCombinatorialManifoldWithBoundary 3 R ∧
      (boundaryComplex 3 R).space = (L.space ∩ W) ∪ (W ∩ (boundaryComplex 3 K).space) ∧
      (IsOrientable 3 K → IsOrientable 3 R) := by
  obtain ⟨R, hRfin, hR⟩ := (isPolyhedron_of_clopen_sdiff_LTP3 hLK hWK hWc hopen hdense).exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  subst hR
  obtain ⟨hman, hbd⟩ := isCombinatorialManifoldWithBoundary_of_oneSided_LTP3 hK hL hLK hB hWK
    hopen hdense hone
  exact ⟨R, hRfin, rfl, hman, hbd, fun h => IsOrientable.of_space_subset K R hWK hK hman h⟩

end GC.LongTime.CuspP1

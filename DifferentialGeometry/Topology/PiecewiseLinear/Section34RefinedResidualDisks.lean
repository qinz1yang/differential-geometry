/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorDensity
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RefinedResidualCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CutExhaustion
import DifferentialGeometry.Topology.PlanarJordan.CompactRegion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isPLBall_closure_sdiff_of_inner_frontier_circle
    {D N J : Set (EuclideanSpace ℝ (Fin 2))} (hD : IsPLBall 2 D)
    (hNclosed : IsClosed N) (hNdense : closure (interior N) = N) (hND : N ⊆ D)
    (hnear : N ∈ 𝓝ˢ[D] (frontier D)) (hJ : IsPLSphere 1 J)
    (hdis : Disjoint (frontier D) J) (hfront : frontier N = frontier D ∪ J) :
    IsPLBall 2 (closure (D \ N)) ∧ frontier (closure (D \ N)) = J := by
  let P := closure (D \ N)
  have hPD : P ⊆ D := closure_minimal sdiff_subset hD.isPolyhedron.isClosed
  obtain ⟨O, hO, hbdO, hON⟩ := mem_nhdsSetWithin.mp hnear
  have hPdis : Disjoint P (frontier D) := by
    apply disjoint_left.mpr
    intro x hxP hxbd
    obtain ⟨y, hyO, hyD, hyN⟩ := mem_closure_iff.mp hxP O hO (hbdO hxbd)
    exact hyN (hON ⟨hyO, hyD⟩)
  have hfrontP : frontier P = J := by
    apply Subset.antisymm
    · intro x hx
      have hxP : x ∈ P := isClosed_closure.frontier_subset hx
      have hxbd : x ∉ frontier D := disjoint_left.mp hPdis hxP
      have hx' : x ∈ frontier D ∪ frontier N := by
        have h := frontier_inter_subset D Nᶜ (frontier_closure_subset hx)
        rcases h with h | h
        · exact Or.inl h.1
        · exact Or.inr (frontier_compl N ▸ h.2)
      exact (hfront ▸ hx'.resolve_left hxbd).resolve_left hxbd
    · intro x hxJ
      have hxN : x ∈ frontier N := hfront.symm ▸ Or.inr hxJ
      have hxD : x ∈ interior D :=
        (mem_interior_iff_notMem_frontier (hND (hNclosed.frontier_subset hxN))).mpr
          (fun hxbd => disjoint_left.mp hdis hxbd hxJ)
      have hxP : x ∈ P := closure_mono (inter_subset_inter_left Nᶜ interior_subset)
        (isOpen_interior.inter_closure
          ⟨hxD, (frontier_eq_closure_inter_closure (s := N) ▸ hxN).2⟩)
      refine ⟨subset_closure hxP, ?_⟩
      intro hxint
      have hdisint : Disjoint (interior P) (interior N) := by
        apply disjoint_left.mpr
        intro y hyP hyN
        have hPcompl : P ⊆ (interior N)ᶜ :=
          closure_minimal (fun z hz hzi => hz.2 (interior_subset hzi))
            isOpen_interior.isClosed_compl
        exact hPcompl (interior_subset hyP) hyN
      have hdisN := hdisint.closure_right isOpen_interior
      rw [hNdense] at hdisN
      exact disjoint_left.mp hdisN hxint (hNclosed.frontier_subset hxN)
  have hPcompact : IsCompact P := hD.isPolyhedron.isCompact.of_isClosed_subset
    isClosed_closure hPD
  have hPnonempty : (interior P).Nonempty := by
    obtain ⟨x, hx⟩ := hJ.nonempty
    have hxP : x ∈ P := isClosed_closure.frontier_subset (hfrontP.symm ▸ hx)
    obtain ⟨y, hy⟩ := closure_nonempty_iff.mp ⟨x, hxP⟩
    have hyD : y ∈ interior D :=
      (mem_interior_iff_notMem_frontier hy.1).mpr
        (fun hybd => hy.2 (hON ⟨hbdO hybd, hy.1⟩))
    have hO' : IsOpen (interior D ∩ Nᶜ) :=
      isOpen_interior.inter hNclosed.isOpen_compl
    have hyP := hO'.subset_interior_closure ⟨hyD, hy.2⟩
    exact ⟨y, interior_mono (closure_mono
      (inter_subset_inter_left Nᶜ interior_subset)) hyP⟩
  have hcircle : IsPLSphere 1 (frontier P) := hfrontP.symm ▸ hJ
  have hinside := PlanarJordan.closure_inside_frontier_eq_of_isCompact hPcompact
    (isJordanCurve_of_isPLSphere_one hcircle) hPnonempty
  have hball : IsPLBall 2 P :=
    hinside ▸ isPLBall_closure_inside_of_isPLSphere_one hcircle
  exact ⟨hball, hfrontP⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem isPLBall_closure_sdiff_annulus_of_boundary_neighborhood
    {D N : Set (EuclideanSpace ℝ (Fin 2))} (hD : IsPLBall 2 D)
    {J : Set E} (hJ : IsPLSphere 1 J) {ρ : E × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc 0 1) N) (hND : N ⊆ D)
    (hnear : N ∈ 𝓝ˢ[D] (frontier D)) : IsPLBall 2 (closure (D \ N)) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 2)) := Classical.decEq _
  obtain ⟨A, hAfin, hA, -, hAN, hAbd⟩ := hρ.exists_annulus_complex hJ zero_lt_one
  let _ : Finite A.faces := hAfin.to_subtype
  have hNclosed : IsClosed N := hAN ▸ (isPolyhedron_space A).isClosed
  have hfrontN : frontier N = ρ '' (J ×ˢ {0, 1}) := by
    rw [← hAN, frontier_space_eq_boundaryComplex_space hA, hAbd]
  have hNdense : closure (interior N) = N := by
    apply Subset.antisymm (closure_minimal interior_subset hNclosed)
    have hdense := hA.space_subset_closure_sdiff_boundaryComplex_space
    rw [← frontier_space_eq_boundaryComplex_space hA, self_sdiff_frontier, hAN] at hdense
    exact hdense
  let J₀ := ρ '' (J ×ˢ {(0 : ℝ)})
  let J₁ := ρ '' (J ×ˢ {(1 : ℝ)})
  have hleft : J ×ˢ {(0 : ℝ)} ⊆ J ×ˢ Icc 0 1 :=
    fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨le_rfl, zero_le_one⟩⟩
  have hright : J ×ˢ {(1 : ℝ)} ⊆ J ×ˢ Icc 0 1 :=
    fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨zero_le_one, le_rfl⟩⟩
  have hJ₀ : IsPLSphere 1 J₀ := hJ.of_isPLHomeomorphOn
    ((hJ.isPolyhedron.isPLHomeomorphOn_prod_const (0 : ℝ)).trans
      (hρ.restrict (isPolyhedron_prod_singleton hJ.isPolyhedron (0 : ℝ)) hleft))
  have hJ₁ : IsPLSphere 1 J₁ := hJ.of_isPLHomeomorphOn
    ((hJ.isPolyhedron.isPLHomeomorphOn_prod_const (1 : ℝ)).trans
      (hρ.restrict (isPolyhedron_prod_singleton hJ.isPolyhedron (1 : ℝ)) hright))
  have hdis : Disjoint J₀ J₁ := by
    apply disjoint_left.mpr
    rintro x ⟨u, hu, hux⟩ ⟨v, hv, hvx⟩
    have heq := hρ.bijOn.injOn (hleft hu) (hright hv) (hux.trans hvx.symm)
    have ht := hu.2.symm.trans ((congrArg Prod.snd heq).trans hv.2)
    norm_num at ht
  have hends : frontier N = J₀ ∪ J₁ := by
    rw [hfrontN]
    change ρ '' (J ×ˢ {0, 1}) = ρ '' (J ×ˢ {0}) ∪ ρ '' (J ×ˢ {1})
    rw [← image_union, ← prod_union, singleton_union]
  have hbd : frontier D ⊆ frontier N := by
    obtain ⟨O, -, hbdO, hON⟩ := mem_nhdsSetWithin.mp hnear
    intro x hx
    rw [hNclosed.frontier_eq]
    refine ⟨hON ⟨hbdO hx, hD.isPolyhedron.isClosed.frontier_subset hx⟩, ?_⟩
    exact fun hxN => hx.2 (interior_mono hND hxN)
  have hside := isPreconnected_iff_subset_of_disjoint_closed.mp
    hD.isPLSphere_frontier.isConnected.isPreconnected J₀ J₁
    hJ₀.isPolyhedron.isClosed hJ₁.isPolyhedron.isClosed (hbd.trans hends.subset)
    (by rw [hdis.inter_eq, inter_empty])
  rcases hside with hside | hside
  · have heq := eq_of_subset_of_isPLSphere_one hD.isPLSphere_frontier hJ₀ hside
    exact (isPLBall_closure_sdiff_of_inner_frontier_circle hD hNclosed hNdense hND hnear
      hJ₁ (heq.symm ▸ hdis) (heq.symm ▸ hends)).1
  · have heq := eq_of_subset_of_isPLSphere_one hD.isPLSphere_frontier hJ₁ hside
    exact (isPLBall_closure_sdiff_of_inner_frontier_circle hD hNclosed hNdense hND hnear
      hJ₀ (heq.symm ▸ hdis.symm) (heq.symm ▸ hends.trans (union_comm _ _))).1

open Classical in
theorem isPLBall_closure_sdiff_annulus_of_boundaryComplex_neighborhood
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {N : Set E} {J : Set F} (hJ : IsPLSphere 1 J) {ρ : F × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc 0 1) N) (hNK : N ⊆ K.space)
    (hnear : N ∈ 𝓝ˢ[K.space] (boundaryComplex 2 K).space) :
    IsPLBall 2 (closure (K.space \ N)) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 2)) := Classical.decEq _
  obtain ⟨R, _, hRfin, _, hR, _⟩ := exists_isPLBall_pair_with_segment_inter
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨f, hf⟩ := hK
  obtain ⟨g, hg⟩ := hR
  have hK : IsPLBall 2 K.space := ⟨f, hf⟩
  have hR : IsPLBall 2 R.space := ⟨g, hg⟩
  let u := g ∘ Function.invFunOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
  have hu : IsPLHomeomorphOn u K.space R.space := hf.symm.trans hg
  have hNpoly : IsPolyhedron N := hρ.image_eq ▸
    (hJ.isPolyhedron.prod (isPLBall_Icc zero_lt_one).isPolyhedron).image_of_isPiecewiseAffineOn
      hρ.isPiecewiseAffineOn hρ.bijOn.injOn
  have hρ' := hρ.trans (hu.restrict hNpoly hNK)
  have hbd : u '' (boundaryComplex 2 K).space = frontier R.space := by
    rw [← boundaryComplex_space_of_isPLHomeomorphOn K R
      hK.isCombinatorialManifoldWithBoundary hu,
      ← frontier_space_eq_boundaryComplex_space hR.isCombinatorialManifoldWithBoundary]
  have hnear' : u '' N ∈ 𝓝ˢ[R.space] (frontier R.space) := by
    obtain ⟨O, hO, hBO, hON⟩ := mem_nhdsSetWithin.mp
      (hu.symm.isPiecewiseAffineOn.continuousOn.preimage_mem_nhdsSetWithin hnear)
    refine mem_nhdsSetWithin.mpr ⟨O, hO, ?_, ?_⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hbd.symm.subset hy
      have hxK := boundaryComplex_space_subset 2 K hx
      apply hBO
      exact ⟨hu.bijOn.mapsTo hxK, by
        simpa only [mem_preimage, hu.bijOn.injOn.leftInvOn_invFunOn hxK] using hx⟩
    · intro y hy
      exact ⟨Function.invFunOn u K.space y,
        hON ⟨hy.1, hy.2, hu.symm.bijOn.mapsTo hy.2⟩, hu.bijOn.invOn_invFunOn.2 hy.2⟩
  have hcomp := isPLBall_closure_sdiff_annulus_of_boundary_neighborhood hR hJ hρ'
    ((image_mono hNK).trans hu.image_eq.le) hnear'
  have himage : u '' closure (K.space \ N) = closure (R.space \ u '' N) := by
    rw [hu.image_closure hK.isPolyhedron.isCompact sdiff_subset,
      hu.bijOn.injOn.image_sdiff_subset hNK, hu.image_eq]
  have hpoly := hK.isPolyhedron.closure_sdiff hNpoly
  have hsub : closure (K.space \ N) ⊆ K.space :=
    closure_minimal sdiff_subset hK.isPolyhedron.isClosed
  rw [← himage] at hcomp
  exact hcomp.of_isPLHomeomorphOn (hu.restrict hpoly hsub).symm

open Classical in
theorem isPLBall_closure_sdiff_derivedNeighborhood_boundaryComplex
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space) :
    IsPLBall 2 (closure (K.space \ (derivedNeighborhood K (boundaryComplex 2 K)).space)) := by
  classical
  let B := boundaryComplex 2 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 2 K).to_subtype
  have hB : IsPLSphere 1 B.space := isPLSphere_boundaryComplex_space_of_isPLBall K hK
  obtain ⟨ρ, hρ⟩ := exists_isPLHomeomorphOn_annulus_derivedNeighborhood_circle K B
    hK.isCombinatorialManifoldWithBoundary (boundaryComplex_faces_subset 2 K)
    hB.isCombinatorialManifold hB.isConnected (isOrientable_of_isPLBall hK)
  have hJ : IsPLSphere 1 (stdSimplexBoundary 2) := by
    simpa only [simplexBoundary_stdVertices_space] using isPLSphere_simplexBoundary_std 1
  apply isPLBall_closure_sdiff_annulus_of_boundaryComplex_neighborhood K hK hJ hρ
    (derivedNeighborhood_space_subset K B)
  rw [nhdsSetWithin, Filter.mem_inf_principal, mem_nhdsSet_iff_forall]
  intro x hx
  exact Filter.mem_inf_principal.mp
    (derivedNeighborhood_mem_nhdsWithin (boundaryComplex_faces_subset 2 K) hx)

open Classical in
theorem isPLBall_closure_subcomplex_sdiff_derivedNeighborhood_of_boundary_core
    (K S L : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsPLBall 2 S.space) (hSK : S.faces ⊆ K.faces) (hLK : L.faces ⊆ K.faces)
    (hcore : L.space ∩ S.space = (boundaryComplex 2 S).space) :
    IsPLBall 2 (closure (S.space \ (derivedNeighborhood K L).space)) := by
  have hLS : restrict L S.space = boundaryComplex 2 S :=
    eq_of_faces_subset_of_space_eq _ _ S
      (fun _ hs => ((mem_restrict_faces_iff_of_faces_subset K L S hLK hSK).mp hs).2)
      (boundaryComplex_faces_subset 2 S)
      ((restrict_space_eq_inter_of_faces_subset K L S hLK hSK).trans hcore)
  have heq : S.space \ (derivedNeighborhood K L).space =
      S.space \ (derivedNeighborhood S (boundaryComplex 2 S)).space := by
    rw [← hLS, derivedNeighborhood_restrict_core_eq K S L hSK hLK,
      ← derivedNeighborhood_space_inter_subcomplex K S L hSK]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [heq]
  exact isPLBall_closure_sdiff_derivedNeighborhood_boundaryComplex S hS

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M}

omit [FiniteDimensional ℝ E] in
theorem restrict_graph_core_triangle_eq_simplexBoundary
    (T : LocallyFinitePLPieceIn E 3 M U) (s : Section34SimplexIndex T 3) :
    restrict (restrict T.complex (T.map ⁻¹' graphSkeletonSpace T))
        (convexHull ℝ (s.1 : Set E)) = simplexBoundary s.1 (T.complex.indep s.2.1) := by
  ext t
  constructor
  · rintro ⟨ht, hconv⟩
    obtain ⟨htK, htcard⟩ := (mem_restrict_preimage_graphSkeletonSpace_iff T).mp ht
    have hne := T.complex.nonempty_of_mem_faces htK
    have hts := face_subset_of_mem_openSimplex_of_mem_convexHull T.complex htK s.2.1
      (centroid_mem_openSimplex hne) (hconv (t.centroid_mem_convexHull hne))
    refine ⟨hts, hne, ?_⟩
    intro heq
    have := s.2.2
    have := congrArg Finset.card heq
    omega
  · rintro ⟨hts, hne, hne'⟩
    have hcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hts, hne'⟩)
    refine ⟨(mem_restrict_preimage_graphSkeletonSpace_iff T).mpr
      ⟨T.complex.down_closed s.2.1 hts hne, ?_⟩,
      convexHull_mono (Finset.coe_subset.mpr hts)⟩
    have := s.2.2
    omega

open Classical in
theorem isPLBall_closure_triangle_sdiff_graph_derivedNeighborhood_of_subdivision
    {T T' : LocallyFinitePLPieceIn E 3 M U}
    (hsub : IsSubdivision T'.complex T.complex) (hmap : T'.map = T.map)
    (s : Section34SimplexIndex T 3) :
    IsPLBall 2 (closure (convexHull ℝ (s.1 : Set E) \
      (derivedNeighborhood T'.complex
        (restrict T'.complex (T'.map ⁻¹' graphSkeletonSpace T))).space)) := by
  classical
  let S₀ := simplexComplex s.1 (T.complex.indep s.2.1)
  let B₀ := simplexBoundary s.1 (T.complex.indep s.2.1)
  let S := restrict T'.complex (convexHull ℝ (s.1 : Set E))
  let L := restrict T'.complex (T'.map ⁻¹' graphSkeletonSpace T)
  let L₀ := restrict T.complex (T.map ⁻¹' graphSkeletonSpace T)
  have hS₀space : S₀.space = convexHull ℝ (s.1 : Set E) :=
    simplexComplex_space _ _ (T.complex.nonempty_of_mem_faces s.2.1)
  have hS₀K : S₀.faces ⊆ T.complex.faces :=
    fun _ ht => T.complex.down_closed s.2.1 ht.2 ht.1
  have hSsub : IsSubdivision S S₀ := by
    simpa only [hS₀space] using hsub.restrict S₀ hS₀K
  have hSspace : S.space = convexHull ℝ (s.1 : Set E) := hSsub.space_eq.trans hS₀space
  have hS₀ : IsPLBall 2 S₀.space := hS₀space.symm ▸
    isPLBall_convexHull_of_affineIndependent s.1 (T.complex.indep s.2.1) s.2.2
  have hS : IsPLBall 2 S.space := hSsub.space_eq.symm ▸ hS₀
  let _ : Finite S₀.faces := (simplexComplex_faces_finite _ _).to_subtype
  let _ : Finite S.faces := (T'.restrict_faces_finite_of_isCompact
    (s.1.finite_toSet.isCompact_convexHull ℝ)
      ((T.complex.convexHull_subset_space s.2.1).trans hsub.space_eq.symm.subset)).to_subtype
  have hSbd : (boundaryComplex 2 S).space = B₀.space := by
    rw [boundaryComplex_space_of_isSubdivision S₀ S hS₀.isCombinatorialManifoldWithBoundary
      hSsub, show boundaryComplex 2 S₀ = B₀ from
        boundaryComplex_simplexComplex (T.complex.indep s.2.1) s.2.2]
  have hLspace : L.space = L₀.space :=
    (isSubdivision_restrict_preimage_graphSkeletonSpace hsub hmap).space_eq
  have hcore : L.space ∩ S.space = (boundaryComplex 2 S).space := by
    rw [hSbd, hLspace, hSspace, ← hS₀space,
      ← restrict_space_eq_inter_of_faces_subset T.complex L₀ S₀
        (restrict_faces_subset _ _) hS₀K, hS₀space,
      restrict_graph_core_triangle_eq_simplexBoundary T s]
  rw [← hSspace]
  exact isPLBall_closure_subcomplex_sdiff_derivedNeighborhood_of_boundary_core T'.complex S L
    hS (restrict_faces_subset _ _) (restrict_faces_subset _ _) hcore

end DifferentialGeometry.Topology.PiecewiseLinear

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphSplitBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphArcBoundaries
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphEdgeDensity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
private theorem boundary_restrict_circle_subset_simplexBoundary
    (K R J : Geometry.SimplicialComplex ℝ E) [Finite J.faces]
    (hsub : IsSubdivision R K) (hJR : J.faces ⊆ R.faces) (hJ : IsPLSphere 1 J.space)
    {t : Finset E} (ht : t ∈ K.faces) (hmax : ∀ u ∈ K.faces, t ⊆ u → u = t)
    (hA : IsPLBall 1 (restrict J (convexHull ℝ (t : Set E))).space) :
    (boundaryComplex 1 (restrict J (convexHull ℝ (t : Set E)))).space ⊆
      (simplexBoundary t (K.indep ht)).space := by
  classical
  let A := restrict J (convexHull ℝ (t : Set E))
  let _ : Finite A.faces := ((Set.toFinite J.faces).subset (restrict_faces_subset _ _)).to_subtype
  intro x hx
  obtain ⟨s, hs, hxs⟩ := (boundaryComplex 1 A).mem_space_iff.mp hx
  obtain ⟨u, hu, hsu, hucard, _⟩ := hs.2
  have hscard : s.card = 1 := by
    have hle := (Finset.card_le_card hsu).trans hucard
    have hpos := Finset.card_pos.mpr (A.nonempty_of_mem_faces hs.1)
    omega
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hscard
  have hxv : x = v := by simpa only [Finset.coe_singleton, convexHull_singleton,
    mem_singleton_iff] using hxs
  subst x
  by_contra hvB
  have hvT : v ∈ convexHull ℝ (t : Set E) := hs.1.2 (by simp)
  have hvopen : v ∈ openSimplex t := by
    rw [openSimplex_eq_sdiff_simplexBoundary t (K.indep ht)]
    exact ⟨hvT, hvB⟩
  have hface : ∀ q ∈ J.faces, v ∈ q → q ∈ A.faces := by
    intro q hq hvq
    obtain ⟨p, hp, hqp⟩ := hsub.exists_face_subset (hJR hq)
    have hvp := hqp (subset_convexHull ℝ (q : Set E) hvq)
    have htp : t ⊆ p := face_subset_of_mem_openSimplex_of_mem_convexHull K ht hp hvopen hvp
    exact ⟨hq, (hmax p hp htp) ▸ hqp⟩
  obtain ⟨a, ha⟩ := (hA.isCombinatorialManifoldWithBoundary.mem_boundaryComplex_iff_unique_coface
    A (Finset.card_singleton v)).mp hs
  obtain ⟨b, c, hbc, hco⟩ := hJ.isCombinatorialManifold.codimension_one_cofaces J hs.1.1
    (Finset.card_singleton v)
  have hba : b = a := by
    have hb : b ∉ ({v} : Finset E) ∧ insert b {v} ∈ J.faces := by
      change b ∈ {z | z ∉ ({v} : Finset E) ∧ insert z {v} ∈ J.faces}
      rw [hco]
      exact mem_insert _ _
    have hbA : b ∈ {z | z ∉ ({v} : Finset E) ∧ insert z {v} ∈ A.faces} :=
      ⟨hb.1, hface _ hb.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))⟩
    simpa only [ha, mem_singleton_iff] using hbA
  have hca : c = a := by
    have hc : c ∉ ({v} : Finset E) ∧ insert c {v} ∈ J.faces := by
      change c ∈ {z | z ∉ ({v} : Finset E) ∧ insert z {v} ∈ J.faces}
      rw [hco]
      exact mem_insert_of_mem _ (mem_singleton _)
    have hcA : c ∈ {z | z ∉ ({v} : Finset E) ∧ insert z {v} ∈ A.faces} :=
      ⟨hc.1, hface _ hc.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))⟩
    simpa only [ha, mem_singleton_iff] using hcA
  exact hbc (hba.trans hca.symm)

open Classical in
private theorem isPLSphere_splittingDisk_inter_residual_inter_boundary
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : L.faces ⊆ K.faces)
    {e : Finset E} (he : e ∈ L.faces) (heB : e ∈ (boundaryComplex 3 K).faces)
    (hcard : e.card = 2) (hmax : ∀ s ∈ L.faces, s.card ≤ e.card) :
    IsPLSphere 0 (((splittingDisk K e (hL he)).space ∩
      closure (K.space \ (derivedNeighborhood K L).space)) ∩ (boundaryComplex 3 K).space) := by
  classical
  let D := splittingDisk K e (hL he)
  let R := closure (K.space \ (derivedNeighborhood K L).space)
  let T := D.space ∩ R
  let B := boundaryComplex 3 K
  let G := restrict L B.space
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  let _ : Finite (dualCell K e (hL he)).faces := (dualCell_faces_finite K (hL he)).to_subtype
  have hBS : B.faces ⊆ K.faces := boundaryComplex_faces_subset 3 K
  have hGB : G.faces ⊆ B.faces := fun f hf =>
    ((mem_restrict_faces_iff_of_faces_subset K L B hL hBS).mp hf).2
  have heG : e ∈ G.faces := ⟨he, B.convexHull_subset_space heB⟩
  have hmaxG : ∀ f ∈ G.faces, f.card ≤ e.card := fun f hf => hmax f hf.1
  have hlocal : B.space \ (derivedNeighborhood K L).space =
      B.space \ (derivedNeighborhood B G).space := by
    rw [show G = restrict L B.space from rfl,
      derivedNeighborhood_restrict_core_eq K B L hBS hL,
      ← derivedNeighborhood_space_inter_subcomplex K B L hBS]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  have htrace : T ∩ B.space = (splittingDisk B e heB).space ∩
      closure (B.space \ (derivedNeighborhood B G).space) := by
    change (D.space ∩ R) ∩ B.space = _
    rw [show (D.space ∩ R) ∩ B.space = (D.space ∩ B.space) ∩ (R ∩ B.space) by
      ext x; simp only [mem_inter_iff]; tauto]
    rw [show D.space ∩ B.space = (splittingDisk B e heB).space from
      splittingDisk_space_inter_subcomplex K B hBS heB,
      show R ∩ B.space = closure (B.space \ (derivedNeighborhood K L).space) from
        closure_sdiff_derivedNeighborhood_inter_subcomplex_ambient K K B L (subset_refl _) hBS hL,
      hlocal]
  change IsPLSphere 0 (T ∩ B.space)
  rw [htrace]
  rw [splittingDisk_inter_residual_eq_geometricLink B G hGB heG hmaxG]
  let _ : Finite (dualCell B e heB).faces := (dualCell_faces_finite B heB).to_subtype
  rw [isPLSphere_geometricLink_iff_of_isSubdivision
    (barycentricSubdivision_isSubdivision (dualCell B e heB))
    (singleton_centroid_mem_dualCell B heB), geometricLink_dualCell]
  exact (isCombinatorialManifold_boundaryComplex K hK).isPLSphere_upperLink B heB
    (k := 1) hcard (by omega)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [T2Space M] {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

open Classical in
theorem isPLCellOn_section34GraphEdgeArc_with_rim_boundary
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK : IsCombinatorialManifoldWithBoundary 3 𝒦.complex)
    (hK' : IsCombinatorialManifold 3 𝒦'.complex)
    (t : Section34SimplexIndex 𝒦 4) (e : Section34EdgeIndex 𝒦 𝒦')
    (het : Section34Incident e.1 t.1) :
    IsPLCellOn 1 (section34GraphSplitCell 𝒦 𝒦' e ∩
      section34GraphResidualCell 𝒦 𝒦' t.1)
      ((section34GraphSplitCell 𝒦 𝒦' e ∩ section34GraphResidualCell 𝒦 𝒦' t.1) ∩
        simplexRim 𝒦 t.1) := by
  classical
  let S₀ := simplexComplex t.1 (𝒦.complex.indep t.2.1)
  let B₀ := simplexBoundary t.1 (𝒦.complex.indep t.2.1)
  let S := restrict 𝒦'.complex (convexHull ℝ (t.1 : Set Ea))
  let L := restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)
  let L₀ := restrict 𝒦.complex (𝒦.map ⁻¹' graphSkeletonSpace 𝒦)
  let G := restrict L S.space
  have hS₀space : S₀.space = convexHull ℝ (t.1 : Set Ea) :=
    simplexComplex_space _ _ (𝒦.complex.nonempty_of_mem_faces t.2.1)
  have hS₀K : S₀.faces ⊆ 𝒦.complex.faces :=
    fun _ ht => 𝒦.complex.down_closed t.2.1 ht.2 ht.1
  have hSsub : IsSubdivision S S₀ := by
    simpa only [hS₀space] using hsub.restrict S₀ hS₀K
  have hSspace : S.space = convexHull ℝ (t.1 : Set Ea) := hSsub.space_eq.trans hS₀space
  have hS₀ : IsPLBall 3 S₀.space := hS₀space.symm ▸
    isPLBall_convexHull_of_affineIndependent t.1 (𝒦.complex.indep t.2.1) t.2.2
  have hS : IsPLBall 3 S.space := hSsub.space_eq.symm ▸ hS₀
  let _ : Finite S₀.faces := (simplexComplex_faces_finite _ _).to_subtype
  let _ : Finite S.faces := (𝒦'.restrict_faces_finite_of_isCompact
    (t.1.finite_toSet.isCompact_convexHull ℝ)
      ((𝒦.complex.convexHull_subset_space t.2.1).trans hsub.space_eq.symm.subset)).to_subtype
  have hSbd : (boundaryComplex 3 S).space = B₀.space := by
    rw [boundaryComplex_space_of_isSubdivision S₀ S hS₀.isCombinatorialManifoldWithBoundary
      hSsub, show boundaryComplex 3 S₀ = B₀ from
        boundaryComplex_simplexComplex (𝒦.complex.indep t.2.1) t.2.2]
  have hcore := isSubdivision_restrict_preimage_graphSkeletonSpace hsub hmap
  have hGS : G.faces ⊆ S.faces := fun f hf =>
    ((mem_restrict_faces_iff_of_faces_subset 𝒦'.complex L S
      (restrict_faces_subset _ _) (restrict_faces_subset _ _)).mp hf).2
  have heS : e.1 ∈ S.faces := ⟨e.2.1,
    convexHull_min het (convex_convexHull ℝ (t.1 : Set Ea))⟩
  have heL : e.1 ∈ L.faces := ⟨e.2.1, fun x hx => e.2.2.2 (mem_image_of_mem _ hx)⟩
  have heG : e.1 ∈ G.faces := ⟨heL, hSspace.symm ▸ heS.2⟩
  have heB : e.1 ∈ (boundaryComplex 3 S).faces := by
    have hcen : e.1.centroid ℝ id ∈ convexHull ℝ (e.1 : Set Ea) :=
      e.1.centroid_mem_convexHull (𝒦'.complex.nonempty_of_mem_faces e.2.1)
    have hxL : e.1.centroid ℝ id ∈ L₀.space := hcore.space_eq ▸
      L.convexHull_subset_space heL hcen
    obtain ⟨f, hf, hxf⟩ := L₀.mem_space_iff.mp hxL
    obtain ⟨hfK, hfcard⟩ := (mem_restrict_preimage_graphSkeletonSpace_iff 𝒦).mp hf
    have hxft : e.1.centroid ℝ id ∈ convexHull ℝ ((f ∩ t.1 : Finset Ea) : Set Ea) := by
      rw [Finset.coe_inter, ← 𝒦.complex.convexHull_inter_convexHull hfK t.2.1]
      exact ⟨hxf, heS.2 hcen⟩
    have hfne : (f ∩ t.1).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h] at hxft
      simp only [Finset.coe_empty, convexHull_empty, mem_empty_iff_false] at hxft
    have hfB : f ∩ t.1 ∈ B₀.faces := by
      refine ⟨Finset.inter_subset_right, hfne, ?_⟩
      intro heq
      have hle := Finset.card_le_card (Finset.inter_subset_left : f ∩ t.1 ⊆ f)
      rw [heq, t.2.2] at hle
      omega
    apply mem_faces_of_mem_openSimplex_of_mem_space (boundaryComplex_faces_subset 3 S) heS
      (centroid_mem_openSimplex (𝒦'.complex.nonempty_of_mem_faces e.2.1))
    rw [hSbd]
    exact B₀.convexHull_subset_space hfB hxft
  have hmax : ∀ f ∈ G.faces, f.card ≤ e.1.card := by
    intro f hf
    rw [e.2.2.1]
    exact hcore.card_le
      (fun q hq => ((mem_restrict_preimage_graphSkeletonSpace_iff 𝒦).mp hq).2) hf.1
  have hball := hS.isCombinatorialManifoldWithBoundary.isPLBall_splittingDisk_inter_residual
    S G hGS heG heB (k := 1) e.2.2.1 hmax
  have hres : closure (convexHull ℝ (t.1 : Set Ea) \
      (derivedNeighborhood 𝒦'.complex L).space) =
      closure (S.space \ (derivedNeighborhood S G).space) := by
    congr 1
    rw [show G = restrict L S.space from rfl,
      derivedNeighborhood_restrict_core_eq 𝒦'.complex S L
        (restrict_faces_subset _ _) (restrict_faces_subset _ _),
      ← derivedNeighborhood_space_inter_subcomplex 𝒦'.complex S L (restrict_faces_subset _ _),
      hSspace]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  let C := closure (convexHull ℝ (t.1 : Set Ea) \
    (derivedNeighborhood 𝒦'.complex L).space)
  have hCS : C ⊆ S.space := hSspace.symm ▸
    closure_minimal sdiff_subset (t.1.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hCK : C ⊆ 𝒦'.complex.space :=
    hCS.trans (space_mono_of_faces_subset (restrict_faces_subset _ _))
  have hraw : IsPLBall 1 ((splittingDisk 𝒦'.complex e.1 e.2.1).space ∩ C) := by
    rw [← inter_eq_right.mpr hCS, ← inter_assoc,
      splittingDisk_space_inter_subcomplex 𝒦'.complex S (restrict_faces_subset _ _) heS]
    simpa only [C, hres] using hball
  let J := boundaryComplex 2 (splittingDisk 𝒦'.complex e.1 e.2.1)
  let A := restrict J (convexHull ℝ (t.1 : Set Ea))
  have hDfin := 𝒦'.splittingDisk_faces_finite ⟨e.1, e.2.1, e.2.2.1⟩
  let _ : Finite (splittingDisk 𝒦'.complex e.1 e.2.1).faces := hDfin.to_subtype
  let _ : Finite J.faces := (boundaryComplex_faces_finite 2 _).to_subtype
  have hAfin : A.faces.Finite := (Set.toFinite J.faces).subset (restrict_faces_subset _ _)
  let _ : Finite A.faces := hAfin.to_subtype
  have hJ : IsPLSphere 1 J.space := isPLSphere_boundaryComplex_space_of_isPLBall _
    (𝒦'.isPLBall_splittingDisk hK' e.2.1 (k := 1) e.2.2.1 (by omega))
  have hJR : J.faces ⊆ (secondDerived 𝒦'.complex).faces := fun q hq =>
    splittingDisk_faces_subset _ e.2.1 (boundaryComplex_faces_subset 2 _ hq)
  have hJspace : J.space ⊆ 𝒦'.complex.space :=
    (space_mono_of_faces_subset hJR).trans (secondDerived_isSubdivision _).space_eq.subset
  have hAs : A.space = J.space ∩ convexHull ℝ (t.1 : Set Ea) := by
    change (restrict J (convexHull ℝ (t.1 : Set Ea))).space = _
    rw [← hSspace, ← (secondDerived_isSubdivision S).space_eq]
    exact restrict_space_eq_inter_of_faces_subset (secondDerived 𝒦'.complex) J
      (secondDerived S) hJR (secondDerived_faces_subset (restrict_faces_subset _ _))
  have hAraw : A.space = (splittingDisk 𝒦'.complex e.1 e.2.1).space ∩ C := by
    rw [hAs, show J = boundaryComplex 2 (splittingDisk 𝒦'.complex e.1 e.2.1) from rfl,
      𝒦'.boundaryComplex_splittingDisk_eq_geometricLink hK' ⟨e.1, e.2.1, e.2.2.1⟩]
    have hm : ∀ f ∈ L.faces, f.card ≤ e.1.card := by
      intro f hf
      rw [e.2.2.1]
      exact hcore.card_le
        (fun q hq => ((mem_restrict_preimage_graphSkeletonSpace_iff 𝒦).mp hq).2) hf
    simpa only [C, hSspace] using
      (splittingDisk_inter_subcomplex_residual_eq_geometricLink 𝒦'.complex S L
        (restrict_faces_subset _ _) (restrict_faces_subset _ _) heL hm).symm
  have hA : IsPLBall 1 A.space := hAraw.symm ▸ hraw
  have hlocal : A.space = (splittingDisk S e.1 heS).space ∩
      closure (S.space \ (derivedNeighborhood S G).space) := by
    rw [hAraw, ← inter_eq_right.mpr hCS, ← inter_assoc,
      splittingDisk_space_inter_subcomplex 𝒦'.complex S (restrict_faces_subset _ _) heS,
      show C = closure (S.space \ (derivedNeighborhood S G).space) from hres]
  have hzero : IsPLSphere 0 (A.space ∩ B₀.space) := by
    rw [hlocal, ← hSbd]
    exact isPLSphere_splittingDisk_inter_residual_inter_boundary S G
      hS.isCombinatorialManifoldWithBoundary hGS heG heB e.2.2.1 hmax
  have hmaxT : ∀ q ∈ 𝒦.complex.faces, t.1 ⊆ q → q = t.1 := by
    intro q hq htq
    obtain ⟨r, _, hqr, hrcard⟩ := 𝒦.exists_face_superset_card_eq hK hq
    apply (Finset.eq_of_subset_of_card_le htq _).symm
    have hle := Finset.card_le_card hqr
    rw [t.2.2]
    omega
  have hbdsub : (boundaryComplex 1 A).space ⊆ A.space ∩ B₀.space :=
    subset_inter (boundaryComplex_space_subset 1 A)
      (boundary_restrict_circle_subset_simplexBoundary 𝒦.complex (secondDerived 𝒦'.complex)
        J ((secondDerived_isSubdivision _).trans hsub) hJR hJ t.2.1
        hmaxT hA)
  have hbd : (boundaryComplex 1 A).space = A.space ∩ B₀.space := by
    obtain ⟨a, b, hab, hpair⟩ := isPLSphere_zero_iff.mp
      (isPLSphere_boundaryComplex_space_of_isPLBall A hA)
    obtain ⟨c, d, hcd, hpair'⟩ := isPLSphere_zero_iff.mp hzero
    rw [hpair, hpair'] at hbdsub ⊢
    apply Set.eq_of_subset_of_ncard_le hbdsub
    rw [ncard_pair hab, ncard_pair hcd]
  have hAK : A.space ⊆ 𝒦'.complex.space := hAs.subset.trans (inter_subset_left.trans hJspace)
  have hB₀K : B₀.space ⊆ 𝒦'.complex.space :=
    (show B₀.space ⊆ convexHull ℝ (t.1 : Set Ea) from fun x hx => by
      obtain ⟨q, hq, hxq⟩ := B₀.mem_space_iff.mp hx
      exact convexHull_mono (Finset.coe_subset.mpr hq.1) hxq).trans
      ((𝒦.complex.convexHull_subset_space t.2.1).trans hsub.space_eq.symm.subset)
  have himage : 𝒦'.map '' A.space = section34GraphSplitCell 𝒦 𝒦' e ∩
      section34GraphResidualCell 𝒦 𝒦' t.1 := by
    rw [hAraw, 𝒦'.bijOn.injOn.image_inter (splittingDisk_space_subset _ e.2.1) hCK,
      image_closure_sdiff_derivedNeighborhood_eq_section34GraphResidualCell hsub hmap t.2.1]
    rfl
  have hrim : 𝒦'.map '' B₀.space = simplexRim 𝒦 t.1 := by
    rw [hmap]
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨q, hq, hxq⟩ := B₀.mem_space_iff.mp hx
      exact mem_iUnion₂.mpr ⟨q, Finset.ssubset_iff_subset_ne.mpr ⟨hq.1, hq.2.2⟩,
        x, hxq, rfl⟩
    · intro x hx
      obtain ⟨q, hq, y, hy, rfl⟩ := mem_iUnion₂.mp hx
      have hqne : q.Nonempty := by
        by_contra hn
        rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hy
        simp only [Finset.coe_empty, convexHull_empty, mem_empty_iff_false] at hy
      exact ⟨y, B₀.convexHull_subset_space ⟨hq.subset, hqne, hq.ne⟩ hy, rfl⟩
  have hcell := 𝒦'.isPLCellOn_image_boundaryComplex A hAfin hAK (by omega) hA
  rwa [hbd, 𝒦'.bijOn.injOn.image_inter hAK hB₀K, himage, hrim] at hcell

open Classical in
theorem isPLCellOn_section34GraphEdgeArc_proper_faces
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK : IsCombinatorialManifoldWithBoundary 3 𝒦.complex)
    (hK' : IsCombinatorialManifold 3 𝒦'.complex) (a : Section34EdgeArcIndex 𝒦 𝒦') :
    IsPLCellOn 1 (section34GraphCutFamily 𝒦 𝒦' (.edgeArc a))
      (⋃ m ∈ section34Face (section34GraphCutFamily 𝒦 𝒦') (.edgeArc a) \ {.edgeArc a},
        section34GraphCutFamily 𝒦 𝒦' m) := by
  classical
  have hA := isPLCellOn_section34GraphEdgeArc_with_rim_boundary hsub hmap hK hK'
    a.1.1 a.1.2 a.2
  have hcell : IsPLCellOn 1 (section34GraphCutFamily 𝒦 𝒦' (.edgeArc a))
      ((section34GraphSplitCell 𝒦 𝒦' a.1.2 ∩
        section34GraphResidualCell 𝒦 𝒦' a.1.1.1) ∩ simplexRim 𝒦 a.1.1.1) := by
    simpa only [section34GraphCutFamily, inter_comm] using hA
  suffices ((section34GraphSplitCell 𝒦 𝒦' a.1.2 ∩
      section34GraphResidualCell 𝒦 𝒦' a.1.1.1) ∩ simplexRim 𝒦 a.1.1.1) =
      ⋃ m ∈ section34Face (section34GraphCutFamily 𝒦 𝒦') (.edgeArc a) \ {.edgeArc a},
        section34GraphCutFamily 𝒦 𝒦' m by rw [← this]; exact hcell
  apply Subset.antisymm
  · rintro x ⟨⟨hxE, hxR⟩, hxrim⟩
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hxrim
    change q ⊂ a.1.1.1 at hq
    have hqne : q.Nonempty := by
      by_contra h
      simp [Finset.not_nonempty_iff_eq_empty.mp h, simplexBody] at hxq
    have hqK := 𝒦.complex.down_closed a.1.1.2.1 hq.subset hqne
    have hxRq : x ∈ section34GraphResidualCell 𝒦 𝒦' q :=
      (section34GraphResidualCell_inter_simplexBody hsub hmap hqK a.1.1.2.1
        hq.subset).subset ⟨hxR, hxq⟩
    have hqcard : q.card = 3 := by
      have hlt := Finset.card_lt_card hq
      rw [a.1.1.2.2] at hlt
      by_contra h3
      have hsmall : q.card ≤ 2 := by omega
      have hem := section34GraphResidualCell_eq_empty_of_card_le_two hsub hmap hqK hsmall
      exact Set.notMem_empty x (hem ▸ hxRq)
    let s : Section34SimplexIndex 𝒦 3 := ⟨q, hqK, hqcard⟩
    have hes := (section34GraphSplitCell_inter_simplexBody_nonempty_iff
      hsub hmap a.1.2 hqK).mp ⟨x, hxE, hxq⟩
    let p : Section34MarkIndex 𝒦 𝒦' := ⟨(s, a.1.2), hes⟩
    have hsubR : section34GraphResidualCell 𝒦 𝒦' q ⊆
        section34GraphResidualCell 𝒦 𝒦' a.1.1.1 :=
      section34GraphResidualCell_mono_of_incident
        fun y hy => subset_convexHull ℝ _ (hq.subset hy)
    exact mem_iUnion₂.mpr ⟨.markedPoint p,
      ⟨fun y hy => ⟨hsubR hy.2, hy.1⟩, by simp⟩, hxE, hxRq⟩
  · refine iUnion₂_subset fun l hl => ?_
    have hLA : section34GraphCutFamily 𝒦 𝒦' l ⊆
        section34GraphCutFamily 𝒦 𝒦' (.edgeArc a) := hl.1
    have hne : l ≠ .edgeArc a := hl.2
    cases l with
    | vertexBall w =>
        have hd := (isPLCellOn_section34GraphVertexCell hsub hmap
          hK'.isCombinatorialManifoldWithBoundary w).dim_le_of_subset hcell hLA
        omega
    | tetraBall t =>
        cases section34GraphCutFamily_subset_strict_on_tetrahedra hsub hmap t (.edgeArc a) hLA
    | splitDisk e =>
        have hd := (isPLCellOn_section34GraphSplitCell hK' e).dim_le_of_subset hcell hLA
        omega
    | faceDisk s =>
        obtain ⟨B, hB⟩ := exists_isPLCellOn_section34GraphResidualTriangle hsub hmap s
        have hd := hB.dim_le_of_subset hcell hLA
        omega
    | patch p =>
        rcases section34GraphCutFamily_subset_strict_on_patches hsub hmap p (.edgeArc a) hLA
          with heq | hdim
        · cases heq
        · simp only [section34Dim] at hdim
          omega
    | faceArc b =>
        rcases (section34GraphCutFamily_subset_strict_on_arcs hsub hmap).1 b (.edgeArc a) hLA
          with heq | hdim
        · cases heq
        · simp only [section34Dim] at hdim
          omega
    | edgeArc i =>
        rcases (section34GraphCutFamily_subset_strict_on_arcs hsub hmap).2 i (.edgeArc a) hLA
          with heq | hdim
        · exact (hne heq).elim
        · simp only [section34Dim] at hdim
          omega
    | markedPoint p =>
        intro x hx
        have hxA := hLA hx
        have hxI := (section34GraphResidualCell_inter hsub hmap
          p.1.1.2.1 a.1.1.2.1).subset ⟨hx.2, hxA.1⟩
        have hst : p.1.1.1 ⊆ a.1.1.1 := by
          by_contra hn
          have hne : p.1.1.1 ∩ a.1.1.1 ≠ p.1.1.1 :=
            fun heq => hn (heq ▸ Finset.inter_subset_right)
          have hc : (p.1.1.1 ∩ a.1.1.1).card ≤ 2 := by
            have hlt := Finset.card_lt_card
              (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, hne⟩)
            rw [p.1.1.2.2] at hlt
            omega
          rcases (p.1.1.1 ∩ a.1.1.1).eq_empty_or_nonempty with hem | hnon
          · simp [hem, section34GraphResidualCell, simplexBody] at hxI
          · rw [section34GraphResidualCell_eq_empty_of_card_le_two hsub hmap
              (𝒦.complex.down_closed p.1.1.2.1 Finset.inter_subset_left hnon) hc] at hxI
            exact hxI
        have hproper : p.1.1.1 ⊂ a.1.1.1 :=
          Finset.ssubset_iff_subset_ne.mpr ⟨hst, fun heq => by
            have := congrArg Finset.card heq
            rw [p.1.1.2.2, a.1.1.2.2] at this
            omega⟩
        exact ⟨⟨hxA.2, hxA.1⟩, mem_iUnion₂.mpr ⟨p.1.1.1, hproper,
          section34GraphResidualCell_subset_simplexBody p.1.1.2.1 hx.2⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphMarkedPoints
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDerivedNeighborhood

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
open Classical in
theorem splittingDisk_inter_residual_eq_geometricLink
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hL : L.faces ⊆ K.faces)
    {e : Finset E} (he : e ∈ L.faces) (hmax : ∀ s ∈ L.faces, s.card ≤ e.card) :
    (splittingDisk K e (hL he)).space ∩ closure (K.space \ (derivedNeighborhood K L).space) =
      (SimplicialComplex.geometricLink (barycentricSubdivision (dualCell K e (hL he)))
        {e.centroid ℝ id}).space := by
  classical
  let X := barycentricSubdivision (dualCell K e (hL he))
  let c := e.centroid ℝ id
  have hlink : ∀ q, q ∈ (SimplicialComplex.geometricLink X {c}).faces ↔
      q ∈ (splittingDisk K e (hL he)).faces ∧ c ∉ q := by
    intro q
    rw [SimplicialComplex.mem_geometricLink_singleton]
    constructor
    · rintro ⟨hqne, hcq, hq⟩
      exact ⟨⟨X.down_closed hq (Finset.subset_insert c q) hqne, hq⟩, hcq⟩
    · rintro ⟨hq, hcq⟩
      exact ⟨X.nonempty_of_mem_faces hq.1, hcq, hq.2⟩
  rw [closure_space_sdiff_derivedNeighborhood_space (A := K) (subset_refl K.faces) hL]
  apply Subset.antisymm
  · rintro x ⟨hxD, hxR⟩
    obtain ⟨u, ⟨hu, huL⟩, hxu⟩ := mem_iUnion₂.mp hxR
    obtain ⟨q, hq, hxq⟩ := exists_face_mem_openSimplex (splittingDisk K e (hL he)) hxD
    have hqK := splittingDisk_faces_subset K (hL he) hq
    have hqu := mem_faces_of_mem_openSimplex_of_mem_space
      (derivedNeighborhoodCell_faces_subset K u) hqK hxq hxu
    apply (SimplicialComplex.geometricLink X {c}).convexHull_subset_space
      ((hlink q).mpr ⟨hq, ?_⟩) (openSimplex_subset_convexHull q hxq)
    intro hcq
    obtain ⟨D, hD, hDne, rfl⟩ := hqK
    have huc := (mem_derivedNeighborhoodCell_faces_iff_of_flag hu hD hDne).mp hqu
    obtain ⟨d, hd, hdc⟩ := Finset.mem_image.mp hcq
    have hde : d = {c} := injOn_faces_of_mem_openSimplex _
      (centroid_mem_openSimplex_of_mem_faces _) (hD.mem_faces hd)
      (singleton_centroid_mem_barycentricSubdivision K (hL he))
      (by simpa only [Finset.centroid_singleton, id_eq, c] using hdc)
    have huc' : u.centroid ℝ id = e.centroid ℝ id := by
      simpa only [hde, Finset.mem_singleton, c] using huc d hd
    exact huL ((injOn_faces_of_mem_openSimplex K
      (centroid_mem_openSimplex_of_mem_faces K) hu (hL he) huc').symm ▸ he)
  · intro x hx
    obtain ⟨q, hq, hxq⟩ := (SimplicialComplex.geometricLink X {c}).mem_space_iff.mp hx
    obtain ⟨hqD, hcq⟩ := (hlink q).mp hq
    refine ⟨(splittingDisk K e (hL he)).convexHull_subset_space hqD hxq, ?_⟩
    obtain ⟨D, hD, hDne, rfl⟩ := splittingDisk_faces_subset K (hL he) hqD
    obtain ⟨hdual, hcenter⟩ := (mem_splittingDisk_faces_iff_of_flag (hL he) hD hDne).mp hqD
    obtain ⟨d, hd, hbot⟩ := hD.exists_bot hDne
    have hcd : c ∈ d := hcenter d hd
    have hdne : d ≠ {c} := by
      intro hde
      apply hcq
      exact Finset.mem_image.mpr ⟨d, hd, by simp only [hde, Finset.centroid_singleton, id_eq]⟩
    obtain ⟨y, hyd, hyc⟩ : ∃ y ∈ d, y ≠ c := by
      by_contra h
      push Not at h
      exact hdne (Finset.eq_singleton_iff_unique_mem.mpr ⟨hcd, h⟩)
    obtain ⟨F, hF, hFne, heF, hdF⟩ := (mem_dualCell_faces_iff K (hL he)).mp (hdual d hd)
    obtain ⟨u, huF, huy⟩ := Finset.mem_image.mp (hdF ▸ hyd)
    have hu : u ∈ K.faces := hF.mem_faces huF
    have heu : e ⊆ u := heF u huF
    have hue : u ≠ e := by
      intro hue
      exact hyc (huy.symm.trans (congrArg (fun z : Finset E => z.centroid ℝ id) hue))
    have huL : u ∉ L.faces := by
      intro huL
      exact hue (Finset.eq_of_subset_of_card_le heu (hmax u huL)).symm
    have huc : ∀ f ∈ D, u.centroid ℝ id ∈ f := by
      intro f hf
      exact hbot f hf (huy.symm ▸ hyd)
    refine mem_iUnion₂.mpr ⟨u, ⟨hu, huL⟩, ?_⟩
    exact (derivedNeighborhoodCell K u).convexHull_subset_space
      ((mem_derivedNeighborhoodCell_faces_iff_of_flag hu hD hDne).mpr huc) hxq

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_splittingDisk_inter_residual
    {n k : ℕ} (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (hL : L.faces ⊆ K.faces)
    {e : Finset E} (he : e ∈ L.faces) (heB : e ∈ (boundaryComplex (n + 1) K).faces)
    (hcard : e.card = k + 1) (hmax : ∀ s ∈ L.faces, s.card ≤ e.card) :
    IsPLBall (n - k) ((splittingDisk K e (hL he)).space ∩
      closure (K.space \ (PiecewiseLinear.derivedNeighborhood K L).space)) := by
  classical
  let _ : Finite (dualCell K e (hL he)).faces := (dualCell_faces_finite K (hL he)).to_subtype
  rw [splittingDisk_inter_residual_eq_geometricLink K L hL he hmax,
    isPLBall_geometricLink_iff_of_isSubdivision
      (barycentricSubdivision_isSubdivision (dualCell K e (hL he)))
      (singleton_centroid_mem_dualCell K (hL he)), geometricLink_dualCell]
  exact hK.isPLBall_upperLink_of_mem_boundaryComplex K heB hcard

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [T2Space M] {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

open Classical in
theorem exists_isPLCellOn_section34GraphSplitCell_inter_residualTetrahedron
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (t : Section34SimplexIndex 𝒦 4) (e : Section34EdgeIndex 𝒦 𝒦')
    (het : Section34Incident e.1 t.1) :
    ∃ B, IsPLCellOn 1 (section34GraphSplitCell 𝒦 𝒦' e ∩
      section34GraphResidualCell 𝒦 𝒦' t.1) B := by
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
  obtain ⟨Bd, hBd⟩ := 𝒦'.exists_isPLCellOn_image
    (inter_subset_left.trans (splittingDisk_space_subset _ e.2.1)) (by omega) hraw
  rw [𝒦'.bijOn.injOn.image_inter (splittingDisk_space_subset _ e.2.1) hCK,
    image_closure_sdiff_derivedNeighborhood_eq_section34GraphResidualCell hsub hmap t.2.1] at hBd
  exact ⟨Bd, hBd⟩

end DifferentialGeometry.Topology.PiecewiseLinear

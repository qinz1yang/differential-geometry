/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphResidualCover
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCutIncidence
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellRestriction

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem exists_singleton_splittingDisk_inter_boundary_residual
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {e : Finset E}
    (heB : e ∈ (boundaryComplex 2 K).faces) (hecard : e.card = 2) :
    ∃ p : E, (splittingDisk K e (boundaryComplex_faces_subset 2 K heB)).space ∩
      closure (K.space \ (derivedNeighborhood K (boundaryComplex 2 K)).space) = {p} := by
  classical
  let B := boundaryComplex 2 K
  have he : e ∈ K.faces := boundaryComplex_faces_subset 2 K heB
  obtain ⟨a, ha⟩ := (hK.mem_boundaryComplex_iff_unique_coface K hecard).mp heB
  have ha' : a ∉ e ∧ insert a e ∈ K.faces := by
    change a ∈ {w | w ∉ e ∧ insert w e ∈ K.faces}
    rw [ha]
    exact mem_singleton a
  let t := insert a e
  have ht : t ∈ K.faces := ha'.2
  have het : e ⊆ t := Finset.subset_insert a e
  have htcard : t.card = 3 := by simp only [t, Finset.card_insert_of_notMem ha'.1, hecard]
  have htB : t ∉ B.faces := by
    intro htB
    have hle := ((hK.mem_boundaryComplex_faces_iff K).mp htB).2.1
    omega
  have hcoface : ∀ u ∈ K.faces, e ⊆ u → u = e ∨ u = t := by
    intro u hu heu
    by_cases hue : u = e
    · exact Or.inl hue
    right
    obtain ⟨b, hbu, hbe⟩ := Finset.exists_of_ssubset
      (Finset.ssubset_iff_subset_ne.mpr ⟨heu, Ne.symm hue⟩)
    have hubound := hK.card_le K hu
    have hucard : u.card = 3 := by
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨heu, Ne.symm hue⟩)
      omega
    have hinsert : insert b e = u := Finset.eq_of_subset_of_card_le
      (Finset.insert_subset_iff.mpr ⟨hbu, heu⟩) (by simp [hbe, hecard, hucard])
    have hb : b ∈ {w | w ∉ e ∧ insert w e ∈ K.faces} := ⟨hbe, hinsert.symm ▸ hu⟩
    rw [ha, mem_singleton_iff] at hb
    exact hinsert.symm.trans (congrArg (fun z => insert z e) hb)
  let f : Finset E := {e.centroid ℝ id, t.centroid ℝ id}
  have hf : f ∈ (barycentricSubdivision K).faces :=
    pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K he ht (Or.inl het)
  have hfdual : f ∈ (dualCell K e he).faces := by
    apply (mem_dualCell_faces_iff K he).mpr
    refine ⟨{e, t}, ⟨?_, ?_⟩, by simp, ?_, by simp [f]⟩
    · intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> assumption
    · intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact Or.inl subset_rfl
      · exact Or.inl het
      · exact Or.inr het
      · exact Or.inl subset_rfl
    · intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact subset_rfl
      · exact het
  refine ⟨f.centroid ℝ id, ?_⟩
  rw [closure_space_sdiff_derivedNeighborhood_space (A := K) (subset_refl K.faces)
    (boundaryComplex_faces_subset 2 K)]
  apply Subset.antisymm
  · rintro x ⟨hxD, hxR⟩
    obtain ⟨u, ⟨hu, huB⟩, hxu⟩ := mem_iUnion₂.mp hxR
    obtain ⟨q, hq, hxq⟩ := exists_face_mem_openSimplex (splittingDisk K e he) hxD
    have hqK := splittingDisk_faces_subset K he hq
    have hqu := mem_faces_of_mem_openSimplex_of_mem_space
      (derivedNeighborhoodCell_faces_subset K u) hqK hxq hxu
    obtain ⟨D, hD, hDne, rfl⟩ := hqK
    obtain ⟨hdual, hecenter⟩ := (mem_splittingDisk_faces_iff_of_flag he hD hDne).mp hq
    have hucenter := (mem_derivedNeighborhoodCell_faces_iff_of_flag hu hD hDne).mp hqu
    have hDsingle : ∀ d ∈ D, d = f := by
      intro d hd
      obtain ⟨c, hc, hcne, hcd, rfl⟩ := (mem_dualCell_faces_iff K he).mp (hdual d hd)
      have hcu : u ∈ c := by
        obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp (hucenter _ hd)
        have hvu' := injOn_faces_of_mem_openSimplex K
          (centroid_mem_openSimplex_of_mem_faces K) (hc.mem_faces hv) hu hvu
        exact hvu' ▸ hv
      have hut : u = t := (hcoface u hu (hcd u hcu)).resolve_left (fun hue =>
        huB (hue.symm ▸ heB))
      apply Finset.Subset.antisymm
      · intro y hy
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
        rcases hcoface v (hc.mem_faces hv) (hcd v hv) with rfl | rfl <;> simp [f]
      · intro y hy
        simp only [f, Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact hecenter _ hd
        · exact hut ▸ hucenter _ hd
    have hqsub : ((D.image fun d => d.centroid ℝ id) : Set E) ⊆ {f.centroid ℝ id} := by
      intro y hy
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
      simp only [hDsingle d hd, mem_singleton_iff]
    exact convexHull_min hqsub (convex_singleton _) (openSimplex_subset_convexHull _ hxq)
  · rintro x rfl
    have hDflag : IsFlag (barycentricSubdivision K) {f} :=
      ⟨fun d hd => (Finset.mem_singleton.mp hd).symm ▸ hf,
        fun d hd g hg => Or.inl ((Finset.mem_singleton.mp hd).trans
          (Finset.mem_singleton.mp hg).symm ▸ subset_rfl)⟩
    have hDne : ({f} : Finset (Finset E)).Nonempty := Finset.singleton_nonempty f
    have hpD : {f.centroid ℝ id} ∈ (splittingDisk K e he).faces := by
      rw [← Finset.image_singleton (fun d : Finset E => d.centroid ℝ id) f]
      apply (mem_splittingDisk_faces_iff_of_flag he hDflag hDne).mpr
      exact ⟨fun d hd => (Finset.mem_singleton.mp hd).symm ▸ hfdual,
        fun d hd => (Finset.mem_singleton.mp hd).symm ▸ (by simp [f])⟩
    have hpC : {f.centroid ℝ id} ∈ (derivedNeighborhoodCell K t).faces := by
      rw [← Finset.image_singleton (fun d : Finset E => d.centroid ℝ id) f]
      apply (mem_derivedNeighborhoodCell_faces_iff_of_flag ht hDflag hDne).mpr
      exact fun d hd => (Finset.mem_singleton.mp hd).symm ▸ (by simp [f])
    refine ⟨(splittingDisk K e he).convexHull_subset_space hpD ?_,
      mem_iUnion₂.mpr ⟨t, ⟨ht, htB⟩, (derivedNeighborhoodCell K t).convexHull_subset_space hpC ?_⟩⟩
    all_goals exact subset_convexHull ℝ _ (by simp)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [T2Space M] {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

open Classical in
theorem exists_singleton_section34GraphSplitCell_inter_residualTriangle
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (s : Section34SimplexIndex 𝒦 3) (e : Section34EdgeIndex 𝒦 𝒦')
    (hes : Section34Incident e.1 s.1) :
    ∃ p : M, section34GraphSplitCell 𝒦 𝒦' e ∩
      section34GraphResidualCell 𝒦 𝒦' s.1 = {p} := by
  classical
  let S₀ := simplexComplex s.1 (𝒦.complex.indep s.2.1)
  let B₀ := simplexBoundary s.1 (𝒦.complex.indep s.2.1)
  let S := restrict 𝒦'.complex (convexHull ℝ (s.1 : Set Ea))
  let L := restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)
  let L₀ := restrict 𝒦.complex (𝒦.map ⁻¹' graphSkeletonSpace 𝒦)
  have hS₀space : S₀.space = convexHull ℝ (s.1 : Set Ea) :=
    simplexComplex_space _ _ (𝒦.complex.nonempty_of_mem_faces s.2.1)
  have hS₀K : S₀.faces ⊆ 𝒦.complex.faces :=
    fun _ ht => 𝒦.complex.down_closed s.2.1 ht.2 ht.1
  have hSsub : IsSubdivision S S₀ := by
    simpa only [hS₀space] using hsub.restrict S₀ hS₀K
  have hSspace : S.space = convexHull ℝ (s.1 : Set Ea) := hSsub.space_eq.trans hS₀space
  have hS₀ : IsPLBall 2 S₀.space := hS₀space.symm ▸
    isPLBall_convexHull_of_affineIndependent s.1 (𝒦.complex.indep s.2.1) s.2.2
  have hS : IsPLBall 2 S.space := hSsub.space_eq.symm ▸ hS₀
  let _ : Finite S₀.faces := (simplexComplex_faces_finite _ _).to_subtype
  let _ : Finite S.faces := (𝒦'.restrict_faces_finite_of_isCompact
    (s.1.finite_toSet.isCompact_convexHull ℝ)
      ((𝒦.complex.convexHull_subset_space s.2.1).trans hsub.space_eq.symm.subset)).to_subtype
  have hSbd : (boundaryComplex 2 S).space = B₀.space := by
    rw [boundaryComplex_space_of_isSubdivision S₀ S hS₀.isCombinatorialManifoldWithBoundary
      hSsub, show boundaryComplex 2 S₀ = B₀ from
        boundaryComplex_simplexComplex (𝒦.complex.indep s.2.1) s.2.2]
  have hLspace : L.space = L₀.space :=
    (isSubdivision_restrict_preimage_graphSkeletonSpace hsub hmap).space_eq
  have hcore : L.space ∩ S.space = (boundaryComplex 2 S).space := by
    rw [hSbd, hLspace, hSspace, ← hS₀space,
      ← restrict_space_eq_inter_of_faces_subset 𝒦.complex L₀ S₀
        (restrict_faces_subset _ _) hS₀K, hS₀space,
      restrict_graph_core_triangle_eq_simplexBoundary 𝒦 s]
  have hLS : restrict L S.space = boundaryComplex 2 S :=
    eq_of_faces_subset_of_space_eq _ _ S
      (fun _ hu => ((mem_restrict_faces_iff_of_faces_subset 𝒦'.complex L S
        (restrict_faces_subset _ _) (restrict_faces_subset _ _)).mp hu).2)
      (boundaryComplex_faces_subset 2 S)
      ((restrict_space_eq_inter_of_faces_subset 𝒦'.complex L S
        (restrict_faces_subset _ _) (restrict_faces_subset _ _)).trans hcore)
  have heS : e.1 ∈ S.faces := ⟨e.2.1,
    convexHull_min hes (convex_convexHull ℝ (s.1 : Set Ea))⟩
  have heL : e.1 ∈ L.faces := ⟨e.2.1, fun x hx => e.2.2.2 (mem_image_of_mem _ hx)⟩
  have heB : e.1 ∈ (boundaryComplex 2 S).faces := by
    rw [← hLS]
    exact ⟨heL, hSspace.symm ▸ heS.2⟩
  obtain ⟨p, hp⟩ := exists_singleton_splittingDisk_inter_boundary_residual S
    hS.isCombinatorialManifoldWithBoundary heB e.2.2.1
  have hres : closure (convexHull ℝ (s.1 : Set Ea) \
      (derivedNeighborhood 𝒦'.complex L).space) =
      closure (S.space \
        (derivedNeighborhood S (boundaryComplex 2 S)).space) := by
    congr 1
    rw [← hLS, derivedNeighborhood_restrict_core_eq 𝒦'.complex S L
      (restrict_faces_subset _ _) (restrict_faces_subset _ _),
      ← derivedNeighborhood_space_inter_subcomplex 𝒦'.complex S L (restrict_faces_subset _ _),
      hSspace]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  let C := closure (convexHull ℝ (s.1 : Set Ea) \
    (derivedNeighborhood 𝒦'.complex L).space)
  have hCS : C ⊆ S.space := hSspace.symm ▸
    closure_minimal sdiff_subset (s.1.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hCK : C ⊆ 𝒦'.complex.space :=
    hCS.trans (space_mono_of_faces_subset (restrict_faces_subset _ _))
  have hraw : (splittingDisk 𝒦'.complex e.1 e.2.1).space ∩ C = {p} := by
    rw [← inter_eq_right.mpr hCS, ← inter_assoc,
      splittingDisk_space_inter_subcomplex 𝒦'.complex S (restrict_faces_subset _ _) heS]
    simpa only [C, hres] using hp
  refine ⟨𝒦'.map p, ?_⟩
  rw [← image_closure_sdiff_derivedNeighborhood_eq_section34GraphResidualCell
    hsub hmap s.2.1]
  change 𝒦'.map '' (splittingDisk 𝒦'.complex e.1 e.2.1).space ∩ 𝒦'.map '' C = _
  rw [← 𝒦'.bijOn.injOn.image_inter (splittingDisk_space_subset _ e.2.1) hCK,
    hraw, image_singleton]

end DifferentialGeometry.Topology.PiecewiseLinear

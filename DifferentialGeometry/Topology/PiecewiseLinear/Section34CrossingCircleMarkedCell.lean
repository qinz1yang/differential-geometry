import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCircleMarkedCellHits
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeMarkedCell
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeChain

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem cone_union (p : E) (X Y : Set E) :
    coneSet p (X ∪ Y) = coneSet p X ∪ coneSet p Y := by
  ext x
  simp only [mem_coneSet_iff, mem_union, exists_or, or_and_right]
  aesop

open Classical in
theorem exists_marked_derived_crossing_cell
    (R Γ : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R) (hΓR : Γ.faces ⊆ R.faces)
    {s : Finset E} (hs : s ∈ Γ.faces) (hsB : s ∉ (boundaryComplex 3 R).faces)
    {t : Fin 2 → Finset E} (ht : ∀ j, t j ∈ Γ.faces)
    (hne : ∀ j, s ≠ t j) (hcomp : ∀ j, s ⊆ t j ∨ t j ⊆ s)
    {D : Fin 2 → Set E} (hD : ∀ j, D j =
      (derivedNeighborhoodCell R s).space ∩ (derivedNeighborhoodCell R (t j)).space)
    {qcap : Fin 2 → (Fin 3 → ℝ) → E}
    (hcap : ∀ j, IsPLHomeomorphOn (qcap j) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D j))
    (hDS : ∀ j, D j ⊆ (derivedNeighborhoodCellBase R s).space)
    (hdis : Disjoint (D 0) (D 1)) {y : Fin 2 → E}
    (hy : ∀ j, y j = ({s.centroid ℝ id, (t j).centroid ℝ id} : Finset E).centroid ℝ id)
    {P : Fin 4 → Set E} {q : Fin 4 → (Fin 3 → ℝ) → E}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (P i))
    (hPR : ∀ i, (PiecewiseLinear.restrict R (P i)).space = P i)
    {W : Set E} (hbd : ∀ x ∈ R.space ∩ W, ∀ i,
      x ∈ q i '' stdSimplexBoundary 2 ↔ x ∈ Γ.space)
    (hstar : (⋃ v ∈ s, closedStar R v) ⊆ W) {γ : Fin 4 → ℝ → E}
    (hγ : ∀ i, IsPLHomeomorphOn (γ i) (Icc 0 1)
      ((derivedNeighborhoodCellBase R s).space ∩ P i))
    (hzero : ∀ i, γ i 0 = y 0) (hone : ∀ i, γ i 1 = y 1)
    (hpoles : Γ.space ∩ (derivedNeighborhoodCellBase R s).space = {y 0, y 1})
    (hTT : ∀ i j, i ≠ j →
      ((derivedNeighborhoodCellBase R s).space ∩ P i) ∩
        ((derivedNeighborhoodCellBase R s).space ∩ P j) = {y 0, y 1})
    (hsep : ∀ i : Fin 4, ∀ U ⊆ (derivedNeighborhoodCellBase R s).space \
      (((derivedNeighborhoodCellBase R s).space ∩ P i) ∪
        ((derivedNeighborhoodCellBase R s).space ∩ P (i + 2))),
      IsPreconnected U →
      (U ∩ ((derivedNeighborhoodCellBase R s).space ∩ P (i + 1))).Nonempty →
      (U ∩ ((derivedNeighborhoodCellBase R s).space ∩ P (i + 3))).Nonempty → False)
    {A B Ω : Set E} {ψ : (ℝ × ℝ) × ℝ → E} {V : Set ((ℝ × ℝ) × ℝ)}
    (hψ : IsPLHomeomorphOn ψ V (R.space ∩ Ω)) (hWΩ : W ⊆ Ω)
    (haxis : ∀ p ∈ V, ψ p ∈ Γ.space ↔ p.1 = 0)
    (hsheets : ∀ p ∈ V, (ψ p ∈ A ↔ p.1.2 = 0) ∧ (ψ p ∈ B ↔ p.1.1 = 0))
    (hread : ∀ x ∈ R.space ∩ W, ∀ i,
      x ∈ P i ↔ Function.invFunOn ψ V x ∈ crossHalfPlane i)
    (hcell : (derivedNeighborhoodCell R s).space ⊆ W) :
    ∃ G : (ℝ × ℝ) × ℝ → E,
      IsPLHomeomorphOn G spliceCylinder (derivedNeighborhoodCell R s).space ∧
      G (0, 1 / 2) = s.centroid ℝ id ∧
      (∀ j : Fin 2, G (0, (j : ℝ)) = y j) ∧
      (∀ i, G '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1) =
        (derivedNeighborhoodCell R s).space ∩ P i) ∧
      G '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) =
        (derivedNeighborhoodCell R s).space ∩ Γ.space ∧
      (∀ j : Fin 2, G '' (spliceSquare ×ˢ ({(j : ℝ)} : Set ℝ)) = D j) ∧
      (∀ j : Fin 2, ∀ i, G '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ
        ({(j : ℝ)} : Set ℝ)) = D j ∩ P i) ∧
      (∀ j : Fin 2, ∀ i, D j ∩ P i =
        segment ℝ (y j) (G (fourSpokeModelLeaf i, (j : ℝ)))) ∧
      (∀ j : Fin 2, ∀ i, qcap j '' stdSimplexBoundary 2 ∩
        ((derivedNeighborhoodCellBase R s).space ∩ P i) =
          {G (fourSpokeModelLeaf i, (j : ℝ))}) ∧
      G '' ((segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 0) ×ˢ Icc (0 : ℝ) 1) ∪
        (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 2) ×ˢ Icc (0 : ℝ) 1)) =
          (derivedNeighborhoodCell R s).space ∩ A ∧
      G '' ((segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 1) ×ˢ Icc (0 : ℝ) 1) ∪
        (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 3) ×ˢ Icc (0 : ℝ) 1)) =
          (derivedNeighborhoodCell R s).space ∩ B := by
  obtain ⟨δ, hδ, hδ0, hδ1, hb0, hb1, ha0, ha1⟩ :=
    exists_marked_arcs_of_interior_derived_cell R Γ hR hΓR hs hsB ht hne hcomp hD hcap
      hDS hdis hy hq hPR hbd hstar hγ hzero hone
  let K := derivedNeighborhoodCellBase R s
  let _ : Finite K.faces := (upperLink_faces_finite _ _).to_subtype
  have hK : IsConeBase (s.centroid ℝ id) K := isConeBase_centroid_upperLink R (hΓR hs)
  have hS : IsPLSphere 2 K.space :=
    hR.isPLSphere_upperLink_centroid_of_not_mem_boundaryComplex (hΓR hs) hsB
  have hyD (j : Fin 2) : y j ∈ D j := by
    rw [hD j, hy j, derivedNeighborhoodCell_inter_eq_coneSet R
      (hΓR hs) (hΓR (ht j)) (hcomp j)]
    exact apex_mem_coneSet _ _
  obtain ⟨G, hG, hGc, hGδ, hGr, hGa, hG0, hG1, -⟩ :=
    exists_isPLHomeomorphOn_spliceCylinder_of_marked hK hS hδ hδ0 hδ1
      (fun _ => inter_subset_left) hTT hsep (hcap 0) (hcap 1) (hDS 0) (hDS 1)
      hdis hb0 hb1 (hyD 0) (hyD 1)
  have hG' : IsPLHomeomorphOn G spliceCylinder (derivedNeighborhoodCell R s).space := by
    rw [derivedNeighborhoodCell_space_eq_coneSet R (hΓR hs)]
    exact hG
  have hcone (L : Geometry.SimplicialComplex ℝ E) (hLR : L.faces ⊆ R.faces)
      (hsL : s ∈ L.faces) : (derivedNeighborhoodCell R s).space ∩ L.space =
      coneSet (s.centroid ℝ id) ((derivedNeighborhoodCellBase R s).space ∩ L.space) := by
    rw [derivedNeighborhoodCell_inter_subcomplex R L hLR hsL,
      derivedNeighborhoodCellBase_inter_subcomplex R L hLR hsL]
    exact derivedNeighborhoodCell_space_eq_coneSet L hsL
  have hpage (i : Fin 4) : (derivedNeighborhoodCell R s).space ∩ P i =
      coneSet (s.centroid ℝ id) ((derivedNeighborhoodCellBase R s).space ∩ P i) := by
    have hsP := comparable_circle_face_mem_page_boundary R Γ hΓR hs hq hPR hbd hstar hs
      (Or.inl Finset.Subset.rfl) i
    simpa only [hPR i] using hcone (PiecewiseLinear.restrict R (P i))
      (restrict_faces_subset R _) (boundaryComplex_faces_subset 2 _ hsP)
  have hGr' (i : Fin 4) :
      G '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1) =
        (derivedNeighborhoodCell R s).space ∩ P i := (hGr i).trans (hpage i).symm
  have hleaf0 (i : Fin 4) : G (fourSpokeModelLeaf i, 0) = δ i (1 / 4) := by
    simpa only [tubeMeridianParam_quarter] using hGδ i (1 / 4) (by norm_num)
  have hleaf1 (i : Fin 4) : G (fourSpokeModelLeaf i, 1) = δ i (3 / 4) := by
    simpa only [tubeMeridianParam_threeQuarter] using hGδ i (3 / 4) (by norm_num)
  have hfaces (j : Fin 2) : G '' (spliceSquare ×ˢ ({(j : ℝ)} : Set ℝ)) = D j := by
    fin_cases j
    · simpa using hG0
    · simpa using hG1
  have hjI (j : Fin 2) : (j : ℝ) ∈ Icc (0 : ℝ) 1 := by fin_cases j <;> norm_num
  have harms (j : Fin 2) (i : Fin 4) :
      G '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({(j : ℝ)} : Set ℝ)) =
        D j ∩ P i := by
    have hrib : segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1 ⊆
        spliceCylinder := prod_mono (segment_fourSpokeModelLeaf_subset_spliceSquare i) subset_rfl
    have hface : spliceSquare ×ˢ ({(j : ℝ)} : Set ℝ) ⊆ spliceCylinder :=
      prod_mono subset_rfl (singleton_subset_iff.mpr (hjI j))
    have heq : (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ Icc (0 : ℝ) 1) ∩
        (spliceSquare ×ˢ ({(j : ℝ)} : Set ℝ)) =
          segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({(j : ℝ)} : Set ℝ) := by
      ext p
      exact ⟨fun h => ⟨h.1.1, h.2.2⟩, fun h =>
        ⟨⟨h.1, h.2 ▸ hjI j⟩, segment_fourSpokeModelLeaf_subset_spliceSquare i h.1, h.2⟩⟩
    rw [← heq, hG'.bijOn.injOn.image_inter hrib hface, hGr', hfaces]
    ext p
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨(hD j ▸ h.1).1, h.2⟩, h.1⟩⟩
  have hwhole := derived_cell_inter_crossing_sheets_eq_cones R Γ hΓR hs hψ hWΩ haxis
    hsheets hPR hread hcell
  refine ⟨G, hG', hGc, ?_, hGr', ?_, hfaces, harms, ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · have hh := hGδ 0 0 (by norm_num)
      rw [tubeMeridianParam_zero, hδ0] at hh
      simpa using hh
    · have hh := hGδ 0 1 (by norm_num)
      rw [tubeMeridianParam_one, hδ1] at hh
      simpa using hh
  · rw [hGa, hcone Γ hΓR hs, inter_comm, hpoles]
  · intro j i
    fin_cases j
    · have hh := ha0 i
      rw [← hleaf0 i] at hh
      simpa using hh
    · have hh := ha1 i
      rw [← hleaf1 i] at hh
      simpa using hh
  · intro j i
    fin_cases j
    · have hh := hb0 i
      rw [← hleaf0 i] at hh
      simpa using hh
    · have hh := hb1 i
      rw [← hleaf1 i] at hh
      simpa using hh
  · rw [image_union, hGr 0, hGr 2, ← cone_union]
    exact hwhole.1.symm
  · rw [image_union, hGr 1, hGr 3, ← cone_union]
    exact hwhole.2.symm

end DifferentialGeometry.Topology.PiecewiseLinear

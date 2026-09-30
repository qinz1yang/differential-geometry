import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCircleLinks

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem even_half_planes (p : (ℝ × ℝ) × ℝ) :
    p ∈ crossHalfPlane 0 ∪ crossHalfPlane 2 ↔ p.1.2 = 0 := by
  constructor
  · rintro (⟨a, -, ha⟩ | ⟨a, -, ha⟩) <;>
      simp [ha, fourSpokeModelLeaf]
  · intro hp
    by_cases ha : 0 ≤ p.1.1
    · exact Or.inl ⟨p.1.1, ha, by ext <;> simp [fourSpokeModelLeaf, hp]⟩
    · exact Or.inr ⟨-p.1.1, neg_nonneg.mpr (not_le.mp ha).le,
        by ext <;> simp [fourSpokeModelLeaf, hp]⟩

private theorem odd_half_planes (p : (ℝ × ℝ) × ℝ) :
    p ∈ crossHalfPlane 1 ∪ crossHalfPlane 3 ↔ p.1.1 = 0 := by
  constructor
  · rintro (⟨a, -, ha⟩ | ⟨a, -, ha⟩) <;>
      simp [ha, fourSpokeModelLeaf]
  · intro hp
    by_cases ha : 0 ≤ p.1.2
    · exact Or.inl ⟨p.1.2, ha, by ext <;> simp [fourSpokeModelLeaf, hp]⟩
    · exact Or.inr ⟨-p.1.2, neg_nonneg.mpr (not_le.mp ha).le,
        by ext <;> simp [fourSpokeModelLeaf, hp]⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem cone_union (p : E) (X Y : Set E) :
    coneSet p (X ∪ Y) = coneSet p X ∪ coneSet p Y := by
  ext x
  simp only [mem_coneSet_iff, mem_union, exists_or, or_and_right]
  aesop

open Classical in
theorem derived_cell_inter_crossing_sheets_eq_cones
    (R Γ : Geometry.SimplicialComplex ℝ E) (hΓR : Γ.faces ⊆ R.faces)
    {s : Finset E} (hs : s ∈ Γ.faces) {A B Ω W : Set E}
    {ψ : (ℝ × ℝ) × ℝ → E} {V : Set ((ℝ × ℝ) × ℝ)}
    (hψ : IsPLHomeomorphOn ψ V (R.space ∩ Ω)) (hWΩ : W ⊆ Ω)
    (haxis : ∀ p ∈ V, ψ p ∈ Γ.space ↔ p.1 = 0)
    (hsheets : ∀ p ∈ V, (ψ p ∈ A ↔ p.1.2 = 0) ∧ (ψ p ∈ B ↔ p.1.1 = 0))
    {P : Fin 4 → Set E} (hPR : ∀ i, (PiecewiseLinear.restrict R (P i)).space = P i)
    (hread : ∀ x ∈ R.space ∩ W, ∀ i,
      x ∈ P i ↔ Function.invFunOn ψ V x ∈ crossHalfPlane i)
    (hcell : (derivedNeighborhoodCell R s).space ⊆ W) :
    (derivedNeighborhoodCell R s).space ∩ A =
      coneSet (s.centroid ℝ id)
        (((derivedNeighborhoodCellBase R s).space ∩ P 0) ∪
          ((derivedNeighborhoodCellBase R s).space ∩ P 2)) ∧
    (derivedNeighborhoodCell R s).space ∩ B =
      coneSet (s.centroid ℝ id)
        (((derivedNeighborhoodCellBase R s).space ∩ P 1) ∪
          ((derivedNeighborhoodCellBase R s).space ∩ P 3)) := by
  let χ := Function.invFunOn ψ V
  have hCW : (derivedNeighborhoodCell R s).space ⊆ R.space ∩ W :=
    fun _ hx => ⟨derivedNeighborhoodCell_space_subset R s hx, hcell hx⟩
  have hCΩ : (derivedNeighborhoodCell R s).space ⊆ R.space ∩ Ω :=
    fun _ hx => ⟨(hCW hx).1, hWΩ (hCW hx).2⟩
  have hχV : ∀ x ∈ (derivedNeighborhoodCell R s).space, χ x ∈ V :=
    fun _ hx => hψ.symm.bijOn.mapsTo (hCΩ hx)
  have hψχ : ∀ x ∈ (derivedNeighborhoodCell R s).space, ψ (χ x) = x :=
    fun _ hx => hψ.bijOn.invOn_invFunOn.2 (hCΩ hx)
  have hcC : s.centroid ℝ id ∈ (derivedNeighborhoodCell R s).space := by
    rw [derivedNeighborhoodCell_space_eq_coneSet R (hΓR hs)]
    exact apex_mem_coneSet _ _
  have hcΓ : s.centroid ℝ id ∈ Γ.space :=
    Γ.convexHull_subset_space hs (s.centroid_mem_convexHull (Γ.nonempty_of_mem_faces hs))
  have hcχ : (χ (s.centroid ℝ id)).1 = 0 :=
    (haxis _ (hχV _ hcC)).mp ((hψχ _ hcC).symm ▸ hcΓ)
  have hcone (i : Fin 4) : (derivedNeighborhoodCell R s).space ∩ P i =
      coneSet (s.centroid ℝ id) ((derivedNeighborhoodCellBase R s).space ∩ P i) := by
    let L := PiecewiseLinear.restrict R (P i)
    have hLR : L.faces ⊆ R.faces := restrict_faces_subset R (P i)
    have hsL : s ∈ L.faces := by
      apply mem_faces_of_mem_openSimplex_of_mem_space hLR (hΓR hs)
        (centroid_mem_openSimplex_of_mem_faces R s (hΓR hs))
      rw [show L.space = P i from hPR i]
      exact (hread _ (hCW hcC) i).mpr ⟨0, le_rfl, by rw [zero_smul]; exact hcχ⟩
    rw [← hPR i, derivedNeighborhoodCell_inter_subcomplex R L hLR hsL,
      derivedNeighborhoodCellBase_inter_subcomplex R L hLR hsL]
    exact derivedNeighborhoodCell_space_eq_coneSet L hsL
  have hlocal (x : E) (hx : x ∈ (derivedNeighborhoodCell R s).space) :
      (x ∈ A ↔ x ∈ P 0 ∪ P 2) ∧ (x ∈ B ↔ x ∈ P 1 ∪ P 3) := by
    have hh := hsheets (χ x) (hχV x hx)
    rw [hψχ x hx] at hh
    simp only [mem_union, hread x (hCW hx)]
    exact ⟨hh.1.trans (even_half_planes _).symm, hh.2.trans (odd_half_planes _).symm⟩
  constructor
  · rw [cone_union, ← hcone 0, ← hcone 2, ← inter_union_distrib_left]
    ext x
    exact ⟨fun h => ⟨h.1, (hlocal x h.1).1.mp h.2⟩,
      fun h => ⟨h.1, (hlocal x h.1).1.mpr h.2⟩⟩
  · rw [cone_union, ← hcone 1, ← hcone 3, ← inter_union_distrib_left]
    ext x
    exact ⟨fun h => ⟨h.1, (hlocal x h.1).2.mp h.2⟩,
      fun h => ⟨h.1, (hlocal x h.1).2.mpr h.2⟩⟩

open Classical in
theorem comparable_circle_face_mem_page_boundary [FiniteDimensional ℝ E]
    (R Γ : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hΓR : Γ.faces ⊆ R.faces) {s : Finset E} (hs : s ∈ Γ.faces)
    {W : Set E} {P : Fin 4 → Set E} {q : Fin 4 → (Fin 3 → ℝ) → E}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (P i))
    (hPR : ∀ i, (PiecewiseLinear.restrict R (P i)).space = P i)
    (hbd : ∀ x ∈ R.space ∩ W, ∀ i, x ∈ q i '' stdSimplexBoundary 2 ↔ x ∈ Γ.space)
    (hstar : (⋃ v ∈ s, closedStar R v) ⊆ W)
    {t : Finset E} (ht : t ∈ Γ.faces) (hcomp : s ⊆ t ∨ t ⊆ s) (i : Fin 4) :
    t ∈ (boundaryComplex 2 (PiecewiseLinear.restrict R (P i))).faces := by
  let L := PiecewiseLinear.restrict R (P i)
  let _ : Finite L.faces := (restrict_faces_finite R _).to_subtype
  have hLsp : L.space = P i := hPR i
  have hLbd := (hq i).image_stdSimplexBoundary_eq_boundaryComplex L hLsp
  obtain ⟨v, hvs, hvt⟩ : ∃ v, v ∈ s ∧ v ∈ t := by
    rcases hcomp with h | h
    · obtain ⟨v, hv⟩ := Γ.nonempty_of_mem_faces hs
      exact ⟨v, hv, h hv⟩
    · obtain ⟨v, hv⟩ := Γ.nonempty_of_mem_faces ht
      exact ⟨v, h hv, hv⟩
  have hc : t.centroid ℝ id ∈ convexHull ℝ (t : Set E) :=
    t.centroid_mem_convexHull (Γ.nonempty_of_mem_faces ht)
  have hcW : t.centroid ℝ id ∈ W :=
    hstar (mem_iUnion₂.mpr ⟨v, hvs, mem_iUnion₂.mpr
      ⟨t, ⟨hΓR ht, subset_convexHull ℝ _ hvt⟩, hc⟩⟩)
  apply mem_faces_of_mem_openSimplex_of_mem_space
    ((boundaryComplex_faces_subset 2 L).trans (restrict_faces_subset R _)) (hΓR ht)
    (centroid_mem_openSimplex_of_mem_faces R t (hΓR ht))
  rw [← hLbd]
  exact (hbd _ ⟨R.convexHull_subset_space (hΓR ht) hc, hcW⟩ i).mpr
    (Γ.convexHull_subset_space ht hc)

end DifferentialGeometry.Topology.PiecewiseLinear

import DifferentialGeometry.Topology.PiecewiseLinear.CellComplex

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isSubdivision_of_forall_convexHull_eq_biUnion (K' K : Geometry.SimplicialComplex ℝ E)
    (hspace : K'.space = K.space)
    (h : ∀ t ∈ K.faces, convexHull ℝ (t : Set E) =
      ⋃ s ∈ {s ∈ K'.faces | convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)},
        convexHull ℝ (s : Set E)) : IsSubdivision K' K := by
  refine ⟨hspace, fun f hf => ?_⟩
  have hx : (f.centroid ℝ id) ∈ openSimplex f := centroid_mem_openSimplex (K'.nonempty_of_mem_faces hf)
  have hxK : f.centroid ℝ id ∈ K.space :=
    hspace ▸ K'.convexHull_subset_space hf (openSimplex_subset_convexHull f hx)
  obtain ⟨t, ht, hxt⟩ := K.mem_space_iff.mp hxK
  rw [h t ht] at hxt
  obtain ⟨f', ⟨hf', hf't⟩, hxf'⟩ := mem_iUnion₂.mp hxt
  refine ⟨t, ht, ?_⟩
  exact (convexHull_mono (Finset.coe_subset.mpr
    (face_subset_of_mem_openSimplex_of_mem_convexHull K' hf hf' hx hxf'))).trans hf't

variable [FiniteDimensional ℝ E]

theorem exists_simplicialComplex_of_forall_isHPolytope {J : Type*} [Finite J] (C : J → Set E)
    (hC : ∀ j, IsHPolytope (C j)) :
    ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = ⋃ j, C j ∧
      ∀ j, C j = ⋃ s ∈ {s ∈ K.faces | convexHull ℝ (s : Set E) ⊆ C j}, convexHull ℝ (s : Set E) := by
  classical
  choose κ hκ L c hCeq using fun j => (hC j).2
  have := hκ
  let l : (Σ j, κ j) → E →ᵃ[ℝ] ℝ := fun p =>
    (L p.1 p.2).toAffineMap - AffineMap.const ℝ E (c p.1 p.2)
  have hl : ∀ (p : Σ j, κ j) (x : E), l p x = L p.1 p.2 x - c p.1 p.2 := fun p x => by
    simp [l]
  have hcell : ∀ j, IsCellClosed l (C j) := by
    intro j x hx y hy
    rw [hCeq j] at hx ⊢
    intro k
    have hxk : l ⟨j, k⟩ x ≤ 0 := by
      rw [hl]
      linarith [hx k]
    have hyk := (mem_closedCell_iff_forall l).mp hy ⟨j, k⟩
    have hsign : SignType.sign (l ⟨j, k⟩ x) = 0 ∨ SignType.sign (l ⟨j, k⟩ x) = -1 := by
      rcases hxk.lt_or_eq with h | h
      · exact Or.inr (sign_eq_neg_one_iff.mpr h)
      · exact Or.inl (sign_eq_zero_iff.mpr h)
    have hyk' : l ⟨j, k⟩ y ≤ 0 := by
      rcases hsign with h | h
      · exact (hyk.1 h).le
      · exact hyk.2.2 h
    rw [hl] at hyk'
    linarith
  have hP : IsCellClosed l (⋃ j, C j) := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact (hcell j x hj).trans (subset_iUnion C j)
  have hPc : IsCompact (⋃ j, C j) := isCompact_iUnion fun j => (hC j).1
  refine ⟨cellDerived l (⋃ j, C j), finite_cellDerived_faces l _, space_cellDerived l _ hP hPc,
    fun j => eq_biUnion_cellDerived_faces l _ hP hPc (hcell j) (subset_iUnion C j)⟩

theorem IsPolyhedron.exists_simplicialComplex {P : Set E} (hP : IsPolyhedron P) :
    ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = P := by
  classical
  obtain ⟨ι, hι, C, hC, rfl⟩ := hP
  have := hι
  obtain ⟨K, hfin, hspace, -⟩ := exists_simplicialComplex_of_forall_isHPolytope C hC
  exact ⟨K, hfin, hspace⟩

theorem exists_isSubdivision_subcomplexes (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {J : Type*} [Finite J] (Q : J → Set E) (hQ : ∀ j, IsPolyhedron (Q j))
    (hQK : ∀ j, Q j ⊆ K.space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      ∀ j, Q j = ⋃ s ∈ {s ∈ K'.faces | convexHull ℝ (s : Set E) ⊆ Q j}, convexHull ℝ (s : Set E) := by
  classical
  choose κ hκ C hC hQeq using hQ
  have := hκ
  let C' : K.faces ⊕ (Σ j, κ j) → Set E := fun p =>
    match p with
    | Sum.inl t => convexHull ℝ ((t : Finset E) : Set E)
    | Sum.inr ⟨j, i⟩ => C j i
  have hC' : ∀ p, IsHPolytope (C' p) := by
    rintro (t | ⟨j, i⟩)
    · exact isHPolytope_convexHull_of_affineIndependent _ (K.indep t.2)
    · exact hC j i
  obtain ⟨K', hfin, hspace, hunion⟩ := exists_simplicialComplex_of_forall_isHPolytope C' hC'
  have hspace' : K'.space = K.space := by
    rw [hspace]
    apply Subset.antisymm
    · refine iUnion_subset fun p => ?_
      rcases p with t | ⟨j, i⟩
      · exact K.convexHull_subset_space t.2
      · exact (subset_iUnion (C j) i).trans ((hQeq j).symm.subset.trans (hQK j))
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := K.mem_space_iff.mp hx
      exact mem_iUnion.mpr ⟨Sum.inl ⟨t, ht⟩, hxt⟩
  refine ⟨K', isSubdivision_of_forall_convexHull_eq_biUnion K' K hspace'
    fun t ht => hunion (Sum.inl ⟨t, ht⟩), hfin, fun j => ?_⟩
  apply Subset.antisymm
  · intro x hx
    have hx' : x ∈ ⋃ i, C j i := (hQeq j).subset hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx'
    have hxi' : x ∈ C' (Sum.inr ⟨j, i⟩) := hxi
    rw [hunion (Sum.inr ⟨j, i⟩)] at hxi'
    obtain ⟨s, ⟨hs, hsC⟩, hxs⟩ := mem_iUnion₂.mp hxi'
    exact mem_biUnion (s := {s ∈ K'.faces | convexHull ℝ (s : Set E) ⊆ Q j})
      (t := fun s : Finset E => convexHull ℝ (s : Set E))
      ⟨hs, hsC.trans ((subset_iUnion (C j) i).trans (hQeq j).symm.subset)⟩ hxs
  · exact iUnion₂_subset fun s hs => hs.2

theorem exists_common_subdivision (K₁ K₂ : Geometry.SimplicialComplex ℝ E) [Finite K₁.faces]
    [Finite K₂.faces] (h : K₁.space = K₂.space) :
    ∃ K : Geometry.SimplicialComplex ℝ E, IsSubdivision K K₁ ∧ IsSubdivision K K₂ ∧
      K.faces.Finite := by
  classical
  obtain ⟨K, hK₁, hfin, hunion⟩ := exists_isSubdivision_subcomplexes K₁
    (fun t : K₂.faces => convexHull ℝ ((t : Finset E) : Set E))
    (fun t => isPolyhedron_convexHull_of_affineIndependent _ (K₂.indep t.2))
    (fun t => h ▸ K₂.convexHull_subset_space t.2)
  refine ⟨K, hK₁, isSubdivision_of_forall_convexHull_eq_biUnion K K₂ (hK₁.space_eq.trans h)
    fun t ht => hunion ⟨t, ht⟩, hfin⟩

end DifferentialGeometry.Topology.PiecewiseLinear

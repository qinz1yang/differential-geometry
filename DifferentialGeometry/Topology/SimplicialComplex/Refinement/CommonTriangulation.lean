import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Geometry.SimplexInequalities

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq E] in
theorem simplicialRefines.face_card_le {L K : SimplicialComplex ℝ E}
    (href : simplicialRefines L K) {n : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ n + 1) :
    ∀ s ∈ L.faces, s.card ≤ n + 1 := by
  classical
  intro s hs
  obtain ⟨t, ht, hst⟩ := href s hs
  exact ((L.indep hs).card_le_card_of_subset_affineSpan
    (fun x hx => convexHull_subset_affineSpan _ (hst (subset_convexHull ℝ _ hx)))).trans (hd t ht)

def complexRestriction (K S : SimplicialComplex ℝ E) : SimplicialComplex ℝ E where
  faces := {s | s ∈ K.faces ∧ ∃ t ∈ S.faces, (s : Set E) ⊆ convexHull ℝ (t : Set E)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    intro u hus hu
    obtain ⟨t, ht, hst⟩ := hs.2
    exact ⟨K.down_closed hs.1 hus hu, t, ht, fun x hx => hst (hus hx)⟩
  indep := fun hs => K.indep hs.1
  inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1

omit [DecidableEq E] in
theorem complexRestriction_faces_subset (K S : SimplicialComplex ℝ E) :
    (complexRestriction K S).faces ⊆ K.faces := by
  classical
  exact fun _ h => h.1

omit [DecidableEq E] in
theorem complexRestriction_refines_right (K S : SimplicialComplex ℝ E) :
    simplicialRefines (complexRestriction K S) S := by
  classical
  intro s hs
  obtain ⟨t, ht, hst⟩ := hs.2
  exact ⟨t, ht, convexHull_min hst (convex_convexHull ℝ _)⟩

omit [DecidableEq E] in
theorem complexRestriction_finite_faces (K S : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    (complexRestriction K S).faces.Finite := by
  classical
  exact hK.subset (complexRestriction_faces_subset K S)

omit [DecidableEq E] in
theorem complexRestriction_space_subset (K S : SimplicialComplex ℝ E) :
    (complexRestriction K S).space ⊆ K.space ∩ S.space := by
  classical
  intro x hx
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  obtain ⟨t, ht, hst⟩ := complexRestriction_refines_right K S s hs
  exact ⟨K.convexHull_subset_space hs.1 hxs, S.convexHull_subset_space ht (hst hxs)⟩

omit [DecidableEq E] in
theorem complexRestriction_space_of_compatible (K S : SimplicialComplex ℝ E)
    (hcompat : ∀ t ∈ S.faces,
      (vertexRestriction K (convexHull ℝ (t : Set E))).space =
        K.space ∩ convexHull ℝ (t : Set E)) :
    (complexRestriction K S).space = K.space ∩ S.space := by
  classical
  apply (complexRestriction_space_subset K S).antisymm
  rintro x ⟨hxK, hxS⟩
  obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hxS
  have hx : x ∈ (vertexRestriction K (convexHull ℝ (t : Set E))).space := by
    rw [hcompat t ht]
    exact ⟨hxK, hxt⟩
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  exact (complexRestriction K S).convexHull_subset_space ⟨hs.1, t, ht, hs.2⟩ hxs

variable [FiniteDimensional ℝ E]

omit [DecidableEq E] in
theorem exists_subdivision_containing_simplices {ι : Type*} [Finite ι]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (V : ι → Finset E)
    (hV : ∀ i, AffineIndependent ℝ ((↑) : V i → E))
    {n : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ n + 1) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ (∀ s ∈ L.faces, s.card ≤ n + 1) ∧
      ∀ i, (vertexRestriction L (convexHull ℝ (V i : Set E))).space =
        K.space ∩ convexHull ℝ (V i : Set E) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose F hF using fun i => exists_affine_inequalities_of_affineIndependent (V i) (hV i)
  obtain ⟨L, hL, hspace, href, hdim, hrestr⟩ :=
    exists_subdivision_with_halfspace_subcomplexes K hK Finset.univ F hd
  refine ⟨L, hL, hspace, href, hdim, ?_⟩
  intro i
  have hr := hrestr i (Finset.mem_univ _)
  rwa [← hF i] at hr

omit [DecidableEq E] in
theorem exists_common_triangulation (K S : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hS : S.faces.Finite) {n : ℕ}
    (hd : ∀ s ∈ K.faces, s.card ≤ n + 1) :
    ∃ L J : SimplicialComplex ℝ E,
      L.faces.Finite ∧ L.space = K.space ∧ simplicialRefines L K ∧
      (∀ s ∈ L.faces, s.card ≤ n + 1) ∧ J.faces.Finite ∧ J.faces ⊆ L.faces ∧
      J.space = K.space ∩ S.space ∧ simplicialRefines J S := by
  classical
  let : Fintype S.faces := hS.fintype
  obtain ⟨L, hL, hspace, href, hdim, hcompat⟩ :=
    exists_subdivision_containing_simplices K hK (fun s : S.faces => s.1)
      (fun s => S.indep s.2) hd
  refine ⟨L, complexRestriction L S, hL, hspace, href, hdim,
    complexRestriction_finite_faces L S hL, complexRestriction_faces_subset L S, ?_,
    complexRestriction_refines_right L S⟩
  rw [complexRestriction_space_of_compatible L S (fun t ht => ?_), hspace]
  simpa only [hspace] using hcompat ⟨t, ht⟩

omit [DecidableEq E] in
theorem exists_subdivision_containing_complex (K S : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hS : S.faces.Finite) (hSK : S.space ⊆ K.space) {n : ℕ}
    (hd : ∀ s ∈ K.faces, s.card ≤ n + 1) :
    ∃ L J : SimplicialComplex ℝ E,
      L.faces.Finite ∧ L.space = K.space ∧ simplicialRefines L K ∧
      (∀ s ∈ L.faces, s.card ≤ n + 1) ∧ J.faces.Finite ∧ J.faces ⊆ L.faces ∧
      J.space = S.space ∧ simplicialRefines J S := by
  classical
  obtain ⟨L, J, hL, hspace, href, hdim, hJ, hJL, hJspace, hJref⟩ :=
    exists_common_triangulation K S hK hS hd
  exact ⟨L, J, hL, hspace, href, hdim, hJ, hJL,
    hJspace.trans (inter_eq_right.mpr hSK), hJref⟩

end DifferentialGeometry.Topology.Engulfing

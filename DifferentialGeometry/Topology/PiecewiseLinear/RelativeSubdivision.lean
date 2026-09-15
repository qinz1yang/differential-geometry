import DifferentialGeometry.Topology.PiecewiseLinear.RegularNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.StellarSphere
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem regularNeighborhoodIn_space_subset_of_isSubdivision
    {K R : Geometry.SimplicialComplex ℝ E} (hR : IsSubdivision R K) (A : Set E) :
    (regularNeighborhoodIn R A).space ⊆ (regularNeighborhoodIn K A).space := by
  intro x hx
  obtain ⟨s, ⟨_, t, ht, hst, y, hyt, hyA⟩, hxs⟩ := (regularNeighborhoodIn R A).mem_space_iff.mp hx
  obtain ⟨u, hu, htu⟩ := hR.exists_face_subset ht
  exact (regularNeighborhoodIn K A).convexHull_subset_space
    ⟨hu, u, hu, Finset.Subset.refl u, y, htu hyt, hyA⟩
      (htu (convexHull_mono (Finset.coe_subset.mpr hst) hxs))

theorem exists_isSubdivision_extension_of_disjoint
    {K A B : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hA : A.faces ⊆ K.faces) (hB : B.faces ⊆ K.faces) (hAB : Disjoint A.space B.space)
    {B' : Geometry.SimplicialComplex ℝ E} [Finite B'.faces] (hB' : IsSubdivision B' B) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      A.faces ⊆ R.faces ∧ B'.faces ⊆ R.faces ∧
        ∀ s ∈ R.faces, (∀ v ∈ s, {v} ∈ B'.faces) → s ∈ B'.faces := by
  classical
  let H := unionComplex A B (fun _ hs _ ht => K.inter_subset_convexHull (hA hs) (hB ht))
  have hAB' : Disjoint A.space B'.space := hB'.space_eq.symm ▸ hAB
  have hcross : ∀ s ∈ A.faces, ∀ t ∈ B'.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
    rintro s hs t ht x ⟨hxs, hxt⟩
    exact (Set.disjoint_left.mp hAB' (A.convexHull_subset_space hs hxs)
      (B'.convexHull_subset_space ht hxt)).elim
  let H' := unionComplex A B' hcross
  have hHK : H.faces ⊆ K.faces := fun _ hs => hs.elim (fun h => hA h) (fun h => hB h)
  have hH' : IsSubdivision H' H := by
    refine ⟨?_, ?_⟩
    · exact (unionComplex_space A B' hcross).trans
        ((congrArg (A.space ∪ ·) hB'.space_eq).trans (unionComplex_space A B _).symm)
    · rintro s (hs | hs)
      · exact ⟨s, Or.inl hs, Subset.refl _⟩
      · obtain ⟨t, ht, hst⟩ := hB'.exists_face_subset hs
        exact ⟨t, Or.inr ht, hst⟩
  have hfinA := (Set.toFinite K.faces).subset hA
  have := (unionComplex_faces_finite A B' hcross hfinA (Set.toFinite _)).to_subtype
  let R := relDerived hHK hH' (centroid_mem_openSimplex_of_mem_faces K)
  have hHR : H'.faces ⊆ R.faces := faces_subset_relDerived _ _ _
  refine ⟨R, relDerived_isSubdivision _ _ _, relDerived_faces_finite _ _ _,
    fun _ hs => hHR (Or.inl hs), fun _ hs => hHR (Or.inr hs), ?_⟩
  intro s hs hv
  have hsH := mem_faces_of_mem_relDerived_of_forall_singleton_mem hHK hH'
    (centroid_mem_openSimplex_of_mem_faces K) hs (fun v hvs => Or.inr (hv v hvs))
  rcases hsH with hsA | hsB
  · obtain ⟨v, hvs⟩ := A.nonempty_of_mem_faces hsA
    exact (Set.disjoint_left.mp hAB' (A.convexHull_subset_space hsA (subset_convexHull ℝ _ hvs))
      (B'.convexHull_subset_space (hv v hvs) (subset_convexHull ℝ _ (by simp)))).elim
  · exact hsB

theorem subset_restrict_compl_space_of_disjoint_regularNeighborhoodIn
    (K A : Geometry.SimplicialComplex ℝ E) {Q : Set E} (hQK : Q ⊆ K.space)
    (hdis : Disjoint (regularNeighborhoodIn K A.space).space Q) :
    Q ⊆ (restrict K A.spaceᶜ).space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp (hQK hx)
  refine (restrict K A.spaceᶜ).convexHull_subset_space ⟨hs, fun y hys hyA => ?_⟩ hxs
  apply Set.disjoint_left.mp hdis ?_ hx
  exact (regularNeighborhoodIn K A.space).convexHull_subset_space
    ⟨hs, s, hs, Finset.Subset.refl s, y, hys, hyA⟩ hxs

theorem exists_isSubdivision_restrict_space_preserving_subcomplex [FiniteDimensional ℝ E]
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hA : A.faces ⊆ K.faces)
    {Q : Set E} (hQ : IsPolyhedron Q) (hQK : Q ⊆ K.space)
    (hdis : Disjoint (regularNeighborhoodIn K A.space).space Q) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      A.faces ⊆ R.faces ∧ (restrict R Q).space = Q := by
  classical
  let B := restrict K A.spaceᶜ
  have := (restrict_faces_finite K A.spaceᶜ).to_subtype
  have hQB := subset_restrict_compl_space_of_disjoint_regularNeighborhoodIn K A hQK hdis
  obtain ⟨B', hB', hfinB', hQ'⟩ := exists_isSubdivision_restrict_space B hQ hQB
  have := hfinB'.to_subtype
  have hAB : Disjoint A.space B.space := by
    rw [Set.disjoint_left]
    exact fun x hx hxb => restrict_space_subset K A.spaceᶜ hxb hx
  obtain ⟨R, hR, hfinR, hAR, hB'R, -⟩ :=
    exists_isSubdivision_extension_of_disjoint hA (restrict_faces_subset K A.spaceᶜ) hAB hB'
  refine ⟨R, hR, hfinR, hAR, Subset.antisymm (restrict_space_subset R Q) ?_⟩
  intro x hx
  obtain ⟨s, hs, hxs⟩ := (restrict B' Q).mem_space_iff.mp (hQ'.symm ▸ hx)
  exact (restrict R Q).convexHull_subset_space ⟨hB'R hs.1, hs.2⟩ hxs

end DifferentialGeometry.Topology.PiecewiseLinear

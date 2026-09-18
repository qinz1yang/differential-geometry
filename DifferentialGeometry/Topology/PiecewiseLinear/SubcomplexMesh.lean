import DifferentialGeometry.Topology.PiecewiseLinear.LinkDimension
import DifferentialGeometry.Topology.PiecewiseLinear.Mesh
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeDerived
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_isSubdivision_diam_lt_restrict_isSubdivision
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hLK : L.faces ⊆ K.faces)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      (∀ s ∈ K'.faces, diam (convexHull ℝ (s : Set E)) < ε) ∧
        IsSubdivision (restrict K' L.space) L := by
  obtain ⟨N, hN⟩ := ((Set.toFinite K.faces).image (fun s : Finset E => s.card)).bddAbove
  have hcard : ∀ s ∈ K.faces, s.card ≤ N + 1 :=
    fun s hs => (hN (mem_image_of_mem _ hs)).trans (Nat.le_succ N)
  obtain ⟨K', hK', hfin, -, hdiam⟩ := exists_isSubdivision_diam_lt K hcard hε
  exact ⟨K', hK', hfin, hdiam, hK'.restrict L hLK⟩

theorem exists_face_notMem_diam_ge_of_isSubdivision_of_faces_subset
    {K K' L : Geometry.SimplicialComplex ℝ E} [Finite K'.faces]
    (hK' : IsSubdivision K' K) (hLK : L.faces ⊆ K.faces) (hLK' : L.faces ⊆ K'.faces)
    {τ σ : Finset E} (hτ : τ ∈ L.faces) (hσ : σ ∈ K.faces) (hτσ : τ ⊆ σ) (hσL : σ ∉ L.faces) :
    ∃ s ∈ K'.faces, s ∉ L.faces ∧ τ ⊆ s ∧
      diam (convexHull ℝ (τ : Set E)) ≤ diam (convexHull ℝ (s : Set E)) := by
  classical
  have hx : τ.centroid ℝ id ∈ openSimplex τ := centroid_mem_openSimplex (L.nonempty_of_mem_faces hτ)
  have hxσ : τ.centroid ℝ id ∈ convexHull ℝ (σ : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr hτσ) (openSimplex_subset_convexHull τ hx)
  let F : Set (Finset E) :=
    {s ∈ K'.faces | convexHull ℝ (s : Set E) ⊆ convexHull ℝ (σ : Set E)}
  have hFfin : F.Finite := (Set.toFinite K'.faces).subset fun s hs => hs.1
  have hcover : openSimplex σ ⊆ ⋃ s ∈ F, (convexHull ℝ (s : Set E) ∩ openSimplex σ) := by
    intro y hy
    have hyσ : y ∈ convexHull ℝ (σ : Set E) := openSimplex_subset_convexHull σ hy
    rw [hK'.convexHull_eq_biUnion hσ] at hyσ
    obtain ⟨s, hs, hys⟩ := mem_iUnion₂.mp hyσ
    exact mem_iUnion₂.mpr ⟨s, hs, hys, hy⟩
  have hxcl : τ.centroid ℝ id ∈
      closure (⋃ s ∈ F, (convexHull ℝ (s : Set E) ∩ openSimplex σ)) :=
    closure_mono hcover (convexHull_subset_closure_openSimplex (K.nonempty_of_mem_faces hσ) hxσ)
  rw [hFfin.closure_biUnion] at hxcl
  obtain ⟨s, hsF, hxs⟩ := mem_iUnion₂.mp hxcl
  have hsK' : s ∈ K'.faces := hsF.1
  have hxs' : τ.centroid ℝ id ∈ convexHull ℝ (s : Set E) :=
    (s.finite_toSet.isCompact_convexHull ℝ).isClosed.closure_subset
      (closure_mono inter_subset_left hxs)
  have hτs : τ ⊆ s := face_subset_of_mem_openSimplex_of_mem_convexHull K' (hLK' hτ) hsK' hx hxs'
  refine ⟨s, hsK', ?_, hτs, diam_mono (convexHull_mono (Finset.coe_subset.mpr hτs))
    (s.finite_toSet.isCompact_convexHull ℝ).isBounded⟩
  intro hsL
  obtain ⟨y, hys, hyσ⟩ := closure_nonempty_iff.mp ⟨_, hxs⟩
  exact notMem_space_of_notMem_faces hLK hσ hσL hyσ (L.convexHull_subset_space hsL hys)

theorem not_exists_isSubdivision_faces_subset_forall_diam_lt
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {τ σ : Finset E} (hτ : τ ∈ L.faces) (hσ : σ ∈ K.faces) (hτσ : τ ⊆ σ) (hσL : σ ∉ L.faces)
    {ε : ℝ} (hε : ε ≤ diam (convexHull ℝ (τ : Set E))) :
    ¬ ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
        L.faces ⊆ K'.faces ∧
          ∀ s ∈ K'.faces, s ∉ L.faces → diam (convexHull ℝ (s : Set E)) < ε := by
  rintro ⟨K', hK', hfin, hLK', h⟩
  have := hfin.to_subtype
  obtain ⟨s, hs, hsL, -, hdiam⟩ :=
    exists_face_notMem_diam_ge_of_isSubdivision_of_faces_subset hK' hLK hLK' hτ hσ hτσ hσL
  exact absurd (h s hs hsL) (not_lt.mpr (hε.trans hdiam))

end DifferentialGeometry.Topology.PiecewiseLinear

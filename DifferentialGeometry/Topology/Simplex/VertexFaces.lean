import DifferentialGeometry.Topology.Simplex.VertexHomeomorphism
import DifferentialGeometry.Topology.Simplex.BoundaryRetraction

set_option autoImplicit false
noncomputable section
open Set Finset
namespace Poincare.Simplex
variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vertexMap_mem_convexHull_image_iff {v : ι → E} (hv : AffineIndependent ℝ v)
    (s : Set ι) (x : stdSimplex ℝ ι) :
    vertexMap v x ∈ convexHull ℝ (v '' s) ↔ ∀ i ∉ s, x.val i = 0 := by
  classical
  constructor
  · intro hx i hi
    apply hv.eq_zero_of_affineCombination_mem_affineSpan x.prop.2 (s := s)
      (i := i) _ (mem_univ i) hi
    rw [Finset.affineCombination_eq_linear_combination _ _ _ x.prop.2]
    exact convexHull_subset_affineSpan (v '' s) hx
  · intro hx
    have hs : ∑ i ∈ univ.filter (· ∈ s), x.val i = 1 := by
      rw [sum_subset (filter_subset _ _) (fun i _ hi => hx i (by simpa using hi))]
      exact x.prop.2
    have he : ∑ i ∈ univ.filter (· ∈ s), x.val i • v i = vertexMap v x := by
      apply sum_subset (filter_subset _ _)
      intro i _ hi
      rw [hx i (by simpa using hi), zero_smul]
    rw [← he]
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => x.prop.1 i) hs
      (fun i hi => subset_convexHull ℝ _ ⟨i, (mem_filter.mp hi).2, rfl⟩)


theorem vertexMap_mem_proper_face_iff {v : ι → E} (hv : AffineIndependent ℝ v)
    (x : stdSimplex ℝ ι) :
    (∃ s : Finset ι, s ≠ Finset.univ ∧ vertexMap v x ∈ convexHull ℝ (v '' (s : Set ι))) ↔
      x ∈ boundary ι := by
  classical
  constructor
  · rintro ⟨s, hs, hx⟩
    have he : ∃ i, i ∉ s := by
      by_contra h
      push Not at h
      exact hs (Finset.eq_univ_iff_forall.mpr h)
    obtain ⟨i, hi⟩ := he
    exact ⟨i, (vertexMap_mem_convexHull_image_iff hv (s : Set ι) x).mp hx i hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨Finset.univ.erase i, ?_, ?_⟩
    · exact (erase_ssubset (mem_univ i)).ne
    · apply (vertexMap_mem_convexHull_image_iff hv _ x).mpr
      intro j hj
      have hji : j = i := by simpa using hj
      simpa only [hji] using hi

end Poincare.Simplex

import DifferentialGeometry.Topology.PiecewiseLinear.ArcCellTrace
import DifferentialGeometry.Topology.PiecewiseLinear.ArcDerivedNeighborhood

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
open Classical in
theorem arcChainFace_card_le_two (v : ℕ → E) (j : ℕ) : (arcChainFace v j).card ≤ 2 := by
  unfold arcChainFace
  exact Finset.card_le_two

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
open Classical in
theorem arcChainFace_injective {n : ℕ} {v : ℕ → E}
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j) {i j : ℕ} (hi : i ≤ 2 * n) (hj : j ≤ 2 * n)
    (h : arcChainFace v i = arcChainFace v j) : i = j := by
  have h₁ : arcChainFace v i ⊆ arcChainFace v j := h ▸ subset_rfl
  have h₂ : arcChainFace v j ⊆ arcChainFace v i := h ▸ subset_rfl
  rw [arcChainFace_subset_iff hinj hi hj] at h₁
  rw [arcChainFace_subset_iff hinj hj hi] at h₂
  omega

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
open Classical in
theorem arcChainFace_comparable_iff {n : ℕ} {v : ℕ → E}
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j) {i j : ℕ} (hi : i ≤ 2 * n) (hj : j ≤ 2 * n) :
    (arcChainFace v i ⊆ arcChainFace v j ∨ arcChainFace v j ⊆ arcChainFace v i) ↔
      (i = j ∨ i + 1 = j ∨ j + 1 = i) := by
  rw [arcChainFace_subset_iff hinj hi hj, arcChainFace_subset_iff hinj hj hi]
  omega

open Classical in
theorem arcChainFace_mem_arcComplexIn_faces {K : Geometry.SimplicialComplex ℝ E} {n : ℕ}
    {v : ℕ → E} (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces) {j : ℕ} (hj : j ≤ 2 * n) :
    arcChainFace v j ∈ (arcComplexIn K v n).faces :=
  ⟨arcChainFace_mem_faces hvert hedge hj, j, hj, rfl⟩

open Classical in
theorem disjoint_derivedNeighborhoodCell_arcChainFace {K : Geometry.SimplicialComplex ℝ E}
    {n : ℕ} {v : ℕ → E} (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j) {i j : ℕ} (hi : i ≤ 2 * n) (hj : j ≤ 2 * n)
    (hfar : i + 1 < j) :
    Disjoint (derivedNeighborhoodCell K (arcChainFace v i)).space
      (derivedNeighborhoodCell K (arcChainFace v j)).space :=
  disjoint_derivedNeighborhoodCell_space K (arcChainFace_mem_faces hvert hedge hi)
    (arcChainFace_mem_faces hvert hedge hj)
    (fun h => by rw [arcChainFace_subset_iff hinj hi hj] at h; omega)
    (fun h => by rw [arcChainFace_subset_iff hinj hj hi] at h; omega)

open Classical in
theorem derivedNeighborhoodCell_inter_arcComplexIn_space {K : Geometry.SimplicialComplex ℝ E}
    {n : ℕ} {v : ℕ → E} (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j) {j : ℕ} (hj0 : 1 ≤ j) (hjn : j + 1 ≤ 2 * n) :
    (derivedNeighborhoodCell K (arcChainFace v j)).space ∩ (arcComplexIn K v n).space =
      coneSet ((arcChainFace v j).centroid ℝ id)
        {({(arcChainFace v j).centroid ℝ id, (arcChainFace v (j - 1)).centroid ℝ id} :
            Finset E).centroid ℝ id,
          ({(arcChainFace v j).centroid ℝ id, (arcChainFace v (j + 1)).centroid ℝ id} :
            Finset E).centroid ℝ id} := by
  have hG : ∀ f ∈ (arcComplexIn K v n).faces, f.card ≤ 2 := by
    rintro f ⟨-, i, -, rfl⟩
    exact arcChainFace_card_le_two v i
  rw [derivedNeighborhoodCell_inter_space_eq_coneSet K (arcComplexIn K v n)
    (arcComplexIn_faces_subset K v n) hG
    (arcChainFace_mem_arcComplexIn_faces hvert hedge (by omega))]
  congr 1
  ext c
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, ⟨-, i, hi, rfl⟩, hne, hcomp, rfl⟩
    rcases (arcChainFace_comparable_iff hinj (by omega) hi).mp hcomp with hij | hij | hij
    · exact absurd (by rw [hij]) hne
    · right
      rw [hij]
    · left
      have hi' : j - 1 = i := by omega
      rw [hi']
  · rintro (rfl | rfl)
    · refine ⟨arcChainFace v (j - 1), arcChainFace_mem_arcComplexIn_faces hvert hedge (by omega),
        fun h => ?_, (arcChainFace_comparable_iff hinj (by omega) (by omega)).mpr (by omega), rfl⟩
      have := arcChainFace_injective hinj (by omega) (by omega) h
      omega
    · refine ⟨arcChainFace v (j + 1), arcChainFace_mem_arcComplexIn_faces hvert hedge (by omega),
        fun h => ?_, (arcChainFace_comparable_iff hinj (by omega) (by omega)).mpr (by omega), rfl⟩
      have := arcChainFace_injective hinj (by omega) (by omega) h
      omega

end DifferentialGeometry.Topology.PiecewiseLinear

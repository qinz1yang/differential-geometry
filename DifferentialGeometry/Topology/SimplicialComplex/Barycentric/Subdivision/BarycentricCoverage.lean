import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Subdivision.BarycentricSubdivision
import Mathlib.Algebra.BigOperators.Field

namespace DifferentialGeometry.Topology.Engulfing

open Set
open scoped BigOperators

variable {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E]

omit [DecidableEq ι] in
theorem exists_faceChain_of_weights (v : ι → E) (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hasum : ∑ i ∈ s, a i = 1) :
    ∃ C : Finset (Finset ι), C.Nonempty ∧ isFaceChain C ∧
      (∀ t ∈ C, t ⊆ s) ∧ (∑ i ∈ s, a i • v i) ∈ convexHull ℝ (chainCentroids v C : Set E) := by
  classical
  induction s using Finset.strongInductionOn generalizing a with
  | _ s ih =>
    have hs : s.Nonempty := by
      by_contra h
      have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [he] at hasum
    obtain ⟨i, hi, hmin⟩ := s.exists_min_image a hs
    let c := a i
    let η : ℝ := (s.card : ℝ) * c
    have hc : 0 ≤ c := ha i hi
    have hη0 : 0 ≤ η := mul_nonneg (Nat.cast_nonneg _) hc
    have hη1 : η ≤ 1 := by
      calc
        η = ∑ j ∈ s, c := by simp [η]
        _ ≤ ∑ j ∈ s, a j := Finset.sum_le_sum (fun j hj => hmin j hj)
        _ = 1 := hasum
    have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hs).ne'
    have hcent : η • s.centroid ℝ v = ∑ j ∈ s, c • v j := by
      rw [centroid_eq_card_inv_smul_sum s hs v, smul_smul, ← Finset.smul_sum]
      congr 1
      dsimp [η]
      field_simp
    have hres : ∑ j ∈ s, (a j - c) = 1 - η := by
      rw [Finset.sum_sub_distrib, hasum, Finset.sum_const, nsmul_eq_mul]
    have hsplit : (∑ j ∈ s, a j • v j) =
        η • s.centroid ℝ v + ∑ j ∈ s, (a j - c) • v j := by
      rw [hcent, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← add_smul]
      congr 1
      ring
    by_cases hη : η = 1
    · have hzero : ∀ j ∈ s, a j - c = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => sub_nonneg.mpr (hmin j hj))).mp
          (by simpa [hη] using hres)
      have hx : (∑ j ∈ s, a j • v j) = s.centroid ℝ v := by
        rw [hsplit, hη, one_smul]
        have hz : ∑ j ∈ s, (a j - c) • v j = 0 := Finset.sum_eq_zero
          (fun j hj => by rw [hzero j hj, zero_smul])
        rw [hz, add_zero]
      refine ⟨{s}, Finset.singleton_nonempty s, ?_, ?_, ?_⟩
      · constructor
        · simpa using hs
        · simp
      · simp
      · rw [hx]
        exact subset_convexHull ℝ _ (mem_chainCentroids.mpr ⟨s, by simp, rfl⟩)
    · have hpos : 0 < 1 - η := sub_pos.mpr (lt_of_le_of_ne hη1 hη)
      let b : ι → ℝ := fun j => (a j - c) / (1 - η)
      have hb : ∀ j ∈ s.erase i, 0 ≤ b j := fun j hj =>
        div_nonneg (sub_nonneg.mpr (hmin j (Finset.mem_of_mem_erase hj))) hpos.le
      have hbsum : ∑ j ∈ s.erase i, b j = 1 := by
        dsimp [b]
        rw [← Finset.sum_div, Finset.sum_erase_eq_sub hi, hres]
        simp only [c, sub_self, sub_zero]
        exact div_self hpos.ne'
      obtain ⟨C, hCne, hC, hCs, hCx⟩ := ih (s.erase i) (Finset.erase_ssubset hi) b hb hbsum
      have hchain : isFaceChain (insert s C) := by
        constructor
        · intro t ht
          rcases Finset.mem_insert.mp ht with hts | ht
          · subst t
            exact hs
          · exact hC.1 t ht
        · intro t ht u hu
          rcases Finset.mem_insert.mp ht with hts | ht
          · subst t
            exact Or.inr (by
              rcases Finset.mem_insert.mp hu with hus | hu
              · exact hus.subset
              · exact (hCs u hu).trans (Finset.erase_subset i s))
          · rcases Finset.mem_insert.mp hu with hus | hu
            · subst u
              exact Or.inl ((hCs t ht).trans (Finset.erase_subset i s))
            · exact hC.2 t ht u hu
      have hCsub : chainCentroids v C ⊆ chainCentroids v (insert s C) :=
        chainCentroids_mono v (Finset.subset_insert s C)
      have hleft : s.centroid ℝ v ∈ convexHull ℝ (chainCentroids v (insert s C) : Set E) :=
        subset_convexHull ℝ _ (mem_chainCentroids.mpr ⟨s, Finset.mem_insert_self s C, rfl⟩)
      have hright := convexHull_mono hCsub hCx
      have hcombo := (convex_convexHull ℝ (chainCentroids v (insert s C) : Set E))
        hleft hright hη0 hpos.le (by ring : η + (1 - η) = 1)
      have hresvec : (1 - η) • (∑ j ∈ s.erase i, b j • v j) =
          ∑ j ∈ s, (a j - c) • v j := by
        rw [Finset.smul_sum]
        simp_rw [smul_smul]
        have hterm (j : ι) : (1 - η) * b j = a j - c := by
          dsimp [b]
          field_simp
        simp_rw [hterm]
        rw [Finset.sum_erase_eq_sub hi]
        simp [c]
      refine ⟨insert s C, Finset.insert_nonempty s C, hchain, ?_, ?_⟩
      · intro t ht
        rcases Finset.mem_insert.mp ht with hts | ht
        · exact hts.subset
        · exact (hCs t ht).trans (Finset.erase_subset i s)
      · rwa [hresvec, ← hsplit] at hcombo

theorem barycentricComplex_space_eq (v : ι → E) (hv : AffineIndependent ℝ v) :
    (barycentricComplex v hv).space = convexHull ℝ (range v) := by
  apply (barycentricComplex_space_subset v hv).antisymm
  intro x hx
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, a, ha, hasum, hax⟩ := hx
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hasum] at hax
  obtain ⟨C, hCne, hC, -, hCx⟩ := exists_faceChain_of_weights v s a ha hasum
  exact Geometry.SimplicialComplex.mem_space_iff.mpr
    ⟨chainCentroids v C, ⟨C, hCne, hC, rfl⟩, hax ▸ hCx⟩

theorem barycentricSimplex_space_eq (V : Finset E)
    (hV : AffineIndependent ℝ ((↑) : V → E)) :
    (barycentricSimplex V hV).space = convexHull ℝ (V : Set E) := by
  classical
  have hr : range (Subtype.val : V → E) = (V : Set E) := by
    ext x
    exact ⟨fun ⟨i, hi⟩ => hi ▸ i.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  change (barycentricComplex (Subtype.val : V → E) hV).space = _
  rw [barycentricComplex_space_eq, hr]

end DifferentialGeometry.Topology.Engulfing

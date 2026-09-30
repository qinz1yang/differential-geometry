import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Coordinates.BarycentricChain
import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Coordinates.BarycentricWeights
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace DifferentialGeometry.Topology.Engulfing

open Set

variable {ι : Type*} [DecidableEq ι]

private theorem faceWeightTerm_nonneg {a : Finset ι → ℝ} {s : Finset ι}
    (ha : 0 ≤ a s) (i : ι) : 0 ≤ (if i ∈ s then a s / (s.card : ℝ) else 0) := by
  split_ifs
  · exact div_nonneg ha (Nat.cast_nonneg _)
  · exact le_rfl

private theorem faceWeightTerm_le {a : Finset ι → ℝ} {s : Finset ι}
    (ha : 0 ≤ a s) {i j : ι} (hij : 0 < a s → i ∈ s → j ∈ s) :
    (if i ∈ s then a s / (s.card : ℝ) else 0) ≤
      (if j ∈ s then a s / (s.card : ℝ) else 0) := by
  by_cases hi : i ∈ s
  · by_cases hj : j ∈ s
    · simp [hi, hj]
    · have hz : a s = 0 := le_antisymm (le_of_not_gt (fun h => hj (hij h hi))) ha
      simp [hz]
  · simp only [hi, ite_false]
    exact faceWeightTerm_nonneg ha j

theorem faceWeightCoord_le {C : Finset (Finset ι)} {a : Finset ι → ℝ}
    (ha : ∀ s ∈ C, 0 ≤ a s) {i j : ι}
    (hij : ∀ s ∈ C, 0 < a s → i ∈ s → j ∈ s) :
    faceWeightCoord C a i ≤ faceWeightCoord C a j := by
  apply Finset.sum_le_sum
  intro s hs
  exact faceWeightTerm_le (ha s hs) (hij s hs)

theorem faceWeightCoord_lt {C : Finset (Finset ι)} {a : Finset ι → ℝ}
    (ha : ∀ s ∈ C, 0 ≤ a s) {i j : ι}
    (hij : ∀ s ∈ C, 0 < a s → i ∈ s → j ∈ s)
    {s : Finset ι} (hs : s ∈ C) (has : 0 < a s) (his : i ∉ s) (hjs : j ∈ s) :
    faceWeightCoord C a i < faceWeightCoord C a j := by
  apply Finset.sum_lt_sum (fun t ht => faceWeightTerm_le (ha t ht) (hij t ht))
  refine ⟨s, hs, ?_⟩
  simp only [his, hjs, ite_false, ite_true]
  exact div_pos has (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨j, hjs⟩))

theorem faceWeightCoord_pos_of_mem {C : Finset (Finset ι)} {a : Finset ι → ℝ}
    (ha : ∀ s ∈ C, 0 ≤ a s) {s : Finset ι} (hs : s ∈ C) (has : 0 < a s)
    {i : ι} (hi : i ∈ s) : 0 < faceWeightCoord C a i := by
  have hpos : 0 < (if i ∈ s then a s / (s.card : ℝ) else 0) := by
    rw [ite_eq_left hi]
    exact div_pos has (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨i, hi⟩))
  exact hpos.trans_le (Finset.single_le_sum (fun t ht => faceWeightTerm_nonneg (ha t ht) i) hs)

theorem isFaceChain.mem_iff_le_faceWeightCoord {C : Finset (Finset ι)}
    (hC : isFaceChain C) {a : Finset ι → ℝ} (ha : ∀ s ∈ C, 0 ≤ a s)
    {s : Finset ι} (hs : s ∈ C) (has : 0 < a s) {i : ι} (hi : i ∈ s)
    (hmin : ∀ t ∈ C, 0 < a t → i ∈ t → s ⊆ t) (j : ι) :
    j ∈ s ↔ faceWeightCoord C a i ≤ faceWeightCoord C a j := by
  constructor
  · intro hj
    exact faceWeightCoord_le ha (fun t ht hpos hit => hmin t ht hpos hit hj)
  · intro hle
    by_contra hj
    have hlt : faceWeightCoord C a j < faceWeightCoord C a i := by
      apply faceWeightCoord_lt ha (s := s) (hs := hs) (has := has) (his := hj) (hjs := hi)
      intro t ht _ hjt
      rcases hC.2 s hs t ht with hst | hts
      · exact hst hi
      · exact False.elim (hj (hts hjt))
    exact (not_lt_of_ge hle) hlt

theorem isFaceChain.exists_face_superlevel {C : Finset (Finset ι)} (hC : isFaceChain C)
    {a : Finset ι → ℝ} (ha : ∀ s ∈ C, 0 ≤ a s) {i : ι}
    (hi : 0 < faceWeightCoord C a i) :
    ∃ s ∈ C, ∀ j, j ∈ s ↔ faceWeightCoord C a i ≤ faceWeightCoord C a j := by
  classical
  let D := C.filter (fun s => i ∈ s ∧ 0 < a s)
  have hD : D.Nonempty := by
    by_contra h
    have hz : faceWeightCoord C a i = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      by_cases his : i ∈ s
      · have has : a s = 0 := le_antisymm
          (le_of_not_gt (fun hp => h ⟨s, Finset.mem_filter.mpr ⟨hs, his, hp⟩⟩)) (ha s hs)
        simp [has]
      · simp [his]
    rw [hz] at hi
    exact lt_irrefl _ hi
  obtain ⟨s, hsD, hsmall⟩ := D.exists_min_image Finset.card hD
  obtain ⟨hs, his, has⟩ := Finset.mem_filter.mp hsD
  refine ⟨s, hs, hC.mem_iff_le_faceWeightCoord ha hs has his ?_⟩
  intro t ht hat hit
  rcases hC.2 s hs t ht with hst | hts
  · exact hst
  · have hcard : s.card ≤ t.card := hsmall t (Finset.mem_filter.mpr ⟨ht, hit, hat⟩)
    exact (Finset.eq_of_subset_of_card_le hts hcard).symm.subset

theorem isFaceChain.mem_of_faceWeightCoord_eq {C D : Finset (Finset ι)}
    (hC : isFaceChain C) (hD : isFaceChain D) (a b : Finset ι → ℝ)
    (ha : ∀ s ∈ C, 0 ≤ a s) (hb : ∀ s ∈ D, 0 ≤ b s)
    (heq : faceWeightCoord C a = faceWeightCoord D b)
    {s : Finset ι} (hs : s ∈ C) (has : 0 < a s) : s ∈ D := by
  obtain ⟨i, his, hexclusive⟩ := hC.exists_exclusive_vertex hs
  have hmin : ∀ t ∈ C, 0 < a t → i ∈ t → s ⊆ t := by
    intro t ht _ hit
    rcases hC.2 s hs t ht with hst | hts
    · exact hst
    · rw [hexclusive t ht hts hit]
  have hcoordpos : 0 < faceWeightCoord D b i := by
    rw [← heq]
    exact faceWeightCoord_pos_of_mem ha hs has his
  obtain ⟨t, ht, hlevel⟩ := hD.exists_face_superlevel hb hcoordpos
  have hst : s = t := by
    ext j
    rw [hC.mem_iff_le_faceWeightCoord ha hs has his hmin j, hlevel j, heq]
  exact hst.symm ▸ ht

end DifferentialGeometry.Topology.Engulfing

import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Basic.Real.Basic

namespace DifferentialGeometry.Topology.Engulfing

open Set

variable {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E]

noncomputable def faceWeightCoord (C : Finset (Finset ι)) (a : Finset ι → ℝ) (i : ι) : ℝ :=
  ∑ s ∈ C, if i ∈ s then a s / (s.card : ℝ) else 0

omit [DecidableEq ι] in
theorem centroid_eq_card_inv_smul_sum (s : Finset ι) (hs : s.Nonempty) (v : ι → E) :
    s.centroid ℝ v = (s.card : ℝ)⁻¹ • ∑ i ∈ s, v i := by
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  simp only [Finset.centroidWeights_apply, Finset.smul_sum]

theorem faceWeightCoord_eq_zero_of_not_mem (C : Finset (Finset ι)) (a : Finset ι → ℝ)
    {i : ι} (hi : i ∉ C.biUnion id) : faceWeightCoord C a i = 0 := by
  apply Finset.sum_eq_zero
  intro s hs
  have his : i ∉ s := fun h => hi (Finset.mem_biUnion.mpr ⟨s, hs, h⟩)
  simp only [his, ite_false]

theorem sum_faceWeightCoord (C : Finset (Finset ι)) (a : Finset ι → ℝ) (T : Finset ι)
    (hne : ∀ s ∈ C, s.Nonempty) (hT : ∀ s ∈ C, s ⊆ T) :
    ∑ i ∈ T, faceWeightCoord C a i = ∑ s ∈ C, a s := by
  unfold faceWeightCoord
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  have hrestrict : (∑ i ∈ T, if i ∈ s then a s / (s.card : ℝ) else 0) =
      ∑ i ∈ s, a s / (s.card : ℝ) := by
    rw [← Finset.sum_extend_by_zero s (fun _ => a s / (s.card : ℝ))]
    exact (Finset.sum_subset (hT s hs) (fun i _ hi => by simp [hi])).symm
  rw [hrestrict, Finset.sum_const, nsmul_eq_mul]
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (hne s hs))
  field_simp

theorem sum_faceWeightCoord_smul (C : Finset (Finset ι)) (a : Finset ι → ℝ)
    (T : Finset ι) (v : ι → E) (hne : ∀ s ∈ C, s.Nonempty) (hT : ∀ s ∈ C, s ⊆ T) :
    ∑ i ∈ T, faceWeightCoord C a i • v i = ∑ s ∈ C, a s • s.centroid ℝ v := by
  unfold faceWeightCoord
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  have hrestrict : (∑ i ∈ T, (if i ∈ s then a s / (s.card : ℝ) else 0) • v i) =
      ∑ i ∈ s, (a s / (s.card : ℝ)) • v i := by
    simp_rw [ite_smul, zero_smul]
    rw [← Finset.sum_extend_by_zero s (fun i => (a s / (s.card : ℝ)) • v i)]
    exact (Finset.sum_subset (hT s hs) (fun i _ hi => by simp [hi])).symm
  rw [hrestrict, ← Finset.smul_sum, centroid_eq_card_inv_smul_sum s (hne s hs) v,
    smul_smul, div_eq_mul_inv]

theorem faceWeightCoord_eq_of_sum_eq {v : ι → E} (hv : AffineIndependent ℝ v)
    (C D : Finset (Finset ι)) (a b : Finset ι → ℝ)
    (hC : ∀ s ∈ C, s.Nonempty) (hD : ∀ s ∈ D, s.Nonempty)
    (htotal : ∑ s ∈ C, a s = ∑ s ∈ D, b s)
    (hpoint : ∑ s ∈ C, a s • s.centroid ℝ v = ∑ s ∈ D, b s • s.centroid ℝ v) :
    faceWeightCoord C a = faceWeightCoord D b := by
  let T := C.biUnion id ∪ D.biUnion id
  have hTC : ∀ s ∈ C, s ⊆ T := fun s hs i hi =>
    Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨s, hs, hi⟩)
  have hTD : ∀ s ∈ D, s ⊆ T := fun s hs i hi =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s, hs, hi⟩)
  have hweights : ∑ i ∈ T, (faceWeightCoord C a i - faceWeightCoord D b i) = 0 := by
    rw [Finset.sum_sub_distrib, sum_faceWeightCoord C a T hC hTC,
      sum_faceWeightCoord D b T hD hTD, htotal, sub_self]
  have hsum : ∑ i ∈ T, (faceWeightCoord C a i - faceWeightCoord D b i) • v i = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, sum_faceWeightCoord_smul C a T v hC hTC,
      sum_faceWeightCoord_smul D b T v hD hTD, hpoint, sub_self]
  have hzero := hv T (fun i => faceWeightCoord C a i - faceWeightCoord D b i) hweights
    (by rwa [Finset.weightedVSub_eq_linear_combination T hweights])
  funext i
  by_cases hi : i ∈ T
  · exact sub_eq_zero.mp (hzero i hi)
  · have hiC : i ∉ C.biUnion id := fun h => hi (Finset.mem_union_left _ h)
    have hiD : i ∉ D.biUnion id := fun h => hi (Finset.mem_union_right _ h)
    rw [faceWeightCoord_eq_zero_of_not_mem C a hiC,
      faceWeightCoord_eq_zero_of_not_mem D b hiD]

end DifferentialGeometry.Topology.Engulfing

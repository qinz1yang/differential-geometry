import DifferentialGeometry.Topology.SimplicialComplex.Realization.SimplicialGluing
import Mathlib.Analysis.Convex.Combination

namespace DifferentialGeometry.Topology.Engulfing

set_option linter.unusedSectionVars false

open Set _root_.Geometry
open scoped BigOperators

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem mem_standardFace_iff (s : Finset ι) (x : ι → ℝ) :
    x ∈ convexHull ℝ (s.image (fun i => Pi.single i (1 : ℝ)) : Set (ι → ℝ)) ↔
      ((∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1) ∧ ∀ i ∉ s, x i = 0 := by
  have heq : {x : ι → ℝ | ((∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1) ∧ ∀ i ∉ s, x i = 0} =
      convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (s : Set ι)) := by
    apply Subset.antisymm
    · rintro w ⟨hw, hw0⟩
      have hsum : ∑ i ∈ s, w i = 1 := by
        rw [← hw.2]
        exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hw0 i hi)
      have h := s.centerMass_mem_convexHull (fun i _ => hw.1 i) (by rw [hsum]; norm_num)
        (fun i hi => mem_image_of_mem (fun i : ι => Pi.single i (1 : ℝ)) hi)
      rw [Finset.centerMass_eq_of_sum_1 _ _ hsum] at h
      have he : (∑ i ∈ s, w i • Pi.single i (1 : ℝ)) = w := by
        rw [Finset.sum_subset (Finset.subset_univ s)
          (fun i _ hi => by rw [hw0 i hi, zero_smul])]
        ext i
        simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
      rwa [he] at h
    · apply convexHull_min
      · rintro w ⟨i, hi, rfl⟩
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro j
          simp only [Pi.single_apply]
          split_ifs <;> norm_num
        · simp
        · intro j hj
          have hji : j ≠ i := by intro h; subst j; exact hj hi
          simp [hji]
      · intro x hx y hy a b ha hb hab
        refine ⟨⟨fun i => add_nonneg (mul_nonneg ha (hx.1.1 i))
          (mul_nonneg hb (hy.1.1 i)), ?_⟩, ?_⟩
        · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            Finset.sum_add_distrib, ← Finset.mul_sum, hx.1.2, hy.1.2, mul_one] using hab
        · intro i hi
          simp [Pi.add_apply, Pi.smul_apply, hx.2 i hi, hy.2 i hi]
  rw [← Finset.coe_image] at heq
  exact Set.ext_iff.mp heq x |>.symm

omit [DecidableEq ι] [Fintype κ] in
theorem vertexPushforward_apply_of_injOn [Finite κ] (q : ι → κ) {S : Set ι}
    (hq : S.InjOn q) {x : ι → ℝ} (hx : ∀ i ∉ S, x i = 0) {i : ι} (hi : i ∈ S) :
    vertexPushforward q x (q i) = x i := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  change (∑ j, x j • Pi.single (q j) (1 : ℝ)) (q i) = x i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    by_cases hjS : j ∈ S
    · have hqji : q j ≠ q i := fun h => hji (hq hjS hi h)
      simp [Ne.symm hqji]
    · simp [hx j hjS]
  · simp

omit [DecidableEq ι] [Fintype κ] in
theorem vertexPushforward_injective_of_supported [Finite κ] (q : ι → κ) {S : Set ι}
    (hq : S.InjOn q) {x y : ι → ℝ}
    (hx : ∀ i ∉ S, x i = 0) (hy : ∀ i ∉ S, y i = 0)
    (h : vertexPushforward q x = vertexPushforward q y) : x = y := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  funext i
  by_cases hi : i ∈ S
  · have he := congrFun h (q i)
    simpa only [vertexPushforward_apply_of_injOn q hq hx hi,
      vertexPushforward_apply_of_injOn q hq hy hi] using he
  · rw [hx i hi, hy i hi]

omit [DecidableEq ι] [Fintype κ] in
theorem vertexPushforward_apply_of_unique [Finite κ] (q : ι → κ) {i : ι}
    (hi : ∀ j, q j = q i → j = i) (x : ι → ℝ) :
    vertexPushforward q x (q i) = x i := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  change (∑ j, x j • Pi.single (q j) (1 : ℝ)) (q i) = x i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hqji : q j ≠ q i := fun h => hji (hi j h)
    simp [Ne.symm hqji]
  · simp

end

end DifferentialGeometry.Topology.Engulfing

import DifferentialGeometry.Topology.SimplicialComplex.Stellar.HyperplaneRestriction
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

omit [DecidableEq E] in
theorem exists_affine_inequalities_of_affineIndependent (V : Finset E)
    (hV : AffineIndependent ℝ ((↑) : V → E)) :
    ∃ F : Finset (E →ᵃ[ℝ] ℝ), convexHull ℝ (V : Set E) = {x | ∀ f ∈ F, 0 ≤ f x} := by
  classical
  obtain ⟨T, hVT, hT, htop⟩ := exists_subset_affineIndependent_affineSpan_eq_top hV
  let b : AffineBasis T ℝ E :=
    { toFun := Subtype.val, ind' := hT,
      tot' := by simpa only [Subtype.range_coe] using htop }
  let : Finite T := b.finite
  let : Fintype T := Fintype.ofFinite T
  let J : Finset T := Finset.univ.filter (fun i => (i : E) ∈ V)
  let F : Finset (E →ᵃ[ℝ] ℝ) := Finset.univ.image b.coord ∪
    (Finset.univ.filter (fun i : T => (i : E) ∉ V)).image (fun i => -b.coord i)
  refine ⟨F, ?_⟩
  ext x
  constructor
  · intro hx f hf
    have hnonneg (i : T) : 0 ≤ b.coord i x := by
      apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage (b.coord i)) hx
      intro v hv
      let j : T := ⟨v, hVT hv⟩
      change 0 ≤ b.coord i (b j)
      rw [b.coord_apply]
      split_ifs <;> norm_num
    have hzero (i : T) (hi : (i : E) ∉ V) : b.coord i x = 0 := by
      apply convexHull_min _ ((convex_singleton (0 : ℝ)).affine_preimage (b.coord i)) hx
      intro v hv
      let j : T := ⟨v, hVT hv⟩
      change b.coord i (b j) = 0
      apply b.coord_apply_ne
      intro hij
      exact hi (by simpa [j] using hij ▸ hv)
    rcases Finset.mem_union.mp hf with hf | hf
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hf
      exact hnonneg i
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
      change 0 ≤ -b.coord i x
      rw [hzero i (Finset.mem_filter.mp hi).2]
      norm_num
  · intro hx
    have hnonneg (i : T) : 0 ≤ b.coord i x := hx _
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    have hzero (i : T) (hi : (i : E) ∉ V) : b.coord i x = 0 := by
      have hneg := hx (-b.coord i) (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩))
      have hle : b.coord i x ≤ 0 := neg_nonneg.mp (show 0 ≤ -b.coord i x from hneg)
      exact le_antisymm hle (hnonneg i)
    have hsum : ∑ i ∈ J, b.coord i x = 1 := by
      rw [← b.sum_coord_apply_eq_one x]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      exact hzero i (by simpa [J] using hi)
    have hpoint : ∑ i ∈ J, b.coord i x • b i = x := by
      calc
        ∑ i ∈ J, b.coord i x • b i = ∑ i, b.coord i x • b i := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          rw [hzero i (by simpa [J] using hi), zero_smul]
        _ = x := b.linear_combination_coord_eq_self x
    rw [← hpoint]
    apply (convex_convexHull ℝ (V : Set E)).sum_mem (fun i _ => hnonneg i) hsum
    intro i hi
    exact subset_convexHull ℝ _ (Finset.mem_filter.mp hi).2

end DifferentialGeometry.Topology.Engulfing

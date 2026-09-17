import DifferentialGeometry.Topology.PiecewiseLinear.SimplexAffine

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def triangleBarycentricCoord (z : ℝ × ℝ) : Fin 3 → ℝ := ![1 - z.1 - z.2, z.2, z.1]

theorem sum_triangleBarycentricCoord (z : ℝ × ℝ) : ∑ i, triangleBarycentricCoord z i = 1 := by
  simp [triangleBarycentricCoord, Fin.sum_univ_succ]
  ring

theorem triangleBarycentricCoord_nonneg {z : ℝ × ℝ}
    (hz : 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) (i : Fin 3) :
    0 ≤ triangleBarycentricCoord z i := by
  fin_cases i <;> simp [triangleBarycentricCoord] <;> linarith [hz.1, hz.2.1, hz.2.2]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def triangleAffineMap (v : Fin 3 → E) : (ℝ × ℝ) →ᵃ[ℝ] E :=
  ((LinearMap.toSpanSingleton ℝ E (v 2 - v 0)).comp (LinearMap.fst ℝ ℝ ℝ) +
    (LinearMap.toSpanSingleton ℝ E (v 1 - v 0)).comp (LinearMap.snd ℝ ℝ ℝ)).toAffineMap +
      AffineMap.const ℝ (ℝ × ℝ) (v 0)

theorem triangleAffineMap_apply (v : Fin 3 → E) (z : ℝ × ℝ) :
    triangleAffineMap v z = z.1 • (v 2 - v 0) + z.2 • (v 1 - v 0) + v 0 := rfl

theorem triangleAffineMap_eq_affineCombination (v : Fin 3 → E) (z : ℝ × ℝ) :
    triangleAffineMap v z = Finset.univ.affineCombination ℝ v (triangleBarycentricCoord z) := by
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (sum_triangleBarycentricCoord z)]
  change z.1 • (v 2 - v 0) + z.2 • (v 1 - v 0) + v 0 =
    (1 - z.1 - z.2) • v 0 + (z.2 • v 1 + (z.1 • v 2 + 0))
  module

theorem triangleAffineMap_injective {v : Fin 3 → E} (hv : AffineIndependent ℝ v) :
    Function.Injective (triangleAffineMap v) := by
  intro z w hzw
  have hcoord := (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ v).mp hv
    (triangleBarycentricCoord z) (triangleBarycentricCoord w)
    (sum_triangleBarycentricCoord z) (sum_triangleBarycentricCoord w) (by
      rwa [← triangleAffineMap_eq_affineCombination, ← triangleAffineMap_eq_affineCombination])
  apply Prod.ext
  · simpa [triangleBarycentricCoord] using congrFun hcoord 2
  · simpa [triangleBarycentricCoord] using congrFun hcoord 1

private theorem convex_coordinate_triangle :
    Convex ℝ {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1} :=
  (convex_halfSpace_ge (LinearMap.fst ℝ ℝ ℝ).isLinear 0).inter
    ((convex_halfSpace_ge (LinearMap.snd ℝ ℝ ℝ).isLinear 0).inter
      (convex_halfSpace_le (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).isLinear 1))

theorem triangleAffineMap_image (v : Fin 3 → E) :
    triangleAffineMap v '' {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1} =
      convexHull ℝ (range v) := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    rw [triangleAffineMap_eq_affineCombination,
      Finset.affineCombination_eq_linear_combination _ _ _ (sum_triangleBarycentricCoord z)]
    exact (convex_convexHull ℝ (range v)).sum_mem
      (fun i _ => triangleBarycentricCoord_nonneg hz i) (sum_triangleBarycentricCoord z)
      (fun i _ => subset_convexHull ℝ _ (mem_range_self i))
  · apply convexHull_min ?_ (Convex.affine_image (triangleAffineMap v) convex_coordinate_triangle)
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨(0, 0), by norm_num, by simp [triangleAffineMap_apply]⟩
    · exact ⟨(0, 1), by norm_num, by simp [triangleAffineMap_apply]⟩
    · exact ⟨(1, 0), by norm_num, by simp [triangleAffineMap_apply]⟩

theorem triangleAffineMap_mem_convexHull_image_iff {v : Fin 3 → E}
    (hv : AffineIndependent ℝ v) (I : Set (Fin 3)) {z : ℝ × ℝ}
    (hz : 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1) :
    triangleAffineMap v z ∈ convexHull ℝ (v '' I) ↔
      ∀ i ∉ I, triangleBarycentricCoord z i = 0 := by
  classical
  constructor
  · intro h i hi
    exact hv.eq_zero_of_affineCombination_mem_affineSpan (sum_triangleBarycentricCoord z)
      (by rw [← triangleAffineMap_eq_affineCombination]; exact convexHull_subset_affineSpan _ h)
      (Finset.mem_univ i) hi
  · intro hzero
    let B : Finset (Fin 3) := Finset.univ.filter (fun i => i ∈ I)
    have hB : ∀ i, i ∈ B ↔ i ∈ I := by simp [B]
    have hsum : ∑ i ∈ B, triangleBarycentricCoord z i = 1 := by
      calc
        (∑ i ∈ B, triangleBarycentricCoord z i) = ∑ i, triangleBarycentricCoord z i :=
          Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hzero i (fun h => hi ((hB i).mpr h)))
        _ = 1 := sum_triangleBarycentricCoord z
    have hcomb : ∑ i ∈ B, triangleBarycentricCoord z i • v i =
        ∑ i, triangleBarycentricCoord z i • v i :=
      Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
        rw [hzero i (fun h => hi ((hB i).mpr h)), zero_smul])
    rw [triangleAffineMap_eq_affineCombination,
      Finset.affineCombination_eq_linear_combination _ _ _ (sum_triangleBarycentricCoord z), ← hcomb]
    exact (convex_convexHull ℝ (v '' I)).sum_mem
      (fun i _ => triangleBarycentricCoord_nonneg hz i) hsum
      (fun i hi => subset_convexHull ℝ _ ⟨i, (hB i).mp hi, rfl⟩)

theorem triangleAffineMap_mem_convexHull_image_iff_of_preserving_edges {v : Fin 3 → E}
    (hv : AffineIndependent ℝ v) (I : Set (Fin 3)) {z w : ℝ × ℝ}
    (hz : 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1)
    (hw : 0 ≤ w.1 ∧ 0 ≤ w.2 ∧ w.1 + w.2 ≤ 1)
    (hleft : z.1 = 0 ↔ w.1 = 0) (hbottom : z.2 = 0 ↔ w.2 = 0)
    (hright : z.1 + z.2 = 1 ↔ w.1 + w.2 = 1) :
    triangleAffineMap v z ∈ convexHull ℝ (v '' I) ↔
      triangleAffineMap v w ∈ convexHull ℝ (v '' I) := by
  rw [triangleAffineMap_mem_convexHull_image_iff hv I hz,
    triangleAffineMap_mem_convexHull_image_iff hv I hw]
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro _
  fin_cases i
  · change 1 - z.1 - z.2 = 0 ↔ 1 - w.1 - w.2 = 0
    constructor
    · intro h
      have := hright.mp (by linarith)
      linarith
    · intro h
      have := hright.mpr (by linarith)
      linarith
  · exact hbottom
  · exact hleft

end DifferentialGeometry.Topology.PiecewiseLinear

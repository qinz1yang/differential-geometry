import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryOfBall

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_convexHull_erase_iff_weights_eq_zero [DecidableEq E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {v : E} (hv : v ∈ T) {x : E}
    (hx : x ∈ convexHull ℝ (T : Set E)) :
    x ∈ convexHull ℝ ((T.erase v : Finset E) : Set E) ↔ weights T x v = 0 := by
  constructor
  · intro hxv
    exact weights_eq_zero_of_subset_of_notMem hT (Finset.erase_subset v T) hxv hv
      (Finset.notMem_erase v T)
  · intro hv0
    refine mem_convexHull_iff_exists_weights.mpr ⟨weights T x,
      fun w hw => weights_nonneg hx (Finset.mem_of_mem_erase hw), ?_, ?_⟩
    · have h := sum_weights hx
      rw [← Finset.add_sum_erase T _ hv, hv0, zero_add] at h
      exact h
    · have h := sum_weights_smul hx
      rw [← Finset.add_sum_erase T _ hv, hv0, zero_smul, zero_add] at h
      exact h

theorem weights_stdVertices {n : ℕ} {x : Fin (n + 2) → ℝ}
    (hx : x ∈ stdSimplex ℝ (Fin (n + 2))) (i : Fin (n + 2)) :
    weights (stdVertices n) x (Pi.single i (1 : ℝ)) = x i := by
  classical
  have hx' : x ∈ convexHull ℝ ((stdVertices n : Finset _) : Set _) := by
    rwa [convexHull_stdVertices]
  have h := congrFun (sum_weights_smul hx') i
  rw [stdVertices, Finset.sum_image (fun j _ k _ h => stdVertex_injective n h)] at h
  simpa only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, stdVertices, Finset.mem_univ, if_true] using h

theorem simplexBoundary_stdVertices_space (n : ℕ) :
    (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).space =
      stdSimplexBoundary (n + 1) := by
  classical
  rw [simplexBoundary_space _ _ (two_le_card_stdVertices n)]
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
    have hxT := convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset v (stdVertices n))) hxv
    rw [convexHull_stdVertices] at hxT
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    refine ⟨hxT, i, ?_⟩
    rw [← weights_stdVertices hxT i]
    exact weights_eq_zero_of_subset_of_notMem (stdVertices_affineIndependent n)
      (Finset.erase_subset _ _) hxv (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      (Finset.notMem_erase _ _)
  · rintro ⟨hx, i, hi⟩
    refine mem_iUnion₂.mpr ⟨Pi.single i (1 : ℝ), Finset.mem_image_of_mem _ (Finset.mem_univ i), ?_⟩
    apply (mem_convexHull_erase_iff_weights_eq_zero (stdVertices_affineIndependent n)
      (Finset.mem_image_of_mem _ (Finset.mem_univ i)) (by rwa [convexHull_stdVertices])).mpr
    rwa [weights_stdVertices hx i]

open Classical in
theorem image_stdSimplexBoundary_of_isPLHomeomorphOn_convexHull [FiniteDimensional ℝ E]
    {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E)) {n : ℕ}
    (hcard : T.card = n + 2) {f : (Fin (n + 2) → ℝ) → E}
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) (convexHull ℝ (T : Set E))) :
    f '' stdSimplexBoundary (n + 1) = (simplexBoundary T hT).space := by
  have : Finite (simplexComplex T hT).faces := (simplexComplex_faces_finite T hT).to_subtype
  have hspace : (simplexComplex T hT).space = convexHull ℝ (T : Set E) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hf' : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) (simplexComplex T hT).space := by
    rwa [hspace]
  have h := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex (simplexComplex T hT) hf'
  rw [boundaryComplex_simplexComplex hT hcard, simplexBoundary_stdVertices_space] at h
  exact h.symm

end DifferentialGeometry.Topology.PiecewiseLinear

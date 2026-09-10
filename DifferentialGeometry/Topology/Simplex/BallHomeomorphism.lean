import DifferentialGeometry.Topology.Simplex.BallCoordinates

set_option autoImplicit false

noncomputable section

open Set Metric Topology

namespace Poincare.Simplex

def coordinateSimplexBallAmbientHomeomorph (n : ℕ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_coordinateSimplex n) (interior_coordinateSimplex_nonempty n)
    (isCompact_coordinateSimplex n).isBounded).choose

theorem coordinateSimplexBallAmbientHomeomorph_image (n : ℕ) :
    coordinateSimplexBallAmbientHomeomorph n '' coordinateSimplex n =
      closedBall (0 : Fin n → ℝ) 1 := by
  have h := (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_coordinateSimplex n) (interior_coordinateSimplex_nonempty n)
    (isCompact_coordinateSimplex n).isBounded).choose_spec.2.1
  change coordinateSimplexBallAmbientHomeomorph n '' closure (coordinateSimplex n) =
    closedBall (0 : Fin n → ℝ) 1 at h
  simpa only [(isCompact_coordinateSimplex n).isClosed.closure_eq] using h


theorem coordinateSimplexBallAmbientHomeomorph_image_frontier (n : ℕ) :
    coordinateSimplexBallAmbientHomeomorph n '' frontier (coordinateSimplex n) =
      sphere (0 : Fin n → ℝ) 1 :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_coordinateSimplex n) (interior_coordinateSimplex_nonempty n)
    (isCompact_coordinateSimplex n).isBounded).choose_spec.2.2


def coordinateSimplexBallHomeomorph (n : ℕ) :
    coordinateSimplex n ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  (coordinateSimplexBallAmbientHomeomorph n).sets (by
    rw [← coordinateSimplexBallAmbientHomeomorph_image,
      Set.preimage_image_eq _ (coordinateSimplexBallAmbientHomeomorph n).injective])


def stdSimplexBallHomeomorph (n : ℕ) :
    stdSimplex ℝ (Fin (n + 1)) ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  (stdSimplexCoordinateHomeomorph n).trans (coordinateSimplexBallHomeomorph n)


theorem stdSimplexBallHomeomorph_mem_sphere_iff (n : ℕ)
    (x : stdSimplex ℝ (Fin (n + 1))) :
    (stdSimplexBallHomeomorph n x).val ∈ sphere (0 : Fin n → ℝ) 1 ↔
      x ∈ boundary (Fin (n + 1)) := by
  change coordinateSimplexBallAmbientHomeomorph n (stdSimplexCoordinateHomeomorph n x).val ∈
      sphere (0 : Fin n → ℝ) 1 ↔ _
  rw [← coordinateSimplexBallAmbientHomeomorph_image_frontier,
    (coordinateSimplexBallAmbientHomeomorph n).injective.mem_set_image,
    mem_frontier_coordinateSimplex_iff]
  simp


theorem stdSimplexBallHomeomorph_norm_eq_one_iff (n : ℕ)
    (x : stdSimplex ℝ (Fin (n + 1))) :
    ‖(stdSimplexBallHomeomorph n x).val‖ = 1 ↔ x ∈ boundary (Fin (n + 1)) := by
  simpa only [mem_sphere_zero_iff_norm] using stdSimplexBallHomeomorph_mem_sphere_iff n x

def stdSimplexBoundarySphereHomeomorph (n : ℕ) :
    boundary (Fin (n + 1)) ≃ₜ sphere (0 : Fin n → ℝ) 1 where
  toFun x := ⟨(stdSimplexBallHomeomorph n x.val).val,
    (stdSimplexBallHomeomorph_mem_sphere_iff n x.val).mpr x.prop⟩
  invFun y := ⟨(stdSimplexBallHomeomorph n).symm ⟨y.val, sphere_subset_closedBall y.prop⟩,
    (stdSimplexBallHomeomorph_mem_sphere_iff n _).mp (by simp)⟩
  left_inv x := by
    apply Subtype.ext
    exact (stdSimplexBallHomeomorph n).symm_apply_apply x.val
  right_inv y := by
    apply Subtype.ext
    change ((stdSimplexBallHomeomorph n) ((stdSimplexBallHomeomorph n).symm
      ⟨y.val, sphere_subset_closedBall y.prop⟩)).val = y.val
    rw [Homeomorph.apply_symm_apply]
  continuous_toFun := (continuous_subtype_val.comp
    ((stdSimplexBallHomeomorph n).continuous.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := ((stdSimplexBallHomeomorph n).symm.continuous.comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _


@[simp]
theorem stdSimplexBoundarySphereHomeomorph_val (n : ℕ) (x : boundary (Fin (n + 1))) :
    (stdSimplexBoundarySphereHomeomorph n x).val = (stdSimplexBallHomeomorph n x.val).val := rfl


@[simp]
theorem stdSimplexBoundarySphereHomeomorph_symm_val (n : ℕ)
    (y : sphere (0 : Fin n → ℝ) 1) :
    ((stdSimplexBoundarySphereHomeomorph n).symm y).val =
      (stdSimplexBallHomeomorph n).symm ⟨y.val, sphere_subset_closedBall y.prop⟩ := rfl

end Poincare.Simplex

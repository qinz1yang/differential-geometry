import DifferentialGeometry.Topology.Simplex.BallCoordinates

set_option autoImplicit false
noncomputable section
open Set Metric Topology
namespace Poincare.Simplex
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (e : (Fin n → ℝ) ≃L[ℝ] E)

private theorem coordinateBody_interior_nonempty : (interior (e '' coordinateSimplex n)).Nonempty := by
  change (interior (e.toHomeomorph '' coordinateSimplex n)).Nonempty
  rw [← e.toHomeomorph.image_interior]
  exact (interior_coordinateSimplex_nonempty n).image e


def normedSimplexBallAmbientHomeomorph : E ≃ₜ E :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    ((convex_coordinateSimplex n).linear_image e.toLinearMap)
    (coordinateBody_interior_nonempty e)
    ((isCompact_coordinateSimplex n).image e.continuous).isBounded).choose


theorem normedSimplexBallAmbientHomeomorph_image :
    normedSimplexBallAmbientHomeomorph e '' (e '' coordinateSimplex n) = closedBall (0 : E) 1 := by
  have hh := (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    ((convex_coordinateSimplex n).linear_image e.toLinearMap)
    (coordinateBody_interior_nonempty e)
    ((isCompact_coordinateSimplex n).image e.continuous).isBounded).choose_spec.2.1
  change normedSimplexBallAmbientHomeomorph e '' closure (e '' coordinateSimplex n) = closedBall (0 : E) 1 at hh
  rwa [((isCompact_coordinateSimplex n).image e.continuous).isClosed.closure_eq] at hh


theorem normedSimplexBallAmbientHomeomorph_image_frontier :
    normedSimplexBallAmbientHomeomorph e '' frontier (e '' coordinateSimplex n) = sphere (0 : E) 1 :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    ((convex_coordinateSimplex n).linear_image e.toLinearMap)
    (coordinateBody_interior_nonempty e)
    ((isCompact_coordinateSimplex n).image e.continuous).isBounded).choose_spec.2.2


def stdSimplexNormedBallHomeomorph : stdSimplex ℝ (Fin (n + 1)) ≃ₜ closedBall (0 : E) 1 :=
  (stdSimplexCoordinateHomeomorph n).trans
    ((e.toHomeomorph.trans (normedSimplexBallAmbientHomeomorph e)).sets (by
      ext x
      change x ∈ coordinateSimplex n ↔ normedSimplexBallAmbientHomeomorph e (e x) ∈ closedBall (0 : E) 1
      rw [← normedSimplexBallAmbientHomeomorph_image e, (normedSimplexBallAmbientHomeomorph e).injective.mem_set_image,
        e.injective.mem_set_image]))


theorem stdSimplexNormedBallHomeomorph_mem_sphere_iff (x : stdSimplex ℝ (Fin (n + 1))) :
    (stdSimplexNormedBallHomeomorph e x).val ∈ sphere (0 : E) 1 ↔ x ∈ boundary (Fin (n + 1)) := by
  change normedSimplexBallAmbientHomeomorph e (e (stdSimplexCoordinateHomeomorph n x).val) ∈
    sphere (0 : E) 1 ↔ _
  rw [← normedSimplexBallAmbientHomeomorph_image_frontier e, (normedSimplexBallAmbientHomeomorph e).injective.mem_set_image]
  change e.toHomeomorph (stdSimplexCoordinateHomeomorph n x).val ∈ frontier (e.toHomeomorph '' coordinateSimplex n) ↔ _
  rw [← e.toHomeomorph.image_frontier, e.toHomeomorph.injective.mem_set_image,
    mem_frontier_coordinateSimplex_iff]
  simp


def stdSimplexNormedBoundarySphereHomeomorph : boundary (Fin (n + 1)) ≃ₜ sphere (0 : E) 1 where
  toFun x := ⟨(stdSimplexNormedBallHomeomorph e x.val).val,
    (stdSimplexNormedBallHomeomorph_mem_sphere_iff e x.val).mpr x.prop⟩
  invFun y := ⟨(stdSimplexNormedBallHomeomorph e).symm ⟨y.val, sphere_subset_closedBall y.prop⟩,
    (stdSimplexNormedBallHomeomorph_mem_sphere_iff e _).mp (by simp)⟩
  left_inv x := by
    apply Subtype.ext
    exact (stdSimplexNormedBallHomeomorph e).symm_apply_apply x.val
  right_inv y := by
    apply Subtype.ext
    change ((stdSimplexNormedBallHomeomorph e) ((stdSimplexNormedBallHomeomorph e).symm
      ⟨y.val, sphere_subset_closedBall y.prop⟩)).val = y.val
    rw [Homeomorph.apply_symm_apply]
  continuous_toFun := (continuous_subtype_val.comp
    ((stdSimplexNormedBallHomeomorph e).continuous.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := ((stdSimplexNormedBallHomeomorph e).symm.continuous.comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _


@[simp]
theorem stdSimplexNormedBoundarySphereHomeomorph_val (x : boundary (Fin (n + 1))) :
    (stdSimplexNormedBoundarySphereHomeomorph e x).val =
      (stdSimplexNormedBallHomeomorph e x.val).val := rfl

end Poincare.Simplex

import Mathlib.Geometry.Euclidean.Projection

set_option autoImplicit false
noncomputable section

namespace Submodule
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem norm_sub_starProjection_eq_infDist_affine
    (P : Submodule 𝕜 H) [P.HasOrthogonalProjection] (o y : H) :
    ‖(y - o) - P.starProjection (y - o)‖ =
      Metric.infDist y (AffineSubspace.mk' o P : Set H) := by
  let A := AffineSubspace.mk' o P
  have : A.direction.HasOrthogonalProjection := by
    simpa only [A, AffineSubspace.direction_mk'] using (inferInstance : P.HasOrthogonalProjection)
  have h := EuclideanGeometry.dist_orthogonalProjection_eq_infDist A y
  rw [EuclideanGeometry.orthogonalProjection_apply_mem A (AffineSubspace.self_mem_mk' o P)] at h
  simpa only [A, AffineSubspace.direction_mk', vsub_eq_sub, vadd_eq_add,
    Submodule.coe_orthogonalProjectionOnto_apply, dist_eq_norm, sub_add_eq_sub_sub,
    sub_right_comm] using h
end Submodule

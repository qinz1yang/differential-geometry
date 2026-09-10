import DifferentialGeometry.Topology.LocalDegree.SphereSuspension.RadialExtension
import DifferentialGeometry.Topology.LocalDegree.SphereCover

set_option autoImplicit false
open Metric Set
open scoped RealInnerProductSpace
noncomputable section
namespace DifferentialGeometry.LocalDegree
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Submodule ℝ E) [K.HasOrthogonalProjection]


def orthogonalRadialExtension (f : C(sphere (0 : K) 1, sphere (0 : K) 1)) : C(E, E) where
  toFun x := (sphereRadialExtension f (K.orthogonalProjectionOnto x) : E) + Kᗮ.starProjection x
  continuous_toFun :=
    (continuous_subtype_val.comp ((sphereRadialExtension f).continuous.comp
      K.orthogonalProjectionOnto.continuous)).add Kᗮ.starProjection.continuous


@[simp]
theorem orthogonalRadialExtension_norm
    (f : C(sphere (0 : K) 1, sphere (0 : K) 1)) (x : E) :
    ‖orthogonalRadialExtension K f x‖ = ‖x‖ := by
  have hi : ⟪(sphereRadialExtension f (K.orthogonalProjectionOnto x) : E),
      Kᗮ.starProjection x⟫ = 0 :=
    (K.mem_orthogonal _).mp (Kᗮ.starProjection_apply_mem x) _ (Subtype.coe_prop _)
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi
  simp only [← sq] at hn
  change ‖orthogonalRadialExtension K f x‖ ^ 2 =
    ‖sphereRadialExtension f (K.orthogonalProjectionOnto x)‖ ^ 2 +
      ‖Kᗮ.orthogonalProjectionOnto x‖ ^ 2 at hn
  rw [sphereRadialExtension_norm, ← Submodule.norm_sq_eq_add_norm_sq_projection] at hn
  nlinarith [norm_nonneg (orthogonalRadialExtension K f x), norm_nonneg x]


@[simp]
theorem orthogonalRadialExtension_projection
    (f : C(sphere (0 : K) 1, sphere (0 : K) 1)) (x : E) :
    K.orthogonalProjectionOnto (orthogonalRadialExtension K f x) =
      sphereRadialExtension f (K.orthogonalProjectionOnto x) := by
  change K.orthogonalProjectionOnto (_ + _) = _
  rw [map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (Kᗮ.starProjection_apply_mem x), add_zero]


theorem orthogonalRadialExtension_orthogonalProjection
    (f : C(sphere (0 : K) 1, sphere (0 : K) 1)) (x : E) :
    Kᗮ.starProjection (orthogonalRadialExtension K f x) = Kᗮ.starProjection x := by
  rw [Submodule.starProjection_orthogonal_val]
  change ((sphereRadialExtension f (K.orthogonalProjectionOnto x) : E) + Kᗮ.starProjection x) -
    (K.orthogonalProjectionOnto (orthogonalRadialExtension K f x) : E) = _
  rw [orthogonalRadialExtension_projection, add_sub_cancel_left]


@[simp]
theorem orthogonalRadialExtension_of_mem_orthogonal
    (f : C(sphere (0 : K) 1, sphere (0 : K) 1)) {x : E} (hx : x ∈ Kᗮ) :
    orthogonalRadialExtension K f x = x := by
  change (sphereRadialExtension f (K.orthogonalProjectionOnto x) : E) + Kᗮ.starProjection x = x
  rw [Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hx,
    sphereRadialExtension_zero, Submodule.coe_zero, zero_add,
    (Kᗮ.starProjection_eq_self_iff).mpr hx]


theorem orthogonalRadialExtension_eq_of_mem_orthogonal_iff
    (f : C(sphere (0 : K) 1, sphere (0 : K) 1)) {x z : E} (hz : z ∈ Kᗮ) :
    orthogonalRadialExtension K f x = z ↔ x = z := by
  constructor
  · intro h
    have hp := congrArg K.orthogonalProjectionOnto h
    rw [orthogonalRadialExtension_projection,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hz] at hp
    have hn := congrArg norm hp
    rw [sphereRadialExtension_norm, norm_zero, norm_eq_zero] at hn
    have hx : x ∈ Kᗮ := (K.orthogonalProjectionOnto_eq_zero_iff).mp hn
    rwa [orthogonalRadialExtension_of_mem_orthogonal K f hx] at h
  · intro h
    rw [h]
    exact orthogonalRadialExtension_of_mem_orthogonal K f hz


def orthogonalSphereSuspension (f : C(sphere (0 : K) 1, sphere (0 : K) 1)) :
    C(sphere (0 : E) 1, sphere (0 : E) 1) := by
  let g : C(E, E) := orthogonalRadialExtension K f
  have hg : ∀ x : sphere (0 : E) 1, g x ∈ sphere (0 : E) 1 := by
    intro x
    rw [mem_sphere, dist_zero_right]
    exact (orthogonalRadialExtension_norm K f x).trans (norm_eq_of_mem_sphere x)
  exact ⟨fun x ↦ ⟨g x, hg x⟩,
    (g.continuous.comp continuous_subtype_val).subtype_mk hg⟩


@[simp]
theorem orthogonalSphereSuspension_apply
    (f : C(sphere (0 : K) 1, sphere (0 : K) 1)) (x : sphere (0 : E) 1) :
    (orthogonalSphereSuspension K f x : E) =
      (sphereRadialExtension f (K.orthogonalProjectionOnto x) : E) + Kᗮ.starProjection x := rfl


theorem orthogonalRadialExtension_sphere
    (f : C(sphere (0 : K) 1, sphere (0 : K) 1)) (v : sphere (0 : K) 1) :
    orthogonalRadialExtension K f (v.val : E) = (f v).val := by
  change (sphereRadialExtension f (K.orthogonalProjectionOnto v.val) : E) +
    Kᗮ.starProjection v.val = _
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    sphereRadialExtension_sphere, Submodule.starProjection_orthogonal_apply_eq_zero v.val.property,
    add_zero]


def equatorSphereSuspension (v : sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) : C(sphere (0 : E) 1, sphere (0 : E) 1) :=
  orthogonalSphereSuspension (ℝ ∙ (v : E))ᗮ f

private theorem pole_mem_doubleOrthogonal (v : sphere (0 : E) 1) :
    (v : E) ∈ (ℝ ∙ (v : E))ᗮᗮ :=
  (ℝ ∙ (v : E)).le_orthogonal_orthogonal (Submodule.mem_span_singleton_self _)


@[simp]
theorem equatorSphereSuspension_eq_north_iff (v : sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) (x : sphere (0 : E) 1) :
    equatorSphereSuspension v f x = v ↔ x = v := by
  rw [Subtype.ext_iff, Subtype.ext_iff]
  exact orthogonalRadialExtension_eq_of_mem_orthogonal_iff _ f (pole_mem_doubleOrthogonal v)


@[simp]
theorem equatorSphereSuspension_eq_south_iff (v : sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) (x : sphere (0 : E) 1) :
    equatorSphereSuspension v f x = -v ↔ x = -v := by
  rw [Subtype.ext_iff, Subtype.ext_iff]
  exact orthogonalRadialExtension_eq_of_mem_orthogonal_iff _ f
    ((ℝ ∙ (v : E))ᗮᗮ.neg_mem (pole_mem_doubleOrthogonal v))


theorem equatorSphereSuspension_height (v : sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) (x : sphere (0 : E) 1) :
    ⟪(v : E), (equatorSphereSuspension v f x : E)⟫ = ⟪(v : E), (x : E)⟫ := by
  let K : Submodule ℝ E := (ℝ ∙ (v : E))ᗮ
  have hv : Kᗮ.starProjection (v : E) = v :=
    Kᗮ.starProjection_eq_self_iff.mpr (pole_mem_doubleOrthogonal v)
  calc
    _ = ⟪Kᗮ.starProjection (v : E), (equatorSphereSuspension v f x : E)⟫ := by rw [hv]
    _ = ⟪(v : E), Kᗮ.starProjection (equatorSphereSuspension v f x : E)⟫ :=
      Submodule.inner_starProjection_left_eq_right Kᗮ _ _
    _ = ⟪(v : E), Kᗮ.starProjection (x : E)⟫ := by
      change ⟪(v : E), Kᗮ.starProjection (orthogonalRadialExtension K f x)⟫ = _
      rw [orthogonalRadialExtension_orthogonalProjection]
    _ = ⟪Kᗮ.starProjection (v : E), (x : E)⟫ :=
      (Submodule.inner_starProjection_left_eq_right Kᗮ _ _).symm
    _ = _ := by rw [hv]

end DifferentialGeometry.LocalDegree

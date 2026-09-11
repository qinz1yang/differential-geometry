import DifferentialGeometry.Topology.LocalDegree.IsolatedZero
import DifferentialGeometry.Topology.LocalDegree.SphereSuspension.Geometry

set_option autoImplicit false
open Metric Set
open scoped Topology unitInterval
noncomputable section
namespace DifferentialGeometry.LocalDegree
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Submodule ℝ E) [K.HasOrthogonalProjection]


def orthogonalProductField (F : K → K) (x : E) : E :=
  (F (K.orthogonalProjectionOnto x) : E) + Kᗮ.starProjection x


@[simp]
theorem orthogonalProductField_projection (F : K → K) (x : E) :
    K.orthogonalProjectionOnto (orthogonalProductField K F x) = F (K.orthogonalProjectionOnto x) := by
  change K.orthogonalProjectionOnto (_ + _) = _
  rw [map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (Kᗮ.starProjection_apply_mem x), add_zero]


theorem orthogonalProductField_orthogonalProjection (F : K → K) (x : E) :
    Kᗮ.starProjection (orthogonalProductField K F x) = Kᗮ.starProjection x := by
  rw [Submodule.starProjection_orthogonal_val]
  change ((F (K.orthogonalProjectionOnto x) : E) + Kᗮ.starProjection x) -
    (K.orthogonalProjectionOnto (orthogonalProductField K F x) : E) = _
  rw [orthogonalProductField_projection, add_sub_cancel_left]

private theorem projection_closedBall {R : ℝ} :
    MapsTo K.orthogonalProjectionOnto (closedBall (0 : E) R) (closedBall (0 : K) R) := by
  intro x hx
  rw [mem_closedBall, dist_zero_right] at hx ⊢
  exact (K.norm_orthogonalProjectionOnto_apply_le x).trans hx


theorem IsolatingRadius.orthogonalProduct {F : K → K} {R : ℝ} (h : IsolatingRadius F 0 R) :
    IsolatingRadius (orthogonalProductField K F) 0 R where
  pos := h.pos
  continuousOn :=
    (continuous_subtype_val.comp_continuousOn
      (h.continuousOn.comp K.orthogonalProjectionOnto.continuous.continuousOn
        (projection_closedBall K))).add Kᗮ.starProjection.continuous.continuousOn
  zero_iff x hx := by
    constructor
    · intro hz
      have hp := congrArg K.orthogonalProjectionOnto hz
      rw [orthogonalProductField_projection, map_zero,
        h.zero_iff _ (projection_closedBall K hx)] at hp
      have hq := congrArg Kᗮ.starProjection hz
      rw [orthogonalProductField_orthogonalProjection, map_zero] at hq
      have hd := K.starProjection_add_starProjection_orthogonal x
      rw [Submodule.starProjection_apply, hp, Submodule.coe_zero, hq, add_zero] at hd
      exact hd.symm
    · intro hx
      subst x
      simp [orthogonalProductField, h.zero]

private theorem sphere_scaled_mem {R : ℝ} (r : Ioc (0 : ℝ) R) (v : sphere (0 : E) 1) :
    (r : ℝ) • (v : E) ∈ closedBall (0 : E) R := by
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg r.property.1.le,
    norm_eq_of_mem_sphere v, mul_one]
  exact r.property.2


def orthogonalProductInterpolation {F : K → K} {R : ℝ} (h : IsolatingRadius F 0 R)
    (r : Ioc (0 : ℝ) R) : C(I × sphere (0 : E) 1, E) where
  toFun p := (1 - (p.1 : ℝ)) • orthogonalProductField K F ((r : ℝ) • (p.2 : E)) +
    (p.1 : ℝ) • ((r : ℝ) • (orthogonalSphereSuspension K
      (sphereMap F 0 R h.continuousOn h.nonzero r) p.2 : E))
  continuous_toFun := by
    have hp : Continuous (fun v : sphere (0 : E) 1 ↦
        orthogonalProductField K F ((r : ℝ) • (v : E))) :=
      (h.orthogonalProduct K).continuousOn.comp_continuous
        (continuous_const.smul continuous_subtype_val) (sphere_scaled_mem r)
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (hp.comp continuous_snd) |>.add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_const.smul (continuous_subtype_val.comp
          ((orthogonalSphereSuspension K (sphereMap F 0 R h.continuousOn h.nonzero r)).continuous.comp
            continuous_snd))))


theorem orthogonalProductInterpolation_orthogonalProjection {F : K → K} {R : ℝ}
    (h : IsolatingRadius F 0 R) (r : Ioc (0 : ℝ) R) (t : I) (x : sphere (0 : E) 1) :
    Kᗮ.starProjection (orthogonalProductInterpolation K h r (t, x)) =
      (r : ℝ) • Kᗮ.starProjection (x : E) := by
  change Kᗮ.starProjection ((1 - (t : ℝ)) • orthogonalProductField K F ((r : ℝ) • (x : E)) +
    (t : ℝ) • ((r : ℝ) • orthogonalRadialExtension K
      (sphereMap F 0 R h.continuousOn h.nonzero r) x)) = _
  rw [map_add, map_smul, map_smul, map_smul, orthogonalProductField_orthogonalProjection,
    map_smul, orthogonalRadialExtension_orthogonalProjection, ← add_smul,
    sub_add_cancel, one_smul]


theorem orthogonalProductInterpolation_equator {F : K → K} {R : ℝ}
    (h : IsolatingRadius F 0 R) (r : Ioc (0 : ℝ) R) (t : I)
    (u : sphere (0 : K) 1) (x : sphere (0 : E) 1) (hx : (x : E) = (u.val : E)) :
    orthogonalProductInterpolation K h r (t, x) =
      ((1 - (t : ℝ)) + (t : ℝ) * (r : ℝ) * ‖F ((r : ℝ) • u.val)‖⁻¹) •
        (F ((r : ℝ) • u.val) : E) := by
  change (1 - (t : ℝ)) • orthogonalProductField K F ((r : ℝ) • (x : E)) +
    (t : ℝ) • ((r : ℝ) • orthogonalRadialExtension K
      (sphereMap F 0 R h.continuousOn h.nonzero r) x) = _
  rw [hx, orthogonalRadialExtension_sphere]
  simp only [orthogonalProductField, map_smul,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.starProjection_orthogonal_apply_eq_zero u.val.property,
    smul_zero, add_zero, sphereMap_apply, zero_add, Submodule.coe_smul_of_tower,
    smul_smul, add_smul, mul_assoc]


theorem orthogonalProductInterpolation_ne_zero {F : K → K} {R : ℝ}
    (h : IsolatingRadius F 0 R) (r : Ioc (0 : ℝ) R) (p : I × sphere (0 : E) 1) :
    orthogonalProductInterpolation K h r p ≠ 0 := by
  intro hz
  have hq := congrArg Kᗮ.starProjection hz
  rw [orthogonalProductInterpolation_orthogonalProjection, map_zero] at hq
  have hxq : Kᗮ.starProjection (p.2 : E) = 0 :=
    (smul_eq_zero.mp hq).resolve_left r.property.1.ne'
  have hd := K.starProjection_add_starProjection_orthogonal (p.2 : E)
  rw [hxq, add_zero] at hd
  have hxK : (p.2 : E) ∈ K := hd ▸ K.starProjection_apply_mem (p.2 : E)
  let u : sphere (0 : K) 1 := ⟨⟨p.2.val, hxK⟩, p.2.property⟩
  have hF : F ((r : ℝ) • u.val) ≠ 0 :=
    h.nonzero _ (sphere_scaled_mem r u)
      (smul_ne_zero r.property.1.ne' (ne_zero_of_mem_unit_sphere u))
  have ha : 0 < ((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (r : ℝ) * ‖F ((r : ℝ) • u.val)‖⁻¹) := by
    have hn : 0 < ‖F ((r : ℝ) • u.val)‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hF)
    by_cases ht : (p.1 : ℝ) = 0
    · simp [ht]
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr p.1.property.2)
        (mul_pos (mul_pos (lt_of_le_of_ne p.1.property.1 (Ne.symm ht)) r.property.1) hn)
  rw [orthogonalProductInterpolation_equator K h r p.1 u p.2 rfl] at hz
  have he : (F ((r : ℝ) • u.val) : E) = 0 := (smul_eq_zero.mp hz).resolve_left ha.ne'
  exact hF (Subtype.ext he)


def orthogonalProductSphereHomotopy {F : K → K} {R : ℝ}
    (h : IsolatingRadius F 0 R) (r : Ioc (0 : ℝ) R) :
    (sphereMap (orthogonalProductField K F) 0 R (h.orthogonalProduct K).continuousOn
      (h.orthogonalProduct K).nonzero r).Homotopy
        (orthogonalSphereSuspension K (sphereMap F 0 R h.continuousOn h.nonzero r)) where
  toFun p := (homeomorphUnitSphereProd E
    ⟨orthogonalProductInterpolation K h r p, orthogonalProductInterpolation_ne_zero K h r p⟩).1
  continuous_toFun := (homeomorphUnitSphereProd E).continuous.fst.comp
    ((orthogonalProductInterpolation K h r).continuous.subtype_mk
      (orthogonalProductInterpolation_ne_zero K h r))
  map_zero_left x := by
    apply Subtype.ext
    rw [homeomorphUnitSphereProd_apply_fst_coe, sphereMap_apply]
    change ‖(1 - (0 : ℝ)) • orthogonalProductField K F ((r : ℝ) • (x : E)) +
      (0 : ℝ) • ((r : ℝ) • _)‖⁻¹ •
      ((1 - (0 : ℝ)) • orthogonalProductField K F ((r : ℝ) • (x : E)) +
        (0 : ℝ) • ((r : ℝ) • _)) = _
    simp
  map_one_left x := by
    apply Subtype.ext
    rw [homeomorphUnitSphereProd_apply_fst_coe]
    change ‖(1 - (1 : ℝ)) • orthogonalProductField K F ((r : ℝ) • (x : E)) +
      (1 : ℝ) • ((r : ℝ) • (orthogonalSphereSuspension K
        (sphereMap F 0 R h.continuousOn h.nonzero r) x : E))‖⁻¹ •
      ((1 - (1 : ℝ)) • orthogonalProductField K F ((r : ℝ) • (x : E)) +
        (1 : ℝ) • ((r : ℝ) • (orthogonalSphereSuspension K
          (sphereMap F 0 R h.continuousOn h.nonzero r) x : E))) = _
    simp only [sub_self, zero_smul, zero_add, smul_smul, one_mul, norm_smul,
      Real.norm_of_nonneg r.property.1.le, norm_eq_of_mem_sphere, mul_one,
      inv_mul_cancel₀ r.property.1.ne', one_smul]


@[simp]
theorem orthogonalProductSphereHomotopy_apply {F : K → K} {R : ℝ}
    (h : IsolatingRadius F 0 R) (r : Ioc (0 : ℝ) R) (p : I × sphere (0 : E) 1) :
    (orthogonalProductSphereHomotopy K h r p : E) =
      ‖orthogonalProductInterpolation K h r p‖⁻¹ • orthogonalProductInterpolation K h r p :=
  homeomorphUnitSphereProd_apply_fst_coe E _

end DifferentialGeometry.LocalDegree

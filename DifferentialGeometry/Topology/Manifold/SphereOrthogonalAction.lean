import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

noncomputable section

open Manifold Set Metric Module
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

noncomputable def sphereMap (e : E ≃ₗᵢ[ℝ] E) :
    sphere (0 : E) 1 → sphere (0 : E) 1 :=
  Set.codRestrict (fun x : sphere (0 : E) 1 => (e (x : E) : E)) (sphere (0 : E) 1)
    (fun x => by
      rw [mem_sphere_zero_iff_norm, e.norm_map]
      exact mem_sphere_zero_iff_norm.mp x.2)

omit [FiniteDimensional ℝ E] in
@[simp] theorem sphereMap_coe (e : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1) :
    (sphereMap e x : E) = e (x : E) := rfl

theorem sphereMap_contMDiff (e : E ≃ₗᵢ[ℝ] E) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (sphereMap e) :=
  ContMDiff.codRestrict_sphere
    (e.toContinuousLinearMap.contMDiff.comp contMDiff_coe_sphere) _

noncomputable def sphereDiffeo (e : E ≃ₗᵢ[ℝ] E) :
    sphere (0 : E) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : E) 1 where
  toFun := sphereMap e
  invFun := sphereMap e.symm
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  contMDiff_toFun := sphereMap_contMDiff (n := n) e
  contMDiff_invFun := sphereMap_contMDiff (n := n) e.symm

@[simp] theorem sphereDiffeo_coe (e : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1) :
    ((sphereDiffeo (n := n) e x : sphere (0 : E) 1) : E) = e (x : E) := rfl

theorem sphereDiffeo_inj :
    Function.Injective (sphereDiffeo (E := E) (n := n)) := by
  intro e f hef
  apply LinearIsometryEquiv.ext
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  let y : sphere (0 : E) 1 :=
    ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere_zero_iff_norm, norm_smul]
      simp [hx]⟩
  have hxy : ‖x‖ • (y : E) = x := by
    dsimp [y]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  have hpoint :
      sphereDiffeo (n := n) e y = sphereDiffeo (n := n) f y := by
    rw [hef]
  have hamb : e (y : E) = f (y : E) := by
    simpa only [sphereDiffeo_coe] using congrArg Subtype.val hpoint
  calc
    e x = e (‖x‖ • (y : E)) := congrArg e hxy.symm
    _ = ‖x‖ • e (y : E) := map_smul e ‖x‖ (y : E)
    _ = ‖x‖ • f (y : E) := congrArg (fun z : E => ‖x‖ • z) hamb
    _ = f (‖x‖ • (y : E)) := (map_smul f ‖x‖ (y : E)).symm
    _ = f x := congrArg f hxy

end DifferentialGeometry.Geometry

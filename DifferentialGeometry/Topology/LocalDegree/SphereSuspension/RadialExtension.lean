import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

set_option autoImplicit false
open Metric Set
noncomputable section
namespace DifferentialGeometry.LocalDegree
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private def radialExtensionFun (f : C(sphere (0 : E) 1, sphere (0 : F) 1)) (x : E) : F := by
  classical
  exact if hx : x = 0 then 0 else
    ‖x‖ • (f ((homeomorphUnitSphereProd E) ⟨x, hx⟩).1 : F)

private theorem radialExtensionFun_zero (f : C(sphere (0 : E) 1, sphere (0 : F) 1)) :
    radialExtensionFun f 0 = 0 := by simp [radialExtensionFun]

private theorem radialExtensionFun_norm (f : C(sphere (0 : E) 1, sphere (0 : F) 1)) (x : E) :
    ‖radialExtensionFun f x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [radialExtensionFun, hx]
  · simp [radialExtensionFun, hx, norm_smul, norm_eq_of_mem_sphere]

private theorem continuous_radialExtensionFun (f : C(sphere (0 : E) 1, sphere (0 : F) 1)) :
    Continuous (radialExtensionFun f) := by
  have hc : ContinuousOn (radialExtensionFun f) ({0}ᶜ : Set E) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : ({0}ᶜ : Set E).domRestrict (radialExtensionFun f) =
        fun x : ({0}ᶜ : Set E) ↦ ‖x.val‖ • (f ((homeomorphUnitSphereProd E) x).1 : F) := by
      funext x
      exact dif_neg (show x.val ≠ 0 from x.property)
    rw [heq]
    exact (continuous_norm.comp continuous_subtype_val).smul
      (continuous_subtype_val.comp (f.continuous.comp (homeomorphUnitSphereProd E).continuous.fst))
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [ContinuousAt, radialExtensionFun_zero, tendsto_zero_iff_norm_tendsto_zero]
    simpa only [ContinuousAt, radialExtensionFun_norm, norm_zero] using (continuous_norm.continuousAt (x := (0 : E)))
  · exact hc.continuousAt (isOpen_compl_singleton.mem_nhds hx)


def sphereRadialExtension (f : C(sphere (0 : E) 1, sphere (0 : F) 1)) : C(E, F) :=
  ⟨radialExtensionFun f, continuous_radialExtensionFun f⟩


@[simp]
theorem sphereRadialExtension_zero (f : C(sphere (0 : E) 1, sphere (0 : F) 1)) :
    sphereRadialExtension f 0 = 0 := radialExtensionFun_zero f


@[simp]
theorem sphereRadialExtension_norm (f : C(sphere (0 : E) 1, sphere (0 : F) 1)) (x : E) :
    ‖sphereRadialExtension f x‖ = ‖x‖ := radialExtensionFun_norm f x


theorem sphereRadialExtension_apply_of_ne_zero (f : C(sphere (0 : E) 1, sphere (0 : F) 1))
    {x : E} (hx : x ≠ 0) :
    sphereRadialExtension f x = ‖x‖ • (f ((homeomorphUnitSphereProd E) ⟨x, hx⟩).1 : F) :=
  dif_neg hx


@[simp]
theorem sphereRadialExtension_sphere (f : C(sphere (0 : E) 1, sphere (0 : F) 1))
    (v : sphere (0 : E) 1) : sphereRadialExtension f v = f v := by
  rw [sphereRadialExtension_apply_of_ne_zero f (ne_zero_of_mem_unit_sphere v),
    norm_eq_of_mem_sphere v, one_smul]
  congr 2
  apply Subtype.ext
  rw [homeomorphUnitSphereProd_apply_fst_coe, norm_eq_of_mem_sphere v]
  simp
end DifferentialGeometry.LocalDegree

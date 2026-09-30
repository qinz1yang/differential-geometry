import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Metric
open scoped Real

namespace ContinuousMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem intervalIntegrable_circle (c : ℂ) (r : ℝ) (f : C(sphere c |r|, E)) :
    IntervalIntegrable (fun θ : ℝ => deriv (circleMap c r) θ •
      f ⟨circleMap c r θ, circleMap_mem_sphere' c r θ⟩) volume 0 (2 * Real.pi) := by
  apply Continuous.intervalIntegrable
  have hf : Continuous (fun θ : ℝ => f ⟨circleMap c r θ, circleMap_mem_sphere' c r θ⟩) :=
    f.continuous.comp ((continuous_circleMap c r).subtype_mk _)
  have hd : Continuous (deriv (circleMap c r)) := by
    rw [funext (deriv_circleMap c r)]
    fun_prop
  exact hd.smul hf

def circleIntegralCLM (c : ℂ) (r : ℝ) : C(sphere c |r|, E) →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ θ : ℝ in 0..2 * Real.pi, deriv (circleMap c r) θ •
        f ⟨circleMap c r θ, circleMap_mem_sphere' c r θ⟩
      map_add' := fun f g => by
        simp only [add_apply, smul_add]
        exact intervalIntegral.integral_add (intervalIntegrable_circle c r f)
          (intervalIntegrable_circle c r g)
      map_smul' := fun z f => by
        simp only [smul_apply, smul_comm (deriv (circleMap c r) _),
          intervalIntegral.integral_smul, RingHom.id_apply] }
    (2 * Real.pi * |r|) (fun f => by
      calc
        ‖∫ θ : ℝ in 0..2 * Real.pi, deriv (circleMap c r) θ •
            f ⟨circleMap c r θ, circleMap_mem_sphere' c r θ⟩‖ ≤
            |r| * ‖f‖ * |2 * Real.pi - 0| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro θ _
          simp only [norm_smul]
          rw [show ‖deriv (circleMap c r) θ‖ = |r| by simp]
          exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (abs_nonneg r)
        _ = (2 * Real.pi * |r|) * ‖f‖ := by
          rw [sub_zero, abs_of_pos Real.two_pi_pos]
          ring)

theorem circleIntegralCLM_apply (c : ℂ) (r : ℝ) {f : ℂ → E}
    (hf : ContinuousOn f (sphere c |r|)) :
    circleIntegralCLM c r ⟨fun z => f z, hf.domRestrict⟩ = ∮ z in C(c, r), f z := rfl

theorem norm_circleIntegralCLM_le (c : ℂ) (r : ℝ) :
    ‖circleIntegralCLM (E := E) c r‖ ≤ 2 * Real.pi * |r| :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end ContinuousMap

import DifferentialGeometry.Topology.Embedding.CylinderCap
import DifferentialGeometry.Topology.Morse.CriticalPoints

open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Morse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem isCriticalPointAt_cylinderCap_snd_iff {a : ℝ} (ha : a ≠ 0) (x : E) :
    IsCriticalPointAt 𝓘(ℝ, E) (fun y : E => (EuclideanGeometry.cylinderCap a y).2) x ↔ x = 0 := by
  rw [IsCriticalPointAt, mfderiv_eq_fderiv]
  exact EuclideanGeometry.fderiv_cylinderCap_snd_eq_zero_iff ha x

theorem isNondegenerateCriticalPointAt_cylinderCap_snd {a : ℝ} (ha : a ≠ 0) :
    IsNondegenerateCriticalPointAt 𝓘(ℝ, E)
      (fun y : E => (EuclideanGeometry.cylinderCap a y).2) 0 := by
  have hf : ContDiff ℝ 2 (fun y : E => (EuclideanGeometry.cylinderCap a y).2) :=
    contDiff_const.mul ((contDiff_norm_sq ℝ).sub contDiff_const)
  apply (isNondegenerateCriticalPointAt_model_iff hf.contDiffAt).mpr
  refine ⟨(EuclideanGeometry.fderiv_cylinderCap_snd_eq_zero_iff ha 0).mpr rfl, ?_⟩
  rw [EuclideanGeometry.fderiv_fderiv_cylinderCap_snd]
  intro x y h
  have he : innerSL ℝ x = innerSL ℝ y :=
    (smul_right_injective (E →L[ℝ] ℝ) (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) ha)) h
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← innerSL_apply_norm ℝ, map_sub, he, sub_self, norm_zero]

end DifferentialGeometry.Topology.Morse

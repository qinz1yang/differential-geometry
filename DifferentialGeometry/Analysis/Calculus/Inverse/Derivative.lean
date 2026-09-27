import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse

section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace OpenPartialHomeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_comp_symm_eq_id
    (e : OpenPartialHomeomorph E F) {z : F} (hz : z ∈ e.target)
    (he : DifferentiableAt ℝ e (e.symm z)) (hi : DifferentiableAt ℝ e.symm z) :
    (fderiv ℝ e (e.symm z)).comp (fderiv ℝ e.symm z) = ContinuousLinearMap.id ℝ F := by
  have hh := (he.hasFDerivAt.comp z hi.hasFDerivAt).fderiv
  have heq : (fun w => e (e.symm w)) =ᶠ[𝓝 z] id := e.eventually_right_inverse hz
  have hd := heq.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (fun w => e (e.symm w)) z = _ at hh
  rw [hh] at hd
  exact hd.trans fderiv_id

theorem fderiv_ne_zero_of_differentiable_symm [Nontrivial F]
    (e : OpenPartialHomeomorph E F) {z : F} (hz : z ∈ e.target)
    (he : DifferentiableAt ℝ e (e.symm z)) (hi : DifferentiableAt ℝ e.symm z) :
    fderiv ℝ e (e.symm z) ≠ 0 := by
  intro hzero
  have hh := e.fderiv_comp_symm_eq_id hz he hi
  rw [hzero, ContinuousLinearMap.zero_comp] at hh
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  have hc := congrArg (fun L : F →L[ℝ] F => L v) hh
  exact hv hc.symm

end OpenPartialHomeomorph

end

end

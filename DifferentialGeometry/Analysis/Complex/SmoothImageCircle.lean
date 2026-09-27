import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.CircleIntegral

section

noncomputable section

open Set Metric
open scoped ContDiff

namespace Complex

theorem exists_regular_parametrization_image_circle
    (W : OpenPartialHomeomorph ℂ ℂ)
    (hsource : sphere (0 : ℂ) 1 ⊆ W.source)
    (hW : ContDiffOn ℝ ∞ W W.source) (hWi : DifferentiableOn ℝ W.symm W.target) :
    ∃ γ : AddCircle (2 * Real.pi) → ℂ,
      Topology.IsEmbedding γ ∧
      ContDiff ℝ ∞ (fun t : ℝ => γ (t : AddCircle (2 * Real.pi))) ∧
      (∀ θ : ℝ, deriv (fun t : ℝ => γ (t : AddCircle (2 * Real.pi))) θ ≠ 0) ∧
      range γ = W '' sphere (0 : ℂ) 1 := by
  let γ : AddCircle (2 * Real.pi) → ℂ := fun θ => W (AddCircle.homeomorphCircle' θ)
  let J := W.homeomorphOfImageSubsetSource hsource rfl
  have hemb : Topology.IsEmbedding γ :=
    Topology.IsEmbedding.subtypeVal.comp (J.isEmbedding.comp
      AddCircle.homeomorphCircle'.isEmbedding)
  have heq : (fun t : ℝ => γ (t : AddCircle (2 * Real.pi))) = W ∘ circleMap 0 1 := by
    ext t
    simp only [γ, AddCircle.homeomorphCircle'_apply_mk, Circle.coe_exp, circleMap,
      ofReal_one, one_mul, zero_add, Function.comp_apply]
  have hcircle (t : ℝ) : circleMap 0 1 t ∈ W.source :=
    hsource (circleMap_mem_sphere 0 zero_le_one t)
  have hsmooth : ContDiff ℝ ∞ (fun t : ℝ => γ (t : AddCircle (2 * Real.pi))) := by
    rw [heq]
    exact hW.comp_contDiff (contDiff_circleMap 0 1) hcircle
  refine ⟨γ, hemb, hsmooth, ?_, ?_⟩
  · intro θ hzero
    have hvalue : γ (θ : AddCircle (2 * Real.pi)) = W (circleMap 0 1 θ) := congrFun heq θ
    have hinv : DifferentiableAt ℝ W.symm (γ (θ : AddCircle (2 * Real.pi))) := by
      rw [hvalue]
      exact (hWi _ (W.map_source (hcircle θ))).differentiableAt
        (W.open_target.mem_nhds (W.map_source (hcircle θ)))
    have hcomp := hinv.hasFDerivAt.comp_hasDerivAt θ
      (hsmooth.differentiable (by simp)).differentiableAt.hasDerivAt
    have hleft : (fun t : ℝ => W.symm (γ (t : AddCircle (2 * Real.pi)))) = circleMap 0 1 := by
      ext t
      rw [congrFun heq t]
      exact W.left_inv (hcircle t)
    have hderiv : deriv (circleMap 0 1) θ =
        (fderiv ℝ W.symm (γ (θ : AddCircle (2 * Real.pi))))
          (deriv (fun t : ℝ => γ (t : AddCircle (2 * Real.pi))) θ) := by
      have hh := hcomp.deriv
      simpa only [Function.comp_def, hleft] using hh
    rw [hzero, map_zero] at hderiv
    exact deriv_circleMap_ne_zero one_ne_zero hderiv
  · ext z
    constructor
    · rintro ⟨θ, rfl⟩
      exact ⟨AddCircle.homeomorphCircle' θ, (AddCircle.homeomorphCircle' θ).2, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨θ, hθ⟩ := AddCircle.homeomorphCircle'.surjective ⟨w, hw⟩
      refine ⟨θ, ?_⟩
      change W (AddCircle.homeomorphCircle' θ) = W w
      rw [hθ]

end Complex

end

end

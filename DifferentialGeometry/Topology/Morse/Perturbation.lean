import DifferentialGeometry.Analysis.Calculus.Sard
import DifferentialGeometry.Topology.Morse.CriticalPoints

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem dense_linear_perturbations_isNondegenerateCriticalPointAt
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Dense {a : E →L[ℝ] ℝ | ∀ x : E,
      IsCriticalPointAt 𝓘(ℝ, E) (fun z => f z - a z) x →
        IsNondegenerateCriticalPointAt 𝓘(ℝ, E) (fun z => f z - a z) x} := by
  have hfder : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) :=
    Subspace.dual_finrank_eq.symm.trans LinearMap.toContinuousLinearMap.finrank_eq
  have hdense := Differentiable.dense_regular_values_of_finrank_eq
    (hfder.differentiable (by norm_num)) hdim
  apply hdense.mono
  intro a ha x hx
  have hdiff (z : E) : fderiv ℝ (fun z => f z - a z) z = fderiv ℝ f z - a :=
    ((hf.differentiable (by norm_num) z).hasFDerivAt.sub a.hasFDerivAt).fderiv
  have hdiffFun : fderiv ℝ (fun z => f z - a z) = fun z => fderiv ℝ f z - a :=
    funext hdiff
  have hx' : fderiv ℝ (fun z => f z - a z) x = 0 := by
    unfold IsCriticalPointAt at hx
    rw [mfderiv_eq_fderiv] at hx
    exact hx
  apply (isNondegenerateCriticalPointAt_model_iff (hf.sub a.contDiff).contDiffAt).mpr
  refine ⟨hx', ?_⟩
  have hfx : fderiv ℝ f x = a := sub_eq_zero.mp ((hdiff x).symm.trans hx')
  rw [hdiffFun, fderiv_sub_const]
  exact (ha x hfx).1

theorem exists_small_linear_perturbation_isNondegenerateCriticalPointAt
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : E →L[ℝ] ℝ, ‖a‖ < ε ∧ ∀ x : E,
      IsCriticalPointAt 𝓘(ℝ, E) (fun z => f z - a z) x →
        IsNondegenerateCriticalPointAt 𝓘(ℝ, E) (fun z => f z - a z) x := by
  obtain ⟨a, ha, hanorm⟩ :=
    (dense_linear_perturbations_isNondegenerateCriticalPointAt hf).exists_dist_lt 0 hε
  exact ⟨a, by simpa using hanorm, ha⟩

end DifferentialGeometry.Topology.Morse

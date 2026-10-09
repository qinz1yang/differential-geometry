import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Normed.Operator.Basic

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

variable {E F H Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem retained_projection_cutoff_adjustment (K : H →L[ℝ] Z) (J : F →L[ℝ] H)
    (hKJ : K.comp J = 0) (ψ : H → ℝ) (v : H → F) :
    (fun x => K (x + ψ x • J (v x))) = K := by
  funext x
  have hh : K (J (v x)) = 0 := congrArg (fun A : F →L[ℝ] Z => A (v x)) hKJ
  simp [hh]

theorem factor_projection_cutoff_adjustment (R : H →L[ℝ] E)
    (Q : H →L[ℝ] F) (L : E →L[ℝ] F) (J : F →L[ℝ] H)
    (hQ : Q = L.comp R) (ψ : H → ℝ) (φ : E → ℝ) (hψ : ψ = φ ∘ R) (P : F → F) :
    (fun x => R (x + ψ x • J (P (Q x) - Q x))) =
      (fun y => y + φ y • (R.comp J) (P (L y) - L y)) ∘ R := by
  funext x
  simp [hQ, hψ]

theorem ker_fderiv_le_ker_postcomp {f : E → F} {g : F → H} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x)) :
    (fderiv ℝ f x).ker ≤ (fderiv ℝ (g ∘ f) x).ker := by
  rw [fderiv_comp x hg hf]
  exact LinearMap.ker_le_ker_comp _ _

theorem ker_fderiv_postcomp_eq_of_injOn_range {f : E → F} {g : F → H} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x))
    (hinj : Set.InjOn (fderiv ℝ g (f x)) (Set.range (fderiv ℝ f x))) :
    (fderiv ℝ (g ∘ f) x).ker = (fderiv ℝ f x).ker := by
  apply le_antisymm _ (ker_fderiv_le_ker_postcomp hf hg)
  intro v hv
  rw [fderiv_comp x hg hf] at hv
  change fderiv ℝ g (f x) (fderiv ℝ f x v) = 0 at hv
  change fderiv ℝ f x v = 0
  apply hinj ⟨v, rfl⟩ ⟨0, map_zero _⟩
  simpa only [map_zero] using hv

end DifferentialGeometry.Analysis

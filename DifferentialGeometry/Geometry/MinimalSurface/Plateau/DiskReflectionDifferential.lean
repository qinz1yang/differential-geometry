import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential



noncomputable section

open Bundle Manifold DifferentialGeometry Function
open scoped Bundle Manifold ContDiff Topology ComplexConjugate

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

set_option backward.isDefEq.respectTransparency false in



theorem mfderiv_comp_planeLinearEquiv (U : ℂ → M) (L : ℂ ≃L[ℝ] ℂ) (z : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (U ∘ L) z =
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (L z)).comp L.toContinuousLinearMap := by
  have hL : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) L z :=
    L.differentiableAt.mdifferentiableAt
  by_cases hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (L z)
  · rw [mfderiv_comp z hU hL, mfderiv_eq_fderiv, L.hasFDerivAt.fderiv]
  · have hc : ¬ MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (U ∘ L) z := by
      intro h
      have hi : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) L.symm (L z) :=
        L.symm.differentiableAt.mdifferentiableAt
      have h' : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (U ∘ L) (L.symm (L z)) :=
        (L.symm_apply_apply z).symm ▸ h
      have heq : ((U ∘ L) ∘ L.symm) = U := by
        funext w
        simp only [Function.comp_apply, L.apply_symm_apply]
      exact hU (heq ▸ h'.comp (L z) hi)
    rw [mfderiv_zero_of_not_mdifferentiableAt hc, mfderiv_zero_of_not_mdifferentiableAt hU]
    rfl



theorem diskMapPartial_comp_conj (U : ℂ → M) (z v : ℂ) :
    diskMapPartial (E := E) (U ∘ conj) z v = diskMapPartial (E := E) U (conj z) (conj v) :=
  congrArg (fun L : ℂ →L[ℝ] E => L v)
    (mfderiv_comp_planeLinearEquiv (E := E) U Complex.conjCLE z)


theorem diskMapPartial_comp_conj_one (U : ℂ → M) (z : ℂ) :
    diskMapPartial (E := E) (U ∘ conj) z 1 = diskMapPartial (E := E) U (conj z) 1 := by
  rw [diskMapPartial_comp_conj, map_one]


theorem diskMapPartial_comp_conj_I (U : ℂ → M) (z : ℂ) :
    diskMapPartial (E := E) (U ∘ conj) z Complex.I = -diskMapPartial (E := E) U (conj z) Complex.I := by
  rw [diskMapPartial_comp_conj, Complex.conj_I]
  exact map_neg (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (conj z)) Complex.I

end DifferentialGeometry.Geometry
